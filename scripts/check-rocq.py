#!/usr/bin/env python3
"""Cache standalone kernel validation of exact Rocq library contents."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile


NAME = r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*"


def digest(path):
    with Path(path).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def project_config(path):
    tokens = shlex.split(path.read_text(), comments=True)
    flags, mappings, files = [], [], []
    while tokens:
        token = tokens.pop(0)
        if token in ('-Q', '-R'):
            physical, logical = tokens[:2]
            del tokens[:2]
            flags.extend([token, physical, logical])
            mappings.append((Path(physical).resolve(), logical))
        elif token.endswith('.v'):
            files.append(Path(token).resolve())
        else:
            raise ValueError(f'Unsupported _CoqProject entry: {token}')
    modules = []
    for source in files:
        matches = [(directory, name) for directory, name in mappings
                   if source.is_relative_to(directory)]
        directory, name = max(matches, key=lambda match: len(match[0].parts))
        suffix = '.'.join(source.relative_to(directory).with_suffix('').parts)
        modules.append(f'{name}.{suffix}')
    if not modules:
        raise ValueError('No proof modules in _CoqProject')
    return flags, modules


def repl(rocq, flags, text):
    with tempfile.TemporaryDirectory(prefix='fix-proof-check-') as directory:
        source = Path(directory) / 'Inventory.v'
        source.write_text(text)
        return subprocess.check_output(
            [rocq, 'repl', '-quiet', '-batch', '-q', *flags, '-l', str(source)],
            text=True)


def inventory(rocq, flags, modules):
    require = 'Require ' + ' '.join(modules) + '.\n'
    output = repl(rocq, flags, require + 'Print Libraries.\n')
    names = re.findall(r'^  (' + NAME + r')\s*$', output, re.MULTILINE)
    if not set(modules).issubset(names):
        raise ValueError('Could not inventory every project library')
    output = repl(rocq, flags, require + ''.join(
        f'Locate Library {name}.\n' for name in names))
    locations = dict(re.findall(
        r'^(' + NAME + r') has been loaded from file\n([^\n]+)',
        output, re.MULTILINE))
    if set(locations) != set(names):
        raise ValueError('Could not locate the complete library closure')
    return {name: str(Path(path.strip().strip('"')).resolve())
            for name, path in locations.items()}


def tool_identity(rocq):
    # Include checker/runtime bytes, not just the advertised version.
    binaries = [Path(rocq).resolve()]
    for name in ('rocqchk', 'rocqworker'):
        binary = Path(rocq).parent / name
        if binary.exists():
            binaries.append(binary.resolve())
    return {
        'version': subprocess.check_output([rocq, '--version'], text=True),
        'binaries': {str(path): digest(path) for path in set(binaries)},
        'driver': digest(__file__),
    }


def fingerprint(identity, flags, libraries):
    data = {'tool': identity, 'flags': flags, 'libraries': {
        name: {'path': path, 'sha256': digest(path)}
        for name, path in sorted(libraries.items())}}
    return hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()


def cached(path, key):
    try:
        return json.loads(path.read_text()) == {'sha256': key}
    except (OSError, ValueError):
        return False


def save(path, key):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as out:
        json.dump({'sha256': key}, out)
        temporary = out.name
    os.replace(temporary, path)


def validate(rocq, flags, roots, jobs):
    # One -norec root per process avoids Rocq 9.1's ordering bug with multiple
    # such roots. Every member of the loaded closure is checked in one of the
    # two stages; neither stage is cached until every assigned root passes.
    def check(root):
        subprocess.run([rocq, 'check', '-silent', *flags, '-norec', root], check=True)
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(check, roots))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--force', action='store_true')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    rocq = shutil.which('rocq')
    if not rocq:
        parser.error('rocq is not on PATH')
    flags, modules = project_config(Path('_CoqProject'))
    libraries = inventory(rocq, flags, modules)
    dependencies = {name: path for name, path in libraries.items() if name not in modules}
    identity = tool_identity(rocq)
    cache = Path('.rocq-check-cache')
    dependency_key = fingerprint(identity, flags, dependencies)
    project_key = fingerprint(identity, flags, libraries)

    def stage(label, path, key, roots, inputs):
        if not args.force and cached(path, key):
            print(f'{label}: cache hit ({len(roots)} libraries)', flush=True)
            return
        print(f'{label}: checking {len(roots)} libraries with {args.jobs} worker(s)', flush=True)
        validate(rocq, flags, roots, args.jobs)
        if fingerprint(tool_identity(rocq), flags, inputs) != key:
            raise ValueError('Check inputs changed during validation; no cache saved')
        save(path, key)

    stage('Dependencies', cache / 'dependencies.json', dependency_key,
          sorted(dependencies), dependencies)
    stage('Project', cache / 'project.json', project_key,
          modules, libraries)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
