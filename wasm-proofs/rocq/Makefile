.PHONY: all check clean

MODULES := Handle Identify Slice Digest ApplyTree Evaluation EvaluationProperties Congruence Equivalence EquivalenceClosure Coupon CouponApi CouponConstructors Host Init ModuleValidation ModuleLayout ExecutionUtil SelfCoupon EvalBlobCoupon CouponTable SymCoupon TransCoupon MappedEqCoupon ThinkToForceCoupon ForceToEncodeStrictCoupon EvalEqCoupon ThinkApplicationCoupon ForceResultEqCoupon WasmNatural Dispatcher TreeLayout LoopUtil TreeCoupon MakeCoupon

all: Init.v CoqMakefile
	$(MAKE) -f CoqMakefile all

Init.v: ../../coupon.wat ../../scripts/generate-rocq-init.py
	python3 ../../scripts/generate-rocq-init.py

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o $@

check: all
	python3 ../../scripts/generate-rocq-init.py --check
	coqchk -silent -Q . FixProof $(addprefix FixProof.,$(MODULES))

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
