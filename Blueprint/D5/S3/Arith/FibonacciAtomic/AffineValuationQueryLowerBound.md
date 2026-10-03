# The affine valuation identification lower bound

## Abstract

Exact adaptive identification by affine prime-power valuation queries requires at least d e (p-1) observations on one fixed input.

**Remark 1.1 (An essential singleton in a coset cover).**

$$
m \ge d e (p-1)
$$

*Citation.* Günter Lettl; Zhi-Wei Sun (2008). *On covers of abelian groups by cosets*. DOI: [10.48550/arXiv.math/0411144](https://doi.org/10.48550/arXiv.math/0411144). URL: <https://arxiv.org/abs/math/0411144>.

*Commentary.*

Lettl and Sun's Theorem 1.3 implies this static inequality when m cosets cover the complement of one point in (Z/p^e Z)^d and all avoid that point. Adding the singleton gives an ordinary cover in which that singleton is essential. Here p is prime and e is positive.

**Theorem 1.2 (One actual complete-response history attains the lower bound).**

$$\forall p \in \mathbb{N}, \forall e \in \mathbb{N}, \forall d \in \mathbb{N}, (\operatorname{Prime}\left(p\right) \land 1 \le e \land 1 \le d) \implies ((\forall T \in P, (\operatorname{Injective}\left(\operatorname{Run}\left(T\right)\right)) \implies (\exists x \in X, d e (p-1) \le \lvert\operatorname{Run}\left(T, x\right)\rvert)) \land (\forall A \in Hist \to Q + X, \forall t \in X \to Hist, \forall b \in X \to \mathbb{N}, (\forall x \in X, \operatorname{Exec}\left(A, \operatorname{b}\left(x\right), \operatorname{nil}\left(\right), x\right) = \operatorname{some}\left((\operatorname{t}\left(x\right),x)\right)) \implies (\exists x \in X, d e (p-1) \le \lvert\operatorname{t}\left(x\right)\rvert)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/AffineValuationQueryLowerBound.affine_valuation_query_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Günter Lettl; Zhi-Wei Sun (2008). *On covers of abelian groups by cosets*. DOI: [10.48550/arXiv.math/0411144](https://doi.org/10.48550/arXiv.math/0411144). URL: <https://arxiv.org/abs/math/0411144>.

*Commentary.*

X is the d-fold product of ZMod(p^e), Q is X times ZMod(p^e), and a query (a,c) returns the greatest r at most e for which p^r divides the representative of the affine value a dot x+c. The zero value has response e. Every row is allowed, including zero and nonprimitive rows. Hist is the finite-list space of query-response pairs and P is the deterministic dependent-tree space PassiveProtocol(Q,N). Run records all complete responses.

The second conjunct includes arbitrary history selectors A:Hist to Q+X. Exec uses the stated fuel b(x), starts at the empty history, and returns the additional history t(x) together with x. Fuel only specifies terminating execution; it is not an observation. No common fuel bound is assumed. Every recorded query costs one, including saturated and uninformative queries.

At a query choose the least response attained by the current nonempty candidate set. The exact response fiber remains nonempty. At an identifying leaf it is one point x. Every different point has a greater response at some query of that same history. Thus the nonsaturated queries supply possibly empty congruence fibers. Their nonempty fibers are cosets; together they cover the complement of x and avoid x.

A character product has nonzero support precisely at x. Averaging its integral group-algebra expansion shows that its value at x is divisible by p^(de) in the cyclotomic integers. The absolute norm of each factor is p^(p^(e-1)), while the field degree is p^(e-1)(p-1). Norm divisibility gives the static inequality, including p=2 and e=1. Deterministic execution on the fixed point x realizes the whole chosen history.

Finite-query normalization preserves terminal fibers and never increases actual query counts. Applied to the history selector, it transfers the dependent-tree lower bound to its original terminating traces.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AffineValuationQueryLowerBound.affine_valuation_query_lower_bound`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](../../ConceptDynamics/Experiment/PassivePolicyNormalization.md)
- Dependency: [D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution](../../Observer/Budget/PrimePowerNonadaptiveResolution.md)
- Dependency: [D5/S3/Observer/Budget/ResidueHeightUpperBound](../../Observer/Budget/ResidueHeightUpperBound.md)
