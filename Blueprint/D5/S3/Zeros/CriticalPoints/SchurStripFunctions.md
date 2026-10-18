# The Schur interpolation functions

## Abstract

Entire matrix interpolation functions with the left boundary estimate and a unitary right multiplier.

**Definition 1.1 (The scalar trace family).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.f`

*Formalization.* `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given n, a complex matrix Q, complex families u,v, real families t,rho and real p, define F(z)=H(n,pz/2) diag(u_j positivePower(t_j,pz)) H(n,pz/2), K(z)=Q diag(conj(v_k) positivePower(rho_k,p(1−z))) Q*, and f(z)=Tr(K(z)F(z)). Each entry is built from explicit scalar exponentials and finite matrix products.

**Theorem 1.2 (Analyticity and boundedness on the closed strip).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.f_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.f_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all supplied finite data, the scalar trace family f has StripData: it is entire and bounded on the closed strip. No positivity, phase normalization, unitary basis or triangularity assumption is needed for this analytic statement.

**Theorem 1.3 (The normalized left boundary).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.left_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.left_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>0, unitary Q, unit phases u and v, positive rho and sum_k rho_k^p=1, the norm of f(iy) is at most one for every real y. The left F matrix is unitary; in the Q basis the absolute diagonal weights sum to one. On the right boundary, K is unitary whenever Q and v have these unitary and phase properties.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.f`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.f_strip`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurStripFunctions.left_bound`
- Dependency: [D5/S3/Zeros/CriticalPoints/RankOneComplexPowers](RankOneComplexPowers.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment](ThreeLinesSchurMoment.md)
