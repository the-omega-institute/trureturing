# Ordinary Coefficient Parity of the Diagonal-Constraint Series

## Abstract

The normalized diagonal-constraint series has odd ordinary coefficients exactly at powers of two.

OEIS A177775 is the ordinary coefficient sequence of DiagonalIterateEven.generatingSeries G. The initial values are G(0)=0 and coeff(1,G)=coeff(2,G)=1; they are specified by the original recursive program and by the revised seed [0,1,1]. The NAME's adjacent-iterate condition holds for every n>2. The construction and uniqueness in DiagonalIterateEven identify this normalized source without assuming existence or integrality. Its ordinary coefficients are coeff(n,G); DiagonalIterateEven.a(n) denotes the different diagonal sequence A395842. The second OEIS offset component 3 adds no initial condition. The A177775 conclusion includes every n≥1, both implications, and n=1=2^0. The PARI programs themselves are not formalized.

**Theorem 1.1 (The full A177775 ordinary-coefficient parity characterization).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{coeff}\left(n, \operatorname{generatingSeries}\left(\right)\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a177775-ordinary-coefficient-parity` (proved) by `D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a177775-ordinary-coefficient-parity","declaration_gid":"D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A177775, parity of the normalized diagonal-constraint series*. URL: <https://raw.githubusercontent.com/oeis/oeisdata/501c6189fe17530d95e5a4f90dbca228feb5713d/seq/A177/A177775.seq>.

*Commentary.*

Let P be CubicFifteenSubstitutionParity.powerTwoSeries over ZMod(2). Its coefficient at n is the indicator of existence of a natural k with n=2^k. The first component of thue_series_equation and characteristic two give P+P²=X. The existing H satisfies H+H²=X, and both constant coefficients are zero. CubicFifteenSubstitutionParity.quadratic_unique therefore gives H=P. The existing mod_two_identity identifies the coefficientwise reduction of G with H. Applying coeff(n) and ZMod.intCast_eq_one_iff_odd proves the displayed equivalence in both directions for every positive n. The zeroth exponent k=0 supplies n=1. This uses ordinary integer coefficients of G and imposes no parity assumption on its construction.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.result`
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](../Invariants/CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Parity/DiagonalIterateEven](DiagonalIterateEven.md)
