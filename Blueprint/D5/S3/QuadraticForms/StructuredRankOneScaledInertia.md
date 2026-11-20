# Coefficient-dependent inertia of the structured downdate

## Abstract

The inertia of A − t w wᵀ/Δ is In(A) − In([Δ]) + In([(1 − t)Δ]) for every real t.

**Definition 1.1 (The scaled downdate).**

Lean statement: `D5/S3/QuadraticForms/StructuredRankOneScaledInertia.scaledDowndate`

*Formalization.* `D5/S3/QuadraticForms/StructuredRankOneScaledInertia.scaledDowndate` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

M_t = A − t w wᵀ/Δ with w = A x and Δ = xᵀ A x.

**Theorem 1.2 (Inertia of the scaled downdate).**

Lean statement: `D5/S3/QuadraticForms/StructuredRankOneScaledInertia.result`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneScaledInertia.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

Let A be real symmetric and x a vector with Δ = xᵀ A x ≠ 0, and put w = A x. For every real t the matrix M_t = A − t w wᵀ/Δ is symmetric, and with [P] equal to 1 when P holds and 0 otherwise: n₊(M_t) + [Δ > 0] = n₊(A) + [(1 − t)Δ > 0], n₋(M_t) + [Δ < 0] = n₋(A) + [(1 − t)Δ < 0], and n₀(M_t) = n₀(A) + [t = 1]. Hence the inertia of M_t equals that of A exactly when t < 1, the nullity is unchanged exactly when t ≠ 1, M_1 is the structured downdate, and for t > 1 one eigenvalue moves from the sign of Δ to the opposite sign.

For t = 0 nothing changes. For t ≠ 0 put d = Δ/t and c = d − Δ. The block matrix A ⊕ [c] is congruent, by the unipotent matrix with x in its corner column, to the bordered matrix with off-diagonal block w and corner Δ + c = d. Eliminating w with the pivot d makes that bordered matrix congruent to (A − w wᵀ/d) ⊕ [d], and A − w wᵀ/d = M_t. Sylvester's law of inertia and additivity over blocks give n₊(A) + [c > 0] = n₊(M_t) + [d > 0] and the same for n₋. Since c = (1 − t)Δ/t, the sign cases t > 0 and t < 0 both give the stated identities, and the nullity follows because the three counts add to n. The congruences adapt the block-congruence mechanism proposed by Lucid in MathOverflow 513954, revision 2 (CC BY-SA 4.0), to arbitrary corners. This is Corollary 4 of H. Ma and W. Zhang (DOI 10.5281/zenodo.23920598) on MathOverflow 513954, revision 2, asked by Lucid.

## References

- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneScaledInertia.result`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneScaledInertia.scaledDowndate`
- Dependency: [D5/S3/QuadraticForms/StructuredRankOneInertia](StructuredRankOneInertia.md)
