# Both spectral properties of the map Psi

## Abstract

The map Psi gives both indexed spectral properties in every dimension.

**Definition 1.1 (The two-property proposition).**

Lean statement: `D5/S3/Quantum/Matrix/LinPsiMap/Result.conjecture`

*Formalization.* `D5/S3/Quantum/Matrix/LinPsiMap/Result.conjecture` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *New properties for certain positive semidefinite matrices*. DOI: [10.48550/arXiv.1609.08231](https://doi.org/10.48550/arXiv.1609.08231). URL: <https://arxiv.org/abs/1609.08231v1>.

*Commentary.*

The proposition quantifies over every natural dimension n, all complex n by n matrices A, X and B, positivity of [A X; X-adjoint B], and every index j in Fin n. It is the conjunction of 2 s_j(Psi(X)) <= lambda_j(Psi(A)+Psi(B)) and s_j(Psi(X)) <= lambda_j(Psi(A) geometric-mean Psi(B)), where Psi(T)=2 trace(T) I−T. Both spectral lists decrease, using the same singular-value, eigenvalue and geometric-mean definitions as the trace-augmentation comparison.

**Theorem 1.2 (The a-property and g-property).**

Lean statement: `D5/S3/Quantum/Matrix/LinPsiMap/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinPsiMap/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/lin-2016-psi-map-properties` (proved) by `D5/S3/Quantum/Matrix/LinPsiMap/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lin-2016-psi-map-properties","declaration_gid":"D5/S3/Quantum/Matrix/LinPsiMap/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *New properties for certain positive semidefinite matrices*. DOI: [10.48550/arXiv.1609.08231](https://doi.org/10.48550/arXiv.1609.08231). URL: <https://arxiv.org/abs/1609.08231v1>.

*Commentary.*

Both inequalities hold for every positive semidefinite complex block matrix. No commutation, invertibility or rank hypothesis is imposed on the original blocks. Dimension zero is vacuous; if either diagonal block is zero, positivity forces the cross block to vanish and the total geometric mean handles the degenerate case.

For positive diagonal traces, a block congruence normalizes them separately. Reduction-block positivity and the Gram-discrepancy estimate provide the arithmetic deficit. The existing difference-square and geometric-mean lower bounds give the normalized geometric comparison. Independent positive homogeneity of the geometric mean restores the g-property for the original blocks, and the matrix arithmetic-geometric mean comparison gives the a-property.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinPsiMap/Result.conjecture`
- Truth anchor: `D5/S3/Quantum/Matrix/LinPsiMap/Result.result`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/Result](../LinGProperty/Result.md)
- Dependency: [D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy](GramDiscrepancy.md)
- Dependency: [D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock](ReductionBlock.md)
