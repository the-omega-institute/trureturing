# The weighted original tail residuals

## Abstract

Weighted residual budgets for the original primal theta tail.

**Definition 1.1 (The first literal residual).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.tailResidual`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.tailResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural cutoff N and real A, alpha, x, R(x)=4*A^2*originalTail(N,x) minus densityAdjoint(alpha,originalTail(N),x). The adjoint is L_alpha(f)=f''+alpha*(f+x*f').

**Definition 1.2 (The second literal residual).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.tailSecondResidual`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.tailSecondResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For N,A,alpha,x as above, R2(x)=4*A^2*R(x)-L_alpha(R)(x). Alpha is fixed for spatial differentiation. When alpha=t/(2*n), R itself depends on t.

**Lemma 1.3 (The weighted first residual budget).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.first_residual_64`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.first_residual_64` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N>=1, A=pi*(N+1)^2>=max(64,a) and 0<=alpha<=a, exp(a*x^2/2)*|R(x)| is integrable over x>0 and its integral is at most 64*originalFlux(N)/A. The full shifted sum is bounded by 256*A^2*exp(-A), and the full cubic flux is at least (11/2)*A^3*exp(-A). This estimate supplies the I response in the complete tail derivative vector.

**Lemma 1.4 (The second residual with its external square weight).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.second_residual_1100`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.second_residual_1100` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N>=1, A=pi*(N+1)^2>=max(64,a) and 0<=alpha<=a, x^2*exp(a*x^2/2)*|R2(x)| is integrable over x>0 and its integral is at most 1100*originalFlux(N)/A. The first omitted mode retains its quartic-jet cancellation before integration and contributes at most 5100*A^2*exp(-A). Each later mode of scale s contributes at most 600*s^3*exp(-s); the complete sum is at most 6000*A^2*exp(-A). This bound supplies both second-residual pairings in the D and M2 responses of the complete vector. These residual estimates assert no sign for the full-source head product or either head-tail cross term.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.first_residual_64`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.second_residual_1100`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.tailResidual`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.tailSecondResidual`
- Dependency: [D5/S3/Zeros/Jensen/OriginalPrimalTailProjection](OriginalPrimalTailProjection.md)
- Dependency: [D5/S3/Zeros/Jensen/OriginalPrimalTailResponse](OriginalPrimalTailResponse.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenPositiveExtension](SourceJensenPositiveExtension.md)
