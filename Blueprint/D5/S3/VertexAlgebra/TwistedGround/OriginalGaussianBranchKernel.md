# Original regularized branch and neck jets

## Abstract

Original regularized branch and neck jets

For square-root coordinates, the original base-coordinate two-current scalar is K0(s,t)=(s^2+t^2)/(2 s t (s^2-t^2)^2). When s,t are nonzero and s^2-t^2 is nonzero, subtracting 1/(s^2-t^2)^2 gives the regular part 1/(2 s t (s+t)^2), the same elementary expression as the pair kernel. These rational coordinate calculations are transient exact checks, not extra library theorems.

With a=t-1 and b=u^(-1)-1, for nonzero p,q and nonzero 1-p^2 q^2, the cross pullback multiplies K0(p,q^(-1)) by p q and the actual inverse-coordinate Jacobian -q^(-4), giving -(1+p^2 q^2)/(2(1-p^2 q^2)^2). The formal cross series is independently obtained by rescaling the native inverse-square branch factor at t u. Its coefficient is -(n+1/2) on every diagonal n>=0 and zero off the diagonal. The p q regularization removes precisely the two half powers.

For nonzero s,p with s^2-p^2 nonzero, the input pullback p K0(s,p) is s^(-3) times the rational factor at p^2 s^(-2). For nonzero s,p with 1-s^2 p^2 nonzero, the detector pullback includes -p^(-4) and is -s^(-1) times that factor at s^2 p^2. Using the constant-one formal neck root s=sqrt(1+a), the formal mixed jets are r_n(1+a)^(-r_n-1) and -r_n(1+a)^(r_n-1), where r_n=n+1/2. They are exactly the negative formal derivatives of the ordinary primitives (1+a)^(-r_n) and (1+a)^(r_n), for every n>=0.

The supplier sources were collected and hash-pinned on 2026-11-02; the candidate retains the original pairScalar and halfBinomial APIs. Formal regularized half powers are the exact scope. Analytic convergence on a sewn curve and binding to raw T, U, coloured G, the infinite M and the full original K remain separate unproved steps. No full Jacobi, no-ghost, string or AdS/CFT result is claimed.

Audit limitation under CLAUDE 3.9: the faithful Reg mirrors for D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel.crossExpansion_coeff and D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel.branch_coeff_eq_negative_source_derivative compile. For each, the current scoped report records declared_unresolved, certificate=null, IE-C050 ClosedTruthReadout, reason=unclassified_form, rule=source.residual_requires_open, with escape_continues.kind=open. The unfinished template assessments are disclosed against the existing issue https://github.com/the-omega-institute/trureturing/issues/5214. No declared_validated audit, admission or freeze is claimed; the judge is unchanged.

**Definition 1.1 (crossExpansion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.crossExpansion`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.crossExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Formal inverse-square branch factor rescaled at the product of the branch variables.

**Theorem 1.2 (crossExpansion_coeff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.crossExpansion_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.crossExpansion_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All regularized cross coefficients, with the negative detector sign.

**Definition 1.3 (inputBranch).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.inputBranch`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.inputBranch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The regularized ordinary input jet.

**Definition 1.4 (detectorBranch).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.detectorBranch`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.detectorBranch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The regularized detector jet with its inverse Jacobian sign.

**Theorem 1.5 (branch_coeff_eq_negative_source_derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.branch_coeff_eq_negative_source_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.branch_coeff_eq_negative_source_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both all-mode neck jets equal negative derivatives of the ordinary source primitives.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.branch_coeff_eq_negative_source_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.crossExpansion`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.crossExpansion_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.detectorBranch`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel.inputBranch`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPairKernel](OriginalGaussianPairKernel.md)
