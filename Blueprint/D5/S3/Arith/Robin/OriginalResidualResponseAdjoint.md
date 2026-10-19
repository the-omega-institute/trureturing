# Adjoint of the Original Response

## Abstract

The adjoint of the exact original Mobius floor response retains the original weighted Gram and gives exact moments, an all-real coefficient pairing identity and both coordinate signs and actual strict intervals of each scalar residual sign.

All logarithms are natural. Let S(N)={m in N:N<=m<2N}. The unchanged finite-transfer coefficient is kappa(N,d)=mu(d)*log(N/d)/log(N), where mu is the actual ArithmeticFunction.moebius, and the original response is R(N,m)=1+C(N)*m-sum_(1<=d<=N) kappa(N,d)*floor(m/d), with C(N)=sum_(1<=d<=N) kappa(N,d)/d. Floors mean natural division followed by a real cast. Every original Mobius row, the constant and linear term remain.

Use the same original w(m)=1/[m(m+1)], v(N,m)=(1,m/N), and full G(N)[i,j]=sum_(m in S(N)) w(m)*v(N,m)[i]*v(N,m)[j]. For N>=3 its original determinant Delta(N) is positive. For arbitrary real a,b, omega(a,b,m) is the original literal density integral over [a,b] intersect [m,m+1]. The original coefficient A(N,a,b,m) is w(m) times the affine residual of the datum log(N)*omega(a,b,m)/w(m) on S(N), extended by zero outside S(N). Its original separate terminal values at 2N are retained, and its Cramer coordinates are unrestricted in sign.

**Definition 1.1 (Right side for the response itself).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointRhs`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointRhs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N and i in Fin 2, H(N)[i]=sum_(m in S(N)) w(m)*R(N,m)*v(N,m)[i]. This projects the original response R, rather than the partial-cell datum log(N)*omega/w.

**Definition 1.2 (The same full Gram inverse).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointCoordinates`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N, q(N)=G(N)^(-1)*H(N), using exactly the original G. The definition uses Lean's total matrix inverse; nonsingularity is used only under N>=3 in the proved statements. No alternate projection is introduced.

**Definition 1.3 (Residual of the original response).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointResidual`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N,m, E(N,m)=R(N,m)-q(N)[0]-q(N)[1]*(m/N). Only its original block S(N) is used in the results below. E is distinct from the original partial-cell datum residual and from the scalar finite-transfer residual. Its definition does not impose a new zero terminal value at 2N.

**Theorem 1.4 (Pairing identity for every real endpoint pair).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjoint_actual_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjoint_actual_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3 and every real a,b, OriginalResidualFiniteTransfer.residual(N,A(N,a,b)) = log(N)*sum_(m in S(N)) omega(a,b,m)*E(N,m). The finite-transfer residual on the left is the literal scalar sum sum A(N,a,b,m)*R(N,m). There are no endpoint order, strictness, upper-bound, nonzero-cell or interval-sign hypotheses in this theorem.

The original coefficient moments sum A=0 and sum m*A=0 remove q0+q1*m/N from the response pairing. The two weighted moments of E remove the original datum's affine correction from A. What remains is precisely log(N) times the same literal partial-cell pairing with E.

**Theorem 1.5 (Two exact moments, the actual identity and both coordinate signs).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.or6_response_adjoint_identity_and_signs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.or6_response_adjoint_identity_and_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3, all eight conclusions hold together: sum_(m in S(N)) w(m)*E(N,m)=0; sum_(m in S(N)) [w(m)*m/N]*E(N,m)=0; the preceding actual scalar identity for every real a,b; some m in S(N) has E(N,m) different from zero; some m in S(N) has E(N,m)>0; and some m in S(N) has E(N,m)<0. The existential witnesses may differ. In addition, there is a legal strict interval N<a<b<2N with positive original scalar residual and another with negative original scalar residual.

The normal equations use the original Gram entries and positive determinant. The nonaffinity theorem for the exact original response prevents E from vanishing throughout S(N). Positivity of w on that block and the zero weighted moment then force both signs. This consumes the original nonaffinity proof; no mathematical novelty is claimed.

The strict intervals use a=m+1/3,b=m+2/3 inside a signed original row cell. The actual omega mass is g(a)-g(b)>0 and vanishes in all other cells, so the original scalar equals log(N)*(g(a)-g(b))*E(N,m). This does not supply a signed endpoint lower bound, a prescribed Robin endpoint pair or a cofinal sequence of favorable pairs. The cutoff, both zero-extension jumps, prefix payments, infinite compensation and analytic suppliers remain unchanged. There is no strict Robin conclusion above 5040 and no RH conclusion. The whole eight-clause registration remains unresolved under source.selection_missing; the separate all-real identity registration is validated by the current report.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.or6_response_adjoint_identity_and_signs`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointCoordinates`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointResidual`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjointRhs`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseAdjoint.responseAdjoint_actual_identity`
- Dependency: [D5/S3/Arith/Robin/OriginalResidualFiniteTransfer](OriginalResidualFiniteTransfer.md)
- Dependency: [D5/S3/Arith/Robin/OriginalResidualPartialCellWeights](OriginalResidualPartialCellWeights.md)
- Dependency: [D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate](OriginalResidualResponseNonaffinityCandidate.md)
