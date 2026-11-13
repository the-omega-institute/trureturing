# Projected unitary polynomial lifting

## Abstract

Polynomial identities for scalar reflection words lift to arbitrary projected unitaries.

Let H be any finite-dimensional complex inner product space, including dimension zero. An encoding E consists only of a unitary U and two arbitrary orthogonal projections Pi and Pt on H. They need not have equal rank. Set A=Pt U Pi and G=A* A, where star means adjoint. The internal positive-idempotent predicate for projections is equivalent to self-adjoint idempotence; ofRaw constructs E directly from these equations. All products act from the right.

Write e(theta)=exp(i theta), F(J,theta)=e(theta)J+e(-theta)(1-J), and V(E,[])=1. For theta::Theta, V is F(Pt,theta) U V(E,Theta) when the tail length is even and F(Pi,theta) U* V(E,Theta) otherwise. Put s(x)=sqrt(1-x squared), D(theta)=diag(e(theta),e(-theta)), R(x)=[[x,s(x)],[s(x),-x]], and S(Psi,x)=the list-ordered product of D(theta)R(x), with empty product 1. These are phaseOp, altSeq, Rref, phaseZ and seqR in Lean.

**Theorem 1.1 (Action on an arbitrary singular pair).**

$$\forall (H: \operatorname{FiniteComplexHilbertSpace}()), \forall (E: \operatorname{Encoding}(H)), \forall (v: H), \forall (sigma: \mathbb{R}), \forall (Psi: \operatorname{List}(\mathbb{R})), (\operatorname{Pair}(E, v, sigma)) \Rightarrow \operatorname{apply}(\operatorname{V}(E, Psi), v) = \operatorname{entry}(\operatorname{S}(Psi, sigma), 0, 0)b+\operatorname{entry}(\operatorname{S}(Psi, sigma), 1, 0)c$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/ProjectedUnitaryLifting.altSeq_apply_singular` (`✓ std3`). ∎

*Citation.* Andras Gilyen, Yuan Su, Guang Hao Low, Nathan Wiebe (2019). *Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics*. DOI: [10.1145/3313276.3316366](https://doi.org/10.1145/3313276.3316366). URL: <https://arxiv.org/abs/1806.01838v1>.

*Commentary.*

Here Pair(E,v,sigma) means exactly Pi v=v, 0<=sigma<=1 and A* A v=sigma squared v. No normalization is required, and v=0 is allowed. Set l=0 when sigma=0 and l=A v/sigma otherwise; set lt=(1-Pt)U v/s(sigma) and rp=(1-Pi)U* l/s(sigma), using the complex inverse with inverse(0)=0. If the list length is even, b=v and c=rp; otherwise b=l and c=lt. The formula gives the entire vector, including its component outside the projected output.

The defining equations imply Uv=sigma l+s lt, U* l=sigma v+s rp, U rp=s l-sigma lt and U* lt=s v-sigma rp. For sigma<1 these follow by cancellation of s and unitarity. At sigma=1, equality of the projected and full norms forces the complementary vector to vanish by Pythagoras. At sigma=0, l=rp=0 and lt=Uv. Projector phases multiply the range vector by e(theta) and the complementary vector by e(-theta). Induction on the phase list now follows the two entries of the scalar reflection recurrence.

**Theorem 1.2 (The scalar 00 identity determines the compressed operator).**

$$\forall (H: \operatorname{FiniteComplexHilbertSpace}()), \forall (E: \operatorname{Encoding}(H)), \forall (Psi: \operatorname{List}(\mathbb{R})), \forall (R: \mathbb{C}[X]), (\forall (x: I), \operatorname{entry}(\operatorname{S}(Psi, x), 0, 0) = \operatorname{cases}(\operatorname{Even}(\operatorname{length}(Psi)), \operatorname{eval}(R, (x)^{2}), x\operatorname{eval}(R, (x)^{2}))) \Rightarrow ((\operatorname{Even}(\operatorname{length}(Psi))) \Rightarrow Pi\operatorname{V}(E, Psi)Pi = Pi\operatorname{eval}(R, G)Pi) \land ((\operatorname{Odd}(\operatorname{length}(Psi))) \Rightarrow Pt\operatorname{V}(E, Psi)Pi = A\operatorname{eval}(R, G))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/ProjectedUnitaryLifting.polynomial_lifting` (`✓ std3`). ∎

*Citation.* Andras Gilyen, Yuan Su, Guang Hao Low, Nathan Wiebe (2019). *Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics*. DOI: [10.1145/3313276.3316366](https://doi.org/10.1145/3313276.3316366). URL: <https://arxiv.org/abs/1806.01838v1>.

*Commentary.*

In the formula I=[0,1]. The scalar premise is required for every real x in [0,1], for an arbitrary complex polynomial R. Evaluation R(G) is Polynomial.aeval. The Gram operator restricts to the input range; its symmetric spectral theorem supplies a complete orthonormal basis there, with eigenvalues sigma squared in [0,1]. The singular-pair action on each basis vector and polynomial evaluation at its eigenvalue give the two equalities. Both sides vanish on the input complement; in the odd case this uses commutation of Pi with G and every polynomial in G.

The input basis includes every zero eigenvalue, even when the output projection has smaller rank. Consequently the even action on an input vector in ker(A) is R(0) times that vector. The empty list is included and gives the input projection for R=1. No full-rank assumption, rank equality, nonzero singular-value assumption or Hermitian restriction on A occurs. The scalar premise can constrain only values on the singular spectrum, but the theorem assumes the stated identity on the whole interval.

These are compressed operator identities. They do not identify a projected block with a deterministic output channel, synthesize a real-part ancilla circuit, prove exact query accounting, or establish a physical adjoint by negating phases. The phase gate itself need not have determinant one.

The structural proofs are reused from shosonoda, auto-res/lean-qsvt, immutable revision 42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/SVT/SVD.lean, TwoFrame.lean and SingularPair.lean, with the required original Operator/Basic.lean, Encoding/Projected.lean, QSP/Conventions.lean, SVT/PhaseOp.lean, AltSeq.lean, EigenBasis.lean, SVTransform.lean and TwoVector.lean declarations. The mathematical source is Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Definitions 15–16 and Theorem 17, printed pages 17–19. Copyright (c) 2026 shosonoda and copied Copyright (c) 2025 Hayata Yamasaki are retained under Apache-2.0; the full license is docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. This application makes no mathematical novelty claim.

## References

- Truth anchor: `D5/S3/ContinuousObservables/ProjectedUnitaryLifting.altSeq_apply_singular`
- Truth anchor: `D5/S3/ContinuousObservables/ProjectedUnitaryLifting.polynomial_lifting`
