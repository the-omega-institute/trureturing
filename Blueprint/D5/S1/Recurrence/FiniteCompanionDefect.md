# Finite companion defect

## Abstract

Constructive elimination of a finite additive reset companion.

Let A be any additive commutative group, J an additive endomorphism, and n a natural number. The carrier is Fin(n+1) -> A, so length one is included. No involution, field, torsion-free or finite-generation hypothesis is imposed. The domain coordinates D(v) are (v(0), t), where t(j)=v(j+1)+v(j). Their inverse is the integral recurrence v(0)=a and v(j+1)=t(j)-v(j). Put R(t)=sum over j in Fin n with Odd(n-j) of t(j). The independent codomain coordinates C(y) are (y(0)-J(R(tail(y))), tail(y)). Their inverse adds J(R(t)) back to the head. Both changes are additive equivalences.

**Theorem 1.1 (Separate domain and codomain elimination).**

$$\forall A \in AddCommGroupType, J \in \operatorname{AddEnd}\left(A\right), n \in Nat, v \in \operatorname{Row}\left(A, \operatorname{succ}\left(n\right)\right),\; \operatorname{C}\left(J, n, \operatorname{L}\left(J, n, v\right)\right) = \operatorname{pair}\left(\operatorname{add}\left(\operatorname{head}\left(\operatorname{D}\left(n, v\right)\right), \operatorname{apply}\left(J, \operatorname{if}\left(\operatorname{Odd}\left(\operatorname{succ}\left(n\right)\right), \operatorname{head}\left(\operatorname{D}\left(n, v\right)\right), 0\right)\right)\right), \operatorname{tail}\left(\operatorname{D}\left(n, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FiniteCompanionDefect.eliminate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Row(A,m) means Fin m -> A; AddEnd(A) means A ->+ A. AddCommGroupType displays the Lean type and its additive commutative group instance. D=domainEquiv and C=codomainEquiv; head and tail are product projections. L=companion has head v(0)+J(sum v) and adjacent-sum tails. The finite sum identity sum v = (if Odd(n+1) then v(0) else 0) + R(t) is proved by induction using cancellation of each adjacent pair. Thus C L D inverse is identity on the tail, and its head is a+J(a) at odd length or a at even length. C and D are separately defined codomain and domain equivalences: this is equivalence of an additive operator's domain and codomain, with no conjugacy claim. For A=Int, J=id and length one the remaining map is multiplication by two. Involutivity of J alone therefore does not imply a torsion-free cokernel. The original two-coefficient integer reset operator uses this same elimination, with J given by right multiplication by the nonidentity sign.

## References

- Truth anchor: `D5/S1/Recurrence/FiniteCompanionDefect.eliminate`
