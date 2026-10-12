# The quarter-turn boundary recurrence

## Abstract

Two-sided integral normal form of identity plus squared reset time.

A is any additive commutative group; J is additive and J(Ja)=a for every a. Row(A,q) means Fin q -> A. Genuine time has head J(sum v) and successor v(j). squareDefect J n is id+(time(J,n) composed with time(J,n)), on length n+1. It is not the square of id+time. InvolutiveAddEnd records both the additive map and its universally quantified involution premise. All formulas use q=n+2. At length one, time=J, so the defect is exactly doubling. The proof does not require torsion freedom, division, finite generation or a field.

**Theorem 1.1 (Independent tail elimination).**

$$\forall A \in AddCommGroupType, J \in \operatorname{InvolutiveAddEnd}\left(A\right), n \in Nat, v \in \operatorname{Row}\left(A, \operatorname{add}\left(n, 2\right)\right),\; \operatorname{codomainEquiv}\left(J, n, \operatorname{squareDefect}\left(J, \operatorname{succ}\left(n\right), v\right)\right) = \operatorname{pair}\left(\operatorname{headResidual}\left(J, \operatorname{add}\left(n, 2\right), \operatorname{head}\left(\operatorname{domainEquiv}\left(n, v\right)\right)\right), \operatorname{tail}\left(\operatorname{domainEquiv}\left(n, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FiniteCompanionSquareDefect.eliminate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Domain coordinates are ((v(0),v(1)),t) with t(j)=v(j+2)+v(j). Reconstruction uses v(j+2)=t(j)-v(j), over any additive commutative group. Split reconstruction into the homogeneous seeds and the zero-seed tail. The codomain subtracts the two actual squareDefect heads of that zero-seed tail. The homogeneous recurrence is a,b,-a,-b. Induction computes (sum,last) as (0,-b), (a,a), (a+b,b), or (b,-a), according to q modulo four. The raw headResidual is (a+s+J(s-l),b+Js), where (s,l)=boundary(q,a,b).

**Theorem 1.2 (Complete period-four normal form).**

$$\forall A \in AddCommGroupType, J \in \operatorname{InvolutiveAddEnd}\left(A\right), n \in Nat, v \in \operatorname{Row}\left(A, \operatorname{add}\left(n, 2\right)\right),\; \operatorname{normalCodomainEquiv}\left(J, n, \operatorname{squareDefect}\left(J, \operatorname{succ}\left(n\right), v\right)\right) = \operatorname{pair}\left(\operatorname{headNormal}\left(J, \operatorname{add}\left(n, 2\right), \operatorname{head}\left(\operatorname{normalDomainEquiv}\left(J, n, v\right)\right)\right), \operatorname{tail}\left(\operatorname{normalDomainEquiv}\left(J, n, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FiniteCompanionSquareDefect.normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residue-dependent head column changes are (a+Jb,b), (a,b+Ja), (a,b+2a+Ja), and (a+b,b). The row change is identity except in residue two, where (r,s) goes to (r+Jr-s,r). Each has an explicit additive inverse. Their normal heads are (a,b), (2a,b), (3a+2Ja,b), and (a+Ja,b+Jb). The tail remains identity. These are two-sided operator equivalences, not conjugacy.

The stride-two recurrence has two independent seeds, whereas the adjacent-sum recurrence has one. Specializing J to the literal swap on Int[C2] produces a new cyclic-five obstruction and a rank-two resonance. On a torsion group, doubling or 3id+2J can have kernels; the integer classifications therefore belong to the reset arithmetic specialization, not to this general theorem.

## References

- Truth anchor: `D5/S1/Recurrence/FiniteCompanionSquareDefect.eliminate`
- Truth anchor: `D5/S1/Recurrence/FiniteCompanionSquareDefect.normal_form`
- Dependency: [D5/S1/Recurrence/FiniteCompanionDefect](FiniteCompanionDefect.md)
