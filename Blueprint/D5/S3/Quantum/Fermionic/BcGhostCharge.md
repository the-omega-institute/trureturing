# Ghost number on countable occupation Fock space

## Abstract

Signed ghost number is an actual diagonal operator and a pointwise finite normal-ordered sum.

The carrier, vacuum, creators, annihilators and integer b and c modes are the original CountableOccupationFock and BcGhostFock objects. Charge counts odd occupied sites minus even occupied sites using integer subtraction. All casts in the operator formulas are into Complex. Products compose from right to left.

**Definition 1.1 (charge).**

$$\forall S \in \operatorname{Finset}\left(Nat\right),\; \operatorname{charge}\left(S\right) = \operatorname{Int}.\operatorname{ofNat}\left(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda(j:Nat)\mapsto(\operatorname{Nat}.\operatorname{mod}\left(j, 2\right) = 1), S\right)\right)\right) - \operatorname{Int}.\operatorname{ofNat}\left(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda(j:Nat)\mapsto(\operatorname{Nat}.\operatorname{mod}\left(j, 2\right) = 0), S\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.charge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty occupation has charge zero, an even singleton has charge minus one, and an odd singleton has charge plus one.

**Definition 1.2 (siteSign).**

$$\forall j \in Nat,\; \operatorname{siteSign}\left(j\right) = \operatorname{ite}\left(\operatorname{Nat}.\operatorname{mod}\left(j, 2\right) = 0, -1, 1\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.siteSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed contribution of one occupied site.

**Definition 1.3 (ghostNumber).**

$$\forall S \in \operatorname{Finset}\left(Nat\right),\; \operatorname{ghostNumber}\left(\operatorname{ket}\left(S\right)\right) = \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(\operatorname{charge}\left(S\right)\right), \operatorname{ket}\left(S\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.ghostNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finsupp.lsum extends this prescribed basis action complex linearly to every finite-excitation vector.

**Theorem 1.4 (ghost number relations).**

$$\operatorname{ghostNumber}\left(vacuum\right) = 0 \land \left(\left(\forall m \in Int,\; ghostNumber \cdot \operatorname{b}\left(m\right) - \operatorname{b}\left(m\right) \cdot ghostNumber = -\operatorname{b}\left(m\right)\right) \land \left(\forall m \in Int,\; ghostNumber \cdot \operatorname{c}\left(m\right) - \operatorname{c}\left(m\right) \cdot ghostNumber = \operatorname{c}\left(m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCharge.ghost_number_relations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Insertion and deletion change the integer occupation charge by opposite site signs. Applying the four mode branches proves both degree identities for every integer, including the zero modes.

**Definition 1.5 (siteTerm).**

$$\forall j \in Nat,\; \operatorname{siteTerm}\left(j\right) = \operatorname{smul}\left(\operatorname{Int}.\operatorname{cast}\left(\operatorname{siteSign}\left(j\right)\right), \operatorname{create}\left(j\right) \cdot \operatorname{annihilate}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.siteTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two Jordan–Wigner phases multiply to one on an occupied site; the bilinear vanishes on an empty site.

**Definition 1.6 (normalTerm).**

$$\forall n \in Int,\; \operatorname{normalTerm}\left(n\right) = \operatorname{ite}\left(n \le 1, \operatorname{c}\left(n\right) \cdot \operatorname{b}\left(-n\right), -\left(\operatorname{b}\left(-n\right) \cdot \operatorname{c}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.normalTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normal ordering uses the exact vacuum cuts at one and two.

**Definition 1.7 (modeSite).**

$$\forall n \in Int,\; \operatorname{modeSite}\left(n\right) = \operatorname{ite}\left(n \le 1, 2 \cdot \operatorname{Int}.\operatorname{toNat}\left(1 - n\right) + 1, 2 \cdot \operatorname{Int}.\operatorname{toNat}\left(n - 2\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.modeSite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This bijection labels odd sites by modes at most one and even sites by modes at least two.

**Definition 1.8 (siteMode).**

$$\forall j \in Nat,\; \operatorname{siteMode}\left(j\right) = \operatorname{ite}\left(\operatorname{Nat}.\operatorname{mod}\left(j, 2\right) = 0, \operatorname{Int}.\operatorname{ofNat}\left(\operatorname{Nat}.\operatorname{div}\left(j, 2\right)\right) + 2, 1 - \operatorname{Int}.\operatorname{ofNat}\left(\operatorname{Nat}.\operatorname{div}\left(j, 2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.siteMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse integer label of a natural occupation site.

**Definition 1.9 (activeModes).**

$$\forall v \in Fock,\; \operatorname{activeModes}\left(v\right) = \operatorname{Finset}.\operatorname{image}\left(siteMode, \operatorname{Finset}.\operatorname{biUnion}\left(\operatorname{Finsupp}.\operatorname{support}\left(v\right), id\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCharge.activeModes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union of the finite occupations in the support of this input supplies a finite set of integer labels.

**Theorem 1.10 (finite normal capture).**

$$\forall v \in Fock,\; \forall K \in \operatorname{Finset}\left(Int\right),\; \operatorname{Finset}.\operatorname{Subset}\left(\operatorname{activeModes}\left(v\right), K\right) \Rightarrow \operatorname{Finset}.\operatorname{sum}\left(K, \lambda(n:Int)\mapsto(\operatorname{normalTerm}\left(n\right))\right)\left(v\right) = \operatorname{ghostNumber}\left(v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCharge.finite_normal_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite superset of the active labels computes the actual ghost number on this input. The proof uses the exact occupied-site projection and the bijection between sites and integer modes.

**Theorem 1.11 (normal term finite support).**

$$\forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left(\lambda(n:Int)\mapsto(\operatorname{normalTerm}\left(n, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCharge.normal_term_finite_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support of the evaluated family is contained in activeModes v. This does not assert finite support of the endomorphism family.

**Theorem 1.12 (ghost number normal sum).**

$$\forall v \in Fock,\; \operatorname{ghostNumber}\left(v\right) = \operatorname{finsum}\left(\lambda(n:Int)\mapsto(\operatorname{normalTerm}\left(n, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCharge.ghost_number_normal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The locally finite sum is formed separately at each input. No infinite endomorphism sum is assumed.

These statements construct ghost number in the algebraic bc representation. They do not construct the total BRST operator, prove its square is zero, or establish a string or AdS/CFT theorem.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.activeModes`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.charge`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.finite_normal_capture`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.ghostNumber`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.ghost_number_normal_sum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.ghost_number_relations`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.modeSite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.normalTerm`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.normal_term_finite_support`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.siteMode`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.siteSign`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCharge.siteTerm`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostFock](BcGhostFock.md)
