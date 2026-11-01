# Exact Ward identities of the cubic ghost charge

## Abstract

Both cubic ghost Ward anticommutators

The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.

**Theorem 1.1 (ward b).**

$$\forall r \in Int,\; \operatorname{Qg} \cdot \operatorname{b}\left(r\right) + \operatorname{b}\left(r\right) \cdot \operatorname{Qg} = \operatorname{L}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRST.ward_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The CAR reduction gives two diagonals in the ordered pair sum. Each is half the actual Virasoro sum. The exchanges use supports on v and b r v, including all zero and edge modes.

**Theorem 1.2 (cc finite).**

$$\forall r \in Int,\; \forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left((p\mapsto\left(\operatorname{c}\left(p\right) \cdot \operatorname{c}\left(r - p\right)\right)\left(v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRST.cc_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a fixed occupation, p lies between r minus A and A. The statement holds on arbitrary finite linear combinations.

**Definition 1.3 (rTerm).**

$$\forall r \in Int,\; \forall p \in Int,\; \operatorname{rTerm}\left(r, p\right) = \operatorname{smul}\left(\operatorname{div}\left(1, 2\right) \cdot \operatorname{Int}.\operatorname{cast}\left(2 \cdot p - r\right), \operatorname{c}\left(p\right) \cdot \operatorname{c}\left(r - p\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostBRST.rTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the coefficient one half times two p minus r in the constrained pure-c quadratic.

**Theorem 1.4 (rTerm finite).**

$$\forall r \in Int,\; \forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left((p\mapsto\operatorname{rTerm}\left(r, p, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRST.rTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted pure-c family is locally finite on the actual input state.

**Definition 1.5 (R).**

$$\forall r \in Int,\; \forall v \in Fock,\; \operatorname{R}\left(r, v\right) = \sum_{p\in Int}^{fin}\operatorname{rTerm}\left(r, p, v\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostBRST.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is an actual complex-linear operator on the original Fock space.

**Theorem 1.6 (ward c).**

$$\forall r \in Int,\; \operatorname{Qg} \cdot \operatorname{c}\left(r\right) + \operatorname{c}\left(r\right) \cdot \operatorname{Qg} = \operatorname{R}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRST.ward_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal p plus q equal to r is reindexed only after proving its finite support on the actual state.

This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRST.R`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRST.cc_finite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRST.rTerm`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRST.rTerm_finite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRST.ward_b`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRST.ward_c`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCubic](BcGhostCubic.md)
