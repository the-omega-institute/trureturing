# General Power Character Layer

## Abstract

Finite abelian power characters detect exactly the quotient by nth powers.

**Definition 1.1 (The complex nth roots of unity).**

$$mu_{n} = \{z \in \mathbb{C}^{\times} \mid z^{n} = 1\}.$$

*Formalization.* `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.complexNthRootsOfUnity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named target is Mathlib's subgroup of complex units whose nth power is one. At n zero this is the full complex unit group.

**Definition 1.2 (Characters of order dividing n).**

$$\operatorname{PowerCharacter}(G, n) = G \to mu_{n}.$$

*Formalization.* `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.PowerCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A power character is a group homomorphism into the named complex nth-root target; no surjectivity condition is imposed.

**Definition 1.3 (The subgroup of nth powers).**

$$G^{n} = \operatorname{range}(g \mapsto g^{n}).$$

*Formalization.* `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.powerSubgroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Commutativity makes the nth-power operation a homomorphism. Its range is the named subgroup denoted by G to the nth power.

**Definition 1.4 (The common kernel of all power characters).**

$$\operatorname{JointKernel}(G, n) = \operatorname{intersection}_{chi: G \to mu_{n}} \operatorname{ker}(chi).$$

*Formalization.* `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.powerCharacterJointKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint blind subgroup is the indexed intersection of the kernels of every homomorphism from G to the complex nth roots.

**Theorem 1.5 (Power characters detect exactly the quotient by nth powers).**

$$\operatorname{JointKernel}(G, n) = G^{n}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.power_character_joint_kernel_eq_power_subgroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every power character kills every nth power. Conversely, Mathlib's finite-abelian duality separates a point from the power subgroup by a complex-unit character.

A character trivial on nth powers has image in the complex nth roots, so it belongs to the indexed family and closes the reverse inclusion.

**Theorem 1.6 (The quotient by nth powers has exponent dividing n).**

$$\operatorname{exponent}(\operatorname{Quotient}(G, G^{n})) \mid n.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.power_quotient_has_exponent_dividing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every quotient class has nth power one because the nth power of each representative lies in the power subgroup.

**Theorem 1.7 (The power quotient is maximal among exponent-n quotients).**

$$G^{n} \leq H \iff\\{}\forall q \in \operatorname{Quotient}(G, H), q^{n} = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.power_subgroup_le_iff_quotient_pow_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A subgroup contains every nth power exactly when every class of its quotient has nth power one. This is the universal maximality asserted for the quotient seen by the character family.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.PowerCharacter`
- Truth anchor: `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.complexNthRootsOfUnity`
- Truth anchor: `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.powerCharacterJointKernel`
- Truth anchor: `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.powerSubgroup`
- Truth anchor: `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.power_character_joint_kernel_eq_power_subgroup`
- Truth anchor: `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.power_quotient_has_exponent_dividing`
- Truth anchor: `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.power_subgroup_le_iff_quotient_pow_eq_one`
