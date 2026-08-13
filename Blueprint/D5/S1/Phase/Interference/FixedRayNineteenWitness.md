# Fixed Ray Nineteen Witness

## Abstract

Two admissible cases on the same modulus nineteen have different Jacobi selector values.

**Definition 1.1 (The fixed ray modulus is nineteen).**

$$fixedRayModulus=19$$

*Formalization.* `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRayModulus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness fixes the ray datum to the explicit modulus nineteen.

**Definition 1.2 (Admissibility is the inverse-residue congruence).**

$$fixedRayAdmissible(beta, gamma)=4betagamma \equiv -1 (\operatorname{mod} 19)$$

*Formalization.* `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRayAdmissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Admissibility is the frozen inverse-residue condition specialized to modulus nineteen.

**Definition 1.3 (The selector is the Jacobi value at nineteen).**

$$fixedRaySelector(beta)=\operatorname{jacobi}(beta,19)$$

*Formalization.* `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRaySelector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selector is defined independently as the Jacobi symbol of the beta numerator at the fixed ray.

**Theorem 1.4 (The first admissible case has selector one).**

$$fixedRayAdmissible(1,14) \land fixedRaySelector(1)=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_case_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit pair beta one and gamma fourteen satisfies the congruence and has selector one.

**Theorem 1.5 (The second admissible case has selector minus one).**

$$fixedRayAdmissible(2,7) \land fixedRaySelector(2)=-1$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_case_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit pair beta two and gamma seven satisfies the same congruence at nineteen and has selector minus one.

**Theorem 1.6 (The same ray admits unequal selectors).**

$$\exists beta,gamma,betaPrime,gammaPrime\in \mathbb{Z},\ fixedRayAdmissible(beta,gamma) \land fixedRayAdmissible(betaPrime,gammaPrime) \land fixedRaySelector(beta)\neq fixedRaySelector(betaPrime)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_nineteen_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two displayed cases share the same modulus nineteen but their selector values differ, providing the concrete fixed-ray refutation.

**Theorem 1.7 (No ray-only character fits both cases).**

$$\neg \exists chi: \mathbb{Z}\to\mathbb{Z},\ \forall beta,gamma\in\mathbb{Z},\ fixedRayAdmissible(beta,gamma) \Rightarrow fixedRaySelector(beta)=chi(fixedRayModulus)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/FixedRayNineteenWitness.no_fixed_ray_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any function of the fixed ray value would assign the same result to both admissible cases, contradicting their checked unequal selectors.

## References

- Truth anchor: `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRayAdmissible`
- Truth anchor: `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRayModulus`
- Truth anchor: `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRaySelector`
- Truth anchor: `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_case_one`
- Truth anchor: `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_case_two`
- Truth anchor: `D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_nineteen_witness`
- Truth anchor: `D5/S1/Phase/Interference/FixedRayNineteenWitness.no_fixed_ray_character`
- Dependency: [D5/S1/Phase/Interference/ZolotarevSelector](ZolotarevSelector.md)
