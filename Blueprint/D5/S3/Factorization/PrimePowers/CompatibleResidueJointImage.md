# Compatible Residue Joint Image

## Abstract

Two residue factors combine exactly along their common-modulus compatibility.

**Theorem 1.1 (The joint image is exactly the compatible-pair subobject).**

$$\forall m, n \in \mathbb{N},\\{}J_{m, n} = C_{m, n}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.joint_residue_image_eq_compatible_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural moduli m and n, an integer produces exactly those local residues whose integer representatives agree after reduction modulo gcd(m,n). No positivity or primality is used.

The proof applies Nat.chineseRemainder' for nonzero moduli and treats each zero-modulus branch directly via ZMod integer casts.

**Theorem 1.2 (Compatibility cuts the joint image out of the direct product).**

$$\forall m, n \in \mathbb{N},\\{}J_{m, n} \subseteq \operatorname{ZMod}(m) \times \operatorname{ZMod}(n) \land J_{m, n} = C_{m, n}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.joint_residue_image_is_compatible_subobject` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint image is contained in the full direct product and equals the named compatibleResiduePairs set. Thus the inclusion is paired with the actual cross-factor equation that selects the subobject.

**Theorem 1.3 (The compatible subobject is strict exactly for noncoprime moduli).**

$$\forall m, n \in \mathbb{N},\\{}J_{m, n} \subset \operatorname{ZMod}(m) \times \operatorname{ZMod}(n) \iff \gcd(m, n) \neq 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.joint_residue_image_ssubset_product_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair of residues zero and one witnesses incompatibility whenever gcd(m,n) is not one. Conversely, gcd one makes the compatibility factor ZMod 1 a singleton, so every product pair is compatible.

**Theorem 1.4 (Free realization occurs exactly for coprime moduli).**

$$\forall m, n \in \mathbb{N},\\{}\operatorname{Independent}(m, n) \iff \gcd(m, n) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.residue_realization_independent_iff_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Surjectivity of the joint readout is equivalent to gcd(m,n)=1. Hence coprime factors fill the product, equal moduli do so only at modulus one, and a modulus-one factor imposes no restriction.

**Theorem 1.5 (Local coverage does not imply independent joint realization).**

$$\operatorname{Surjective}(r_{2}) \land \operatorname{Surjective}(r_{2}) \land \neg\operatorname{Independent}(2, 2).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.local_factorization_does_not_imply_realization_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each integer readout into ZMod 2 is surjective, but their repeated joint readout has only compatible pairs and cannot realize the product pair (0,1).

The degenerate audit also covers inhabited carriers, modulus-zero identity readout, modulus-one constant readout, and the strict diagonal image at (0,0).

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.joint_residue_image_eq_compatible_pairs`
- Truth anchor: `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.joint_residue_image_is_compatible_subobject`
- Truth anchor: `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.joint_residue_image_ssubset_product_iff`
- Truth anchor: `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.local_factorization_does_not_imply_realization_independence`
- Truth anchor: `D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.residue_realization_independent_iff_coprime`
