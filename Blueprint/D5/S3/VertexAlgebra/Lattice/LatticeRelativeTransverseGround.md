# Original transverse polynomial energy and relative shell

## Abstract

Original transverse polynomial energy and relative shell

The original state space is Carrier D tensor[Complex] the actual algebraic bc Fock space, with every integral charge retained. D is arbitrary LatticeData and F is its actual null frame. For any natural t, B is any complex basis indexed by Fin t of the actual transverse space F.K. B need not be real or orthonormal. H satisfies both inverse-Gram equations H gramComplex D = 1 and gramComplex D H = 1 wherever the original Sugawara zero mode is used. totalL0 is exactly matterMode D H 0 + ghostVirasoro D 0, without an identity shift.

The energy-preservation statements quantify independent integral charges p and q, including zero. Their original Ward, tensor cancellation, locally finite sums and inverse-count functional-calculus proofs are used in the literal shellD0 and shellH maps. P0 stability uses the original number spectrum and the same unshifted energy commutation; its b0 law is the existing original contraction law. No desired stability or energy certificate is a premise.

The independent polynomial space has variables Fin t times Nat. weight nu is the sum of nu(j,r) times r+1. energyTarget consists exactly of polynomials whose coefficients vanish unless weight nu + chargeEnergy D p = 1 in Int. target is its image under the existing actual groundMap F B p. These definitions mention neither P0 nor relativeMassShell. The ground ghost vector is the original ket {1}, with unshifted ghost energy -1. Ground coefficient recovery uses the original actualBasis and the injective transverse exponent map.

The homogeneous substitution theorem for the actual null-frame coordinate equivalence, the frozen Sugawara weighted-homogeneous theorem and the actual ghost zero-mode theorem give the exact ground-map energy formula. Linear extension gives its all-polynomial intertwining. Its zero kernel is the independent integer coefficient target. The frozen literal_relative_ground theorem then identifies this genuine image with relativeMassShell D H p intersect ker M. This is an algebraic application of those frozen suppliers; no literature novelty is claimed.

Inclusion is the literal subtype inclusion into the same relativeMassShell. Projection applies the original P0 and restricts its codomain using the proved image identification. shellD0 and shellH are the original d0 and h restricted using the actual preservation proofs. Their retraction and side identities reuse the original ambient contraction, square and zero-product laws. Only shell_contraction assumes pPlus p is nonzero. The polynomial target, its identification, stability and the empty shell theorem have no such assumption. If chargeEnergy D p exceeds one, the existing relativeMassShell_eq_bot_of_one_lt supplies the empty original shell; no zero cutoff is substituted for that result.

These statements do not assert full-Q perturbation, transferred cohomology, Hermitian descent, no-ghost positivity, Monster moonshine, a full VOA/CFT construction, anomaly or fusion completeness, string theory or AdS/CFT. The two retained energy source-family attempts remain unfinished under https://github.com/the-omega-institute/trureturing/issues/25847 and do not establish exact source selection or whole-source reconstruction. No registration has been completed for the additional ground and shell statements, and no declared_validated audit is claimed for them.

**Theorem 1.1 (d0_preserves_original_relative_constraints).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.d0_preserves_original_relative_constraints`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.d0_preserves_original_relative_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ), H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → ∀ (p q : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (x : D5.S3.VertexAlgebra.LatticeQuartetContraction.State D), (D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject p) x = x → D5.S3.VertexAlgebra.LatticeQuartetContraction.ghostB0 x = 0 → (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 + D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0) x = 0 → (D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject p) ((D5.S3.VertexAlgebra.LatticeQuartetContraction.d0 F q) x) = (D5.S3.VertexAlgebra.LatticeQuartetContraction.d0 F q) x ∧ D5.S3.VertexAlgebra.LatticeQuartetContraction.ghostB0 ((D5.S3.VertexAlgebra.LatticeQuartetContraction.d0 F q) x) = 0 ∧ (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 + D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0) ((D5.S3.VertexAlgebra.LatticeQuartetContraction.d0 F q) x) = 0

**Theorem 1.2 (h_preserves_original_relative_constraints).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.h_preserves_original_relative_constraints`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.h_preserves_original_relative_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ), H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → ∀ (p q : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (x : D5.S3.VertexAlgebra.LatticeQuartetContraction.State D), (D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject p) x = x → D5.S3.VertexAlgebra.LatticeQuartetContraction.ghostB0 x = 0 → (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 + D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0) x = 0 → (D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject p) ((D5.S3.VertexAlgebra.LatticeQuartetContraction.h F B q) x) = (D5.S3.VertexAlgebra.LatticeQuartetContraction.h F B q) x ∧ D5.S3.VertexAlgebra.LatticeQuartetContraction.ghostB0 ((D5.S3.VertexAlgebra.LatticeQuartetContraction.h F B q) x) = 0 ∧ (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 + D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0) ((D5.S3.VertexAlgebra.LatticeQuartetContraction.h F B q) x) = 0

**Definition 1.3 (Polynomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.Polynomial`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.Polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ℕ → Type

**Definition 1.4 (Exponent).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.Exponent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.Exponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ℕ → Type

**Definition 1.5 (weight).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.weight`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {t : ℕ} → D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Exponent t → ℕ

**Definition 1.6 (energyTarget).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyTarget`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: (D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData) → (t : ℕ) → D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D → Submodule ℂ (D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Polynomial t)

**Definition 1.7 (target).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) → {t : ℕ} → Module.Basis (Fin t) ℂ ↥F.K → D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D → Submodule ℂ (D5.S3.VertexAlgebra.LatticeQuartetContraction.State D)

**Definition 1.8 (groundIndex).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundIndex`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → {t : ℕ} → D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D → D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Exponent t → D5.S3.VertexAlgebra.LatticeQuartetContraction.StateIndex D t

**Theorem 1.9 (groundIndex_injective).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundIndex_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundIndex_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} {t : ℕ} (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), Function.Injective (D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.groundIndex p)

**Theorem 1.10 (groundMap_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (f : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Polynomial t) (nu : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Exponent t), ((D5.S3.VertexAlgebra.LatticeQuartetContraction.actualBasis F B).repr ((D5.S3.VertexAlgebra.LatticeQuartetContraction.groundMap F B p) f)) (D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.groundIndex p nu) = f.coeff nu

**Theorem 1.11 (groundMap_injective).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), Function.Injective ⇑(D5.S3.VertexAlgebra.LatticeQuartetContraction.groundMap F B p)

**Definition 1.12 (energyOperator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → {t : ℕ} → D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D → Module.End ℂ (D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Polynomial t)

**Theorem 1.13 (energyOperator_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} {t : ℕ} (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (f : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Polynomial t) (nu : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Exponent t), ((D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.energyOperator p) f).coeff nu = ↑(↑(D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.weight nu) + D5.S3.VertexAlgebra.LatticePositiveEnergy.chargeEnergy D p - 1) * f.coeff nu

**Theorem 1.14 (energyOperator_monomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} {t : ℕ} (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (nu : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Exponent t), (D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.energyOperator p) ((MvPolynomial.monomial nu) 1) = ↑(↑(D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.weight nu) + D5.S3.VertexAlgebra.LatticePositiveEnergy.chargeEnergy D p - 1) • (MvPolynomial.monomial nu) 1

**Theorem 1.15 (energyOperator_zero_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} {t : ℕ} (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (f : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Polynomial t), (D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.energyOperator p) f = 0 ↔ f ∈ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.energyTarget D t p

**Theorem 1.16 (frequencyWeight_mapDomain).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.frequencyWeight_mapDomain`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.frequencyWeight_mapDomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {t : ℕ} (nu : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Exponent t), (Finsupp.weight D5.S3.VertexAlgebra.LatticeLightConeCoordinates.frequencyWeight) (Finsupp.mapDomain D5.S3.VertexAlgebra.LatticeQuartetContraction.transverseVariable nu) = D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.weight nu

**Theorem 1.17 (ghost_ground_energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.ghost_ground_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.ghost_ground_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.energy {1} = -1

**Theorem 1.18 (totalL0_groundMap_monomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.totalL0_groundMap_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.totalL0_groundMap_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ), H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → ∀ (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (nu : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Exponent t), (D5.S3.VertexAlgebra.LatticeRelativeMassShell.totalL0 D H) ((D5.S3.VertexAlgebra.LatticeQuartetContraction.groundMap F B p) ((MvPolynomial.monomial nu) 1)) = ↑(↑(D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.weight nu) + D5.S3.VertexAlgebra.LatticePositiveEnergy.chargeEnergy D p - 1) • (D5.S3.VertexAlgebra.LatticeQuartetContraction.groundMap F B p) ((MvPolynomial.monomial nu) 1)

**Theorem 1.19 (totalL0_groundMap).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.totalL0_groundMap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.totalL0_groundMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ), H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → ∀ (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeMassShell.totalL0 D H ∘ₗ D5.S3.VertexAlgebra.LatticeQuartetContraction.groundMap F B p = D5.S3.VertexAlgebra.LatticeQuartetContraction.groundMap F B p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.energyOperator p

**Theorem 1.20 (groundMap_mem_shell_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_mem_shell_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_mem_shell_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ), H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → ∀ (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (f : D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.Polynomial t), (D5.S3.VertexAlgebra.LatticeQuartetContraction.groundMap F B p) f ∈ D5.S3.VertexAlgebra.LatticeRelativeMassShell.relativeMassShell D H p ↔ f ∈ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.energyTarget D t p

**Theorem 1.21 (target_eq_shell_inf_ker).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target_eq_shell_inf_ker`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target_eq_shell_inf_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ), H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → ∀ (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.target F B p = D5.S3.VertexAlgebra.LatticeRelativeMassShell.relativeMassShell D H p ⊓ LinearMap.ker (D5.S3.VertexAlgebra.LatticeQuartetContraction.M F)

**Theorem 1.22 (target_projection_fix).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target_projection_fix`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target_projection_fix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) (u : ↥(D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.target F B p)), (D5.S3.VertexAlgebra.LatticeQuartetContraction.P0 F B) ↑u = ↑u

**Definition 1.23 (inclusion).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.inclusion`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.inclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) → {t : ℕ} → (B : Module.Basis (Fin t) ℂ ↥F.K) → (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) → H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) → ↥(D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.target F B p) →ₗ[ℂ] ↥(D5.S3.VertexAlgebra.LatticeRelativeMassShell.relativeMassShell D H p)

**Definition 1.24 (shellP0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellP0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellP0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) → {t : ℕ} → Module.Basis (Fin t) ℂ ↥F.K → (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) → H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) → Module.End ℂ ↥(D5.S3.VertexAlgebra.LatticeRelativeMassShell.relativeMassShell D H p)

**Definition 1.25 (shellD0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellD0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellD0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D → (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) → H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) → Module.End ℂ ↥(D5.S3.VertexAlgebra.LatticeRelativeMassShell.relativeMassShell D H p)

**Definition 1.26 (shellH).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellH`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) → {t : ℕ} → Module.Basis (Fin t) ℂ ↥F.K → (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) → H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) → Module.End ℂ ↥(D5.S3.VertexAlgebra.LatticeRelativeMassShell.relativeMassShell D H p)

**Definition 1.27 (projection).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} → (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) → {t : ℕ} → (B : Module.Basis (Fin t) ℂ ↥F.K) → (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) → H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1 → D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1 → (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D) → ↥(D5.S3.VertexAlgebra.LatticeRelativeMassShell.relativeMassShell D H p) →ₗ[ℂ] ↥(D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.target F B p)

**Theorem 1.28 (projection_inclusion).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.projection F B H hHG hGH p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.inclusion F B H hHG hGH p = LinearMap.id

**Theorem 1.29 (inclusion_projection).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.inclusion_projection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.inclusion_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.inclusion F B H hHG hGH p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.projection F B H hHG hGH p = D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellP0 F B H hHG hGH p

**Theorem 1.30 (shell_d0_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_d0_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_d0_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellD0 F H hHG hGH p * D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellD0 F H hHG hGH p = 0

**Theorem 1.31 (shell_d0_inclusion).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_d0_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_d0_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellD0 F H hHG hGH p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.inclusion F B H hHG hGH p = 0

**Theorem 1.32 (projection_shell_d0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_shell_d0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_shell_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.projection F B H hHG hGH p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellD0 F H hHG hGH p = 0

**Theorem 1.33 (shell_contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), F.pPlus p ≠ 0 → D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellD0 F H hHG hGH p * D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellH F B H hHG hGH p + D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellH F B H hHG hGH p * D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellD0 F H hHG hGH p = 1 - D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.inclusion F B H hHG hGH p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.projection F B H hHG hGH p

**Theorem 1.34 (shell_h_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_h_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_h_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellH F B H hHG hGH p * D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellH F B H hHG hGH p = 0

**Theorem 1.35 (shell_h_inclusion).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_h_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_h_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellH F B H hHG hGH p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.inclusion F B H hHG hGH p = 0

**Theorem 1.36 (projection_shell_h).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_shell_h`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_shell_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compiled Lean type: ∀ {D : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.LatticeData} (F : D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ ↥F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D = 1) (hGH : D5.S3.VertexAlgebra.LatticeSugawaraCurrents.gramComplex D * H = 1) (p : D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.Charge D), D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.projection F B H hHG hGH p ∘ₗ D5.S3.VertexAlgebra.LatticeRelativeTransverseGround.shellH F B H hHG hGH p = 0

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.Exponent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.Polynomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.d0_preserves_original_relative_constraints`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyOperator_zero_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.energyTarget`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.frequencyWeight_mapDomain`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.ghost_ground_energy`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundIndex`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundIndex_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.groundMap_mem_shell_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.h_preserves_original_relative_constraints`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.inclusion_projection`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_shell_d0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.projection_shell_h`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellD0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellH`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shellP0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_d0_inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_d0_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_h_inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.shell_h_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target_eq_shell_inf_ker`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.target_projection_fix`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.totalL0_groundMap`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.totalL0_groundMap_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround.weight`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction](LatticeQuartetContraction.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell](LatticeRelativeMassShell.md)
