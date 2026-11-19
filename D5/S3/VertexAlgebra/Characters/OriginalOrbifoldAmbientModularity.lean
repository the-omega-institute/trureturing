/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAmbientModularity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldAmbientModularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized original Leech ambient trace is S invariant. -/

import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter
import D5.S3.VertexAlgebra.Lattice.LatticeSectorCharacterWeilCovariance

/-! The untwisted identity trace of the original Golay–Leech orbifold on the upper half-plane. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators
open Complex Matrix

namespace D5.S3.VertexAlgebra.OriginalOrbifoldAmbientModularity

open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldAnalyticCharacter (ambientCharacter nome)
open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticePositiveEnergy
  (chargeEnergy chargeEnergy_nonneg two_chargeEnergy complex_inverse_exists)
open LatticeSugawaraCurrents (gramComplex)
open LatticeTwoCurrentThermal (chargeTheta oscillatorCharacter)
open LatticeDiscriminantTheta LatticeDiscriminantWeil LatticeSectorCharacterWeilCovariance
open D5.S3.Fourier.MatrixGaussian (quadratic theta)

open private zero_sector from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private oscillator_eta character_formula from
  D5.S3.VertexAlgebra.Lattice.LatticeSectorCharacterWeilCovariance

private theorem chargeTheta_eq_theta (D : LatticeData) (hD : (gramReal D).PosDef) (τ : ℂ) :
    chargeTheta D (nome τ) = theta (gramReal D) τ := by
  unfold chargeTheta theta
  apply tsum_congr
  intro a
  have hq : quadratic (gramReal D) (fun i => (a i : ℝ)) = (bilinear D a a : ℝ) := by
    simp [gramReal, quadratic, bilinear, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [hq, ← two_chargeEnergy, nome, ← exp_nat_mul]
  push_cast
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (chargeEnergy_nonneg D hD a)]
  congr 1
  ring

/-- The ambient shifted trace is the theta series of the actual Leech Gram matrix
divided by the rank-24 eta factor. -/
theorem ambientCharacter_eq_theta_div_eta (τ : ℂ) (hτ : 0 < τ.im) :
    ambientCharacter τ = theta (gramReal leechData) τ / ModularForm.eta τ ^ (24 : ℕ) := by
  have hshift : exp (-2 * Real.pi * I * τ * (leechData.rank : ℂ) / 24) = (nome τ)⁻¹ := by
    rw [nome, ← exp_neg, leech_spec.1]
    push_cast
    congr 1
    ring
  have hosc := oscillator_eta leechData τ hτ
  rw [hshift, leech_spec.1] at hosc
  have hnormalized : (nome τ)⁻¹ * oscillatorCharacter leechData (nome τ) =
      (ModularForm.eta τ ^ (24 : ℕ))⁻¹ := hosc
  rw [ambientCharacter, chargeTheta_eq_theta leechData leech_spec.2.2.1,
    mul_left_comm, hnormalized, div_eq_mul_inv]

/-- The ambient trace agrees with the normalized actual dual-coset trace at the zero class.
The zero sector is evaluated using the zero representative of the undoubled Gram matrix. -/
theorem ambientCharacter_eq_sectorCharacter
    (H : Matrix (Fin leechData.rank) (Fin leechData.rank) ℂ)
    (hHG : H * gramComplex leechData = 1) (hGH : gramComplex leechData * H = 1)
    (τ : ℂ) (hτ : 0 < τ.im) :
    ambientCharacter τ = sectorCharacter leechData leech_spec.2.2.1 H hHG hGH 0 τ := by
  have heta := congrArg (fun n : ℕ => ModularForm.eta τ ^ n) leech_spec.1
  rw [ambientCharacter_eq_theta_div_eta τ hτ,
    (character_formula leechData leech_spec.2.2.1 H hHG hGH 0 τ hτ).2,
    zero_sector leechData leech_spec.2.2.1 τ hτ, heta]

private theorem unimodular_discriminant_subsingleton (D : LatticeData) (hD : IsUnit D.G.det) :
    Subsingleton (Discriminant D) := by
  have hzero (a : Discriminant D) : a = 0 := by
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (p := gramRange D) a
    obtain ⟨n, hn⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 (D.G.isUnit_iff_isUnit_det.2 hD)) r
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨n, hn⟩
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- Modular S fixes the original untwisted Leech ambient trace. -/
theorem ambientCharacter_s_invariant (τ : ℂ) (hτ : 0 < τ.im) :
    ambientCharacter (-1 / τ) = ambientCharacter τ := by
  let : Fact (gramReal leechData).PosDef := ⟨leech_spec.2.2.1⟩
  let : Subsingleton (Discriminant leechData) :=
    unimodular_discriminant_subsingleton leechData leech_spec.2.1
  let : Fintype (Discriminant leechData) := Fintype.ofFinite _
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists leechData leech_spec.2.2.1
  have hS : 0 < (-1 / τ).im := by
    simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨τ, hτ⟩ : UpperHalfPlane)
  rw [ambientCharacter_eq_sectorCharacter H hHG hGH _ hS,
    ambientCharacter_eq_sectorCharacter H hHG hGH τ hτ,
    (lattice_sector_character_s_transform leechData leech_spec.2.2.1 H hHG hGH 0 τ hτ).2]
  change (rho leechData)⁻¹ * (∑ b : Discriminant leechData,
    pairingCharacter leechData leech_spec.2.2.1 0 (-b) *
      sectorCharacter leechData leech_spec.2.2.1 H hHG hGH b τ) = _
  rw [Fintype.sum_subsingleton _ (0 : Discriminant leechData)]
  simp only [rho, Nat.card_unique, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one,
    inv_one, neg_zero, AddChar.map_zero_eq_one, one_mul]

#print axioms ambientCharacter_eq_theta_div_eta
#print axioms ambientCharacter_eq_sectorCharacter
#print axioms ambientCharacter_s_invariant

end D5.S3.VertexAlgebra.OriginalOrbifoldAmbientModularity
