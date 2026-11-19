/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumRigidity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The negative twisted Leech pair has fusion multiplicity one in the fixed sector. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumDetection
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumPairing
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedPairingExtension
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldNegativeTwistedPairingComparison

/-! The transformed vacuum pairing determines a lawful rational intertwiner.
The common fixed-mode adjoints and graded Schur comparison give uniqueness
up to scalar on the actual negative twisted Leech pair. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumRigidity

open scoped BigOperators VertexOperator
open ActualLeechHyperbolic (leechData leech_spec)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open OriginalOrbifoldFixedQuasiprimary (fixedL fixedL_val)
open OriginalOrbifoldNegativeTwistedPairingComparison (negative_twisted_pairing_eq_smul)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldTwistedPairingExtension (exists_shared_adjoint_of_quasiprimary)
open OriginalOrbifoldTwistedVacuumDetection (vacuumCoefficients vacuumCoefficients_injective)
open OriginalOrbifoldTwistedVacuumFusion
  (NegativeTwisted operatorSpace canonicalIntertwiner canonicalIntertwiner_ne_zero)
open OriginalOrbifoldTwistedVacuumPairing
open private exp_inverse linear_ext_on_weights vacuumModeForm vacuum_modes_finite from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumPairing

noncomputable section

local notation "X" => NegativeTwisted

private theorem rawVacuumPairing_injective : Function.Injective rawVacuumPairing := by
  intro J K h
  apply vacuumCoefficients_injective
  have coefficients (q : ℚ) : vacuumModeForm J q = vacuumModeForm K q := by
    apply linear_ext_on_weights
    intro s x hx
    apply linear_ext_on_weights
    intro t y hy
    by_cases hq : q = ((s + t - 1 : ℤ) : ℚ)
    · subst q
      change vacuumAt J s t x y = vacuumAt K s t x y
      rw [← rawVacuumPairing_eq_vacuumAt J s t x y hx hy,
        ← rawVacuumPairing_eq_vacuumAt K s t x y hx hy, h]
    · exact (vacuum_mode_eq_zero J s t x y hx hy q hq).trans
        (vacuum_mode_eq_zero K s t x y hx hy q hq).symm
  funext x q y
  exact LinearMap.congr_fun (LinearMap.congr_fun (coefficients q) x) y

private theorem twistedWeightSign_surjective : Function.Surjective twistedWeightSign := by
  have involution : twistedWeightSign.comp twistedWeightSign = LinearMap.id := by
    apply linear_ext_on_weights
    intro s x hx
    change twistedWeightSign (twistedWeightSign x) = x
    rw [twistedWeightSign_apply s x hx, map_smul, twistedWeightSign_apply s x hx, smul_smul,
      ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      (show Even (s + s) from ⟨s, rfl⟩).neg_one_zpow, one_smul]
  intro x
  exact ⟨twistedWeightSign x, LinearMap.congr_fun involution x⟩

private theorem transformedPairing_injective : Function.Injective transformedPairing := by
  have exp_surjective (z : ℂ) : Function.Surjective (twistedExp z) :=
    fun x => ⟨twistedExp (-z) x, exp_inverse z x⟩
  intro J K h
  exact rawVacuumPairing_injective
    ((LinearMap.compl₁₂_inj (g := (twistedExp 1).comp twistedWeightSign) (g' := twistedExp (-1))
      ((exp_surjective 1).comp twistedWeightSign_surjective) (exp_surjective (-1))).mp h)

private def rawVacuumPairingLinear : operatorSpace →ₗ[ℂ] LinearMap.BilinForm ℂ X where
  toFun := rawVacuumPairing
  map_add' J K := by
    apply LinearMap.ext₂
    intro x y
    change (∑ᶠ q : ℚ, vacuumModeForm (J + K) q x y) =
      (∑ᶠ q : ℚ, vacuumModeForm J q x y) + (∑ᶠ q : ℚ, vacuumModeForm K q x y)
    have coeff := congrFun (map_add vacuumCoefficients J K) x
    have h : (fun q : ℚ => vacuumModeForm (J + K) q x y) =
        fun q => vacuumModeForm J q x y + vacuumModeForm K q x y := by
      funext q
      exact congrFun (congrFun coeff q) y
    rw [h]
    exact finsum_add_distrib (vacuum_modes_finite J x y) (vacuum_modes_finite K x y)
  map_smul' c J := by
    apply LinearMap.ext₂
    intro x y
    change (∑ᶠ q : ℚ, vacuumModeForm (c • J) q x y) = c • (∑ᶠ q : ℚ, vacuumModeForm J q x y)
    have coeff := congrFun (map_smul vacuumCoefficients c J) x
    have h : (fun q : ℚ => vacuumModeForm (c • J) q x y) =
        fun q => c • vacuumModeForm J q x y := by
      funext q
      exact congrFun (congrFun coeff q) y
    rw [h]
    exact (smul_finsum' c (vacuum_modes_finite J x y)).symm

private def transformedPairingLinear : operatorSpace →ₗ[ℂ] LinearMap.BilinForm ℂ X where
  toFun := transformedPairing
  map_add' J K := by
    apply LinearMap.ext₂
    intro x y
    exact LinearMap.congr_fun (LinearMap.congr_fun (map_add rawVacuumPairingLinear J K)
      (twistedExp 1 (twistedWeightSign x))) (twistedExp (-1) y)
  map_smul' c J := by
    apply LinearMap.ext₂
    intro x y
    exact LinearMap.congr_fun (LinearMap.congr_fun (map_smul rawVacuumPairingLinear c J)
      (twistedExp 1 (twistedWeightSign x))) (twistedExp (-1) y)

set_option maxHeartbeats 1000000 in
-- The comparison elaborates the fixed modes and energy eigenspaces on the actual Leech carriers.
private theorem intertwiner_eq_smul_canonical (J : operatorSpace) :
    ∃ c : ℂ, J = c • canonicalIntertwiner := by
  have canonical_ne : transformedPairing canonicalIntertwiner ≠ 0 := by
    intro h
    apply canonicalIntertwiner_ne_zero
    apply transformedPairing_injective
    exact h.trans (map_zero transformedPairingLinear).symm
  obtain ⟨opposite, adjoint⟩ := exists_shared_adjoint_of_quasiprimary transformedPairing (by
    intro d a ha hqa n
    have hE : sugawaraMode leechData (gramComplex leechData)⁻¹ 1 a.val = 0 := by
      rw [← fixedL_val 1 a, hqa, Submodule.coe_zero]
    refine ⟨(-1 : ℂ) ^ (d : ℤ) •
      (fixedParityY leechData leech_spec.2.1 (-1) a)[[2 * (d : ℤ) - 2 - n]], ?_⟩
    intro K x y
    simpa only [LinearMap.smul_apply, map_smul] using
      transformedPairing_adjoint K a (d : ℤ) n ha hE x y)
  have orthogonal (K : operatorSpace) (i j : ℕ) (hij : i ≠ j)
      (x : twistedL0.eigenspace (i : ℂ)) (y : twistedL0.eigenspace (j : ℂ)) :
      transformedPairing K x y = 0 := by
    refine transformedPairing_grade_orthogonal K (i : ℤ) (j : ℤ) x y ?_ ?_ ?_
    · simpa only [Int.cast_natCast] using Module.End.mem_eigenspace_iff.mp x.property
    · simpa only [Int.cast_natCast] using Module.End.mem_eigenspace_iff.mp y.property
    · exact fun h => hij (Int.ofNat.inj h)
  obtain ⟨c, hc, _⟩ := negative_twisted_pairing_eq_smul (transformedPairing J)
    (transformedPairing canonicalIntertwiner) opposite canonical_ne
    (orthogonal J) (orthogonal canonicalIntertwiner)
    (fun a n x y => adjoint a n J x y) (fun a n x y => adjoint a n canonicalIntertwiner x y)
  refine ⟨c, transformedPairing_injective ?_⟩
  exact hc.trans (map_smul transformedPairingLinear c canonicalIntertwiner).symm

private def scalarEquiv : ℂ ≃ₗ[ℂ] operatorSpace :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ operatorSpace canonicalIntertwiner)
    ⟨smul_left_injective ℂ canonicalIntertwiner_ne_zero, fun J => by
      obtain ⟨c, hc⟩ := intertwiner_eq_smul_canonical J
      exact ⟨c, hc.symm⟩⟩

/-- The full rational intertwiner space for the negative twisted pair with
fixed-sector target has dimension one. -/
theorem leech_negative_twisted_pair_fusion_finrank :
    Module.finrank ℂ operatorSpace = 1 :=
  scalarEquiv.finrank_eq.symm.trans (Module.finrank_self ℂ)

#print axioms leech_negative_twisted_pair_fusion_finrank

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumRigidity
