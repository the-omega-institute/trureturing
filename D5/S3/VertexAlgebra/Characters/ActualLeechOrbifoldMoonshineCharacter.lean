/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldMoonshineCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldMoonshineCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech orbifold character and the nonzero BRST multiplicity recursion. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldTraceSeries
import D5.S3.VertexAlgebra.Characters.LeechTwiningTraceModularity
import D5.S3.VertexAlgebra.Lattice.ActualLeechTheta

/-! The actual Leech character from its four trace series and the resulting
coefficient recursion for nonzero relative BRST root spaces. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section

open Function UpperHalfPlane ModularForm
open scoped BigOperators MatrixGroups ModularForm

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldMoonshineCharacter

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (leechUnit leechPosDef)
open ActualLeechOrbifoldTraceSeries
open ActualLeechOrbifoldAllWeightDimension (weight_finrank weightMultiplicity twistedMultiplicity)
open LatticePositiveEnergy (EnergyFiber energy energyFiber_finite chargeEnergy_nonneg)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeThetaCharacter (positiveFullThetaCharacter)
open LatticeHalfFockCharacter (actualInsertedCharacter)
open LatticeHalfFockParityT (actualParityInsertedCharacter)
open Lattice.ActualLeechTheta (latticeTheta_leech_eq_E4_cube_sub_discriminant)
open LeechTwiningTraceModularity (actual_twining_trace_identity)

local notation "𝕢" => Periodic.qParam 1
local notation "Δ" => ModularForm.discriminant
local notation "A" => ordinaryCharacter
local notation "B" => positiveFullThetaCharacter leechData (actualInverse leechData)
  (actualInverse_left leechData leechUnit) (actualInverse_right leechData leechUnit) leechPosDef
local notation "U" => actualInsertedCharacter leechData leechUnit LinearMap.id
local notation "P" => actualParityInsertedCharacter leechData leechUnit LinearMap.id

/-- The two modular identities give the half-sum of the four literal traces. -/
theorem four_traces_eq_j_sub_744 (τ : ℍ) :
    (A τ + B τ + U τ - P τ) / 2 = E₄ τ ^ (3 : ℕ) / Δ τ - 744 := by
  have hA : A τ = E₄ τ ^ (3 : ℕ) / Δ τ - 720 := by
    rw [(ordinary_trace_series τ).2, latticeTheta_leech_eq_E4_cube_sub_discriminant]
    change (E₄ τ ^ (3 : ℕ) - 720 * Δ τ) / Δ τ = _
    field_simp [discriminant_ne_zero τ] <;> ring
  rw [hA]
  linear_combination (actual_twining_trace_identity τ) / 2

/-- The normalized graded dimension of the literal assembled stress eigenspaces. -/
theorem character_eq_j_sub_744 (τ : ℍ) :
    character τ = E₄ τ ^ (3 : ℕ) / Δ τ - 744 := by
  rw [character, ← tsum_mul_left, (graded_dimension_series τ).2.tsum_eq]
  exact four_traces_eq_j_sub_744 τ

/-- The holomorphic weight-twelve numerator of the normalized character. -/
def normalizedNumerator : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) -
    (744 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

private theorem normalizedNumerator_apply (τ : ℍ) :
    normalizedNumerator τ = E₄ τ ^ (3 : ℕ) - 744 * Δ τ := by
  simp only [normalizedNumerator, FunLike.coe_sub, Pi.sub_apply, ModularForm.coe_mcast,
    ModularForm.coe_pow, Pi.pow_apply] <;> rfl

private theorem delta_div_q_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => (qExpansion 1 Δ).coeff (n + 1) * 𝕢 τ ^ n) (Δ τ / 𝕢 τ) := by
  have h := ModularForm.hasSum_qExpansion (f := CuspForm.discriminant)
    one_pos one_mem_strictPeriods_SL τ
  have hzero : (qExpansion 1 Δ).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  have hshift : HasSum (fun n : ℕ => (qExpansion 1 Δ).coeff (n + 1) * 𝕢 τ ^ (n + 1))
      (Δ τ) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => (qExpansion 1 Δ).coeff n * 𝕢 τ ^ n) 1).mpr
    simpa [Finset.sum_range_one, hzero] using h
  have hdiv := hshift.div_const (𝕢 τ)
  simpa only [pow_succ, ← mul_assoc,
    mul_div_cancel_right₀ _ (Periodic.qParam_ne_zero (h := 1) (τ : ℂ))] using hdiv

/-- Coefficient comparison for the actual dimension series times the discriminant divided by q. -/
theorem dimension_delta_coefficient (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (dimension k : ℂ) * (qExpansion 1 Δ).coeff (n - k + 1)) =
      (qExpansion 1 normalizedNumerator).coeff n := by
  refine ModularFormClass.qExpansion_coeff_unique
    (f := normalizedNumerator) (c := fun m => ∑ k ∈ Finset.range (m + 1),
      (dimension k : ℂ) * (qExpansion 1 Δ).coeff (m - k + 1))
    one_pos one_mem_strictPeriods_SL ?_ n
  intro τ
  have hd := (graded_dimension_series τ).1
  have hΔ := delta_div_q_hasSum τ
  have hΔabs := summable_norm_iff.mpr hΔ.summable
  have hprod := hasSum_sum_range_mul_of_summable_norm hd hΔabs
  change HasSum
    (fun m : ℕ => ∑ k ∈ Finset.range (m + 1),
      ((dimension k : ℂ) * 𝕢 τ ^ k) *
        ((qExpansion 1 Δ).coeff (m - k + 1) * 𝕢 τ ^ (m - k)))
    ((∑' k : ℕ, (dimension k : ℂ) * 𝕢 τ ^ k) *
      (∑' j : ℕ, (qExpansion 1 Δ).coeff (j + 1) * 𝕢 τ ^ j)) at hprod
  rw [hΔ.tsum_eq] at hprod
  have hvalue : (∑' k : ℕ, (dimension k : ℂ) * 𝕢 τ ^ k) * (Δ τ / 𝕢 τ) =
      normalizedNumerator τ := by
    calc
      _ = Δ τ * character τ := by unfold character; ring
      _ = _ := by
        rw [character_eq_j_sub_744, normalizedNumerator_apply]
        field_simp [discriminant_ne_zero τ] <;> ring
  rw [hvalue] at hprod
  refine hprod.congr_fun ?_
  intro m
  rw [smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : 𝕢 τ ^ k * 𝕢 τ ^ (m - k) = 𝕢 τ ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [← hpow]
  ring

/-- The leading coefficient of the discriminant divided by q is one. -/
theorem dimension_recursion (n : ℕ) :
    (dimension n : ℂ) = (qExpansion 1 normalizedNumerator).coeff n -
      ∑ k ∈ Finset.range n, (dimension k : ℂ) * (qExpansion 1 Δ).coeff (n - k + 1) := by
  have h := dimension_delta_coefficient n
  rw [Finset.sum_range_succ, Nat.sub_self, zero_add, discriminant_qExpansion_coeff_one,
    mul_one] at h
  linear_combination h

private theorem dimension_eq_zero_of_neg (n : ℤ) (hn : n < 0) : dimension n = 0 := by
  classical
  letI : IsEmpty (EnergyFiber leechData n) :=
    ⟨fun x => by
      have h := x.2
      have hc := chargeEnergy_nonneg leechData leechPosDef x.1.1
      change energy leechData x.1 = n at h
      unfold energy at h
      omega⟩
  have hcard : Nat.card (EnergyFiber leechData n) = 0 := Nat.card_of_isEmpty
  have h := weight_finrank n
  change (dimension n : ℂ) = _ at h
  rw [weightMultiplicity, hcard, ite_eq_right (not_le.mpr hn),
    twistedMultiplicity, ite_eq_right (show ¬ 2 ≤ n by omega)] at h
  exact_mod_cast (show (dimension n : ℂ) = 0 by simpa using h)

end D5.S3.VertexAlgebra.ActualLeechOrbifoldMoonshineCharacter

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open ActualLeechOrbifoldTraceSeries (dimension)
open ActualLeechOrbifoldMoonshineCharacter (normalizedNumerator dimension_recursion)

local notation "Δ" => ModularForm.discriminant

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

local instance (p : Charge hyperbolicPlane) :
    AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup (GradedCycles planeFrame planeBasis p 1)

/-- At nonzero plane momentum the recursion reads the coefficient with Laurent
index minus the product of the two charge coordinates. -/
theorem ghost_one_finrank_nonzero_moonshine (p : Charge hyperbolicPlane) (hp : p ≠ 0) :
    let n : ℤ := 1 - p (0 : Fin 2) * p (1 : Fin 2)
    (Module.finrank ℂ (GradedCohomology planeFrame planeBasis p 1) : ℂ) =
      if 0 ≤ n then
        (qExpansion 1 normalizedNumerator).coeff n.toNat -
          ∑ k ∈ Finset.range n.toNat,
            (dimension k : ℂ) * (qExpansion 1 Δ).coeff (n.toNat - k + 1)
      else 0 := by
  dsimp only
  rw [(ghostOneCohomologyEquivNonzero p hp).finrank_eq]
  let n : ℤ := 1 - p (0 : Fin 2) * p (1 : Fin 2)
  change (dimension n : ℂ) =
    if 0 ≤ n then
      (qExpansion 1 normalizedNumerator).coeff n.toNat -
        ∑ k ∈ Finset.range n.toNat,
          (dimension k : ℂ) * (qExpansion 1 Δ).coeff (n.toNat - k + 1)
    else 0
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left hn]
    have h := dimension_recursion n.toNat
    rw [Int.toNat_of_nonneg hn] at h
    exact h
  · rw [ite_eq_right hn, ActualLeechOrbifoldMoonshineCharacter.dimension_eq_zero_of_neg n
      (lt_of_not_ge hn), Nat.cast_zero]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology

#print axioms D5.S3.VertexAlgebra.ActualLeechOrbifoldMoonshineCharacter.character_eq_j_sub_744
#print axioms D5.S3.VertexAlgebra.ActualLeechOrbifoldMoonshineCharacter.dimension_recursion
#print axioms D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology.ghost_one_finrank_nonzero_moonshine
