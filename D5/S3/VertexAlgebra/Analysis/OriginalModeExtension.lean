/- GID: D5/S3/VertexAlgebra/Analysis/OriginalModeExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalModeExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orthogonal-image Sobolev bounds and actual dense mode extensions. -/

import D5.S3.VertexAlgebra.Analysis.OriginalSobolev

/-!
Carpi--Tomassini, arXiv:2303.14097v2, Remark on smeared fields motivates the
consumer. The supplier is the original all-integer generating charged bound,
not an all-state extension. The higher-order proof uses actual orthogonal output
grades via energy_bound_of_grades; a scalar spectral inequality alone is not used
as an operator inequality. All original source/literature attributions are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator InnerProductSpace
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open Lattice.OriginalChargedEnergy OriginalGram LatticeAllStateField
open SourceBPZ.OriginalMatterHermitian
open private normD_smul from D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy
open private energy_bound_of_grades from
  D5.S3.VertexAlgebra.Energy.OriginalNeutralEnergy

open private charged_mode_grade Hm_charged_circle actual_phase from
  D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
open private norm_order_mono from
  D5.S3.VertexAlgebra.Analysis.OriginalSobolev

open Model

variable (M : Model)

def Model.order (a : Charge M.D) : ℕ := 2 * (chargeEnergy M.D a).toNat

/-- Circle indexing is m+d-1, with the original integral charge energy d. -/
def Model.mode (a : Charge M.D) (m : ℤ) : Module.End ℂ (Carrier M.D) :=
  (actualField M.D a)[[m + chargeEnergy M.D a - 1]]

private theorem zero_mode (m : ℤ) :
    M.mode 0 m = if m = 0 then LinearMap.id else 0 := by
  simp only [mode, actual_zero, chargeEnergy_zero, add_zero, identity_modes]
  simp only [show m-1 = -1 ↔ m = 0 by omega]

private theorem rank_zero_charge (hr : M.D.rank = 0) (a : Charge M.D) : a = 0 :=
  congrArg Prod.fst (rank_zero_label M.D hr (a,0))

private theorem zero_charge_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (v : Carrier M.D),
      normD (M.mode 0 m v) ≤ C * (1+|(m : ℝ)|)^(M.order 0) *
        normD ((M.energyOperator ^ M.order 0) v) := by
  refine ⟨1, zero_lt_one, fun m v => ?_⟩
  simp only [order, chargeEnergy_zero, Int.toNat_zero, mul_zero, pow_zero,
    one_mul, Module.End.one_apply, zero_mode]
  split_ifs <;> simp [normD]

private theorem base_bound_exists (a : Charge M.D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (v : Carrier M.D),
      normD (M.mode a m v) ≤ C * (1+|(m : ℝ)|)^(M.order a) *
        normD ((M.energyOperator ^ M.order a) v) := by
  by_cases hr : M.D.rank = 0
  · have ha := rank_zero_charge M hr a
    subst a
    exact zero_charge_bound M
  · by_cases ha : a = 0
    · subst a
      exact zero_charge_bound M
    · have hd := Int.toNat_of_nonneg (chargeEnergy_nonneg M.D M.positive a)
      simpa only [order, mode, hd] using charged_energy_bound M.positive M.inverse
        M.inverse_left M.inverse_right a ha

/-- Fixed before every mode and every input vector, also at zero charge. -/
def Model.modeConstant (a : Charge M.D) : ℝ := (base_bound_exists M a).choose

private theorem modeConstant_pos (a : Charge M.D) : 0 < M.modeConstant a :=
  (base_bound_exists M a).choose_spec.1

private theorem base_bound (a : Charge M.D) (m : ℤ) (v : Carrier M.D) :
    normD (M.mode a m v) ≤ M.modeConstant a * (1+|(m : ℝ)|)^(M.order a) *
      normD ((M.energyOperator ^ M.order a) v) :=
  (base_bound_exists M a).choose_spec.2 m v

private theorem higher_grade_bound (a : Charge M.D) (m : ℤ) (k E : ℕ)
    (v : Carrier M.D) (hv : v ∈ grade M.D (E : ℤ)) :
    normD ((M.energyOperator ^ k) (M.mode a m v)) ≤
      (M.modeConstant a * (1+|(m : ℝ)|)^(M.order a+k)) *
        ((E : ℝ)+1)^(M.order a+k) * normD v := by
  have hC := modeConstant_pos M a
  let u := M.mode a m v
  have hu : u ∈ grade M.D ((E : ℤ)-m) := charged_mode_grade a _ m v hv
  by_cases hneg : (E : ℤ)-m < 0
  · have hz := negative_grade_eq_zero M.positive _ hneg u hu
    change normD ((M.energyOperator ^ k) u) ≤ _
    rw [hz, map_zero]
    simp only [normD, Hm_zero_left, Complex.zero_re, Real.sqrt_zero]
    positivity
  · let F := ((E : ℤ)-m).toNat
    have hF : (F : ℤ) = (E : ℤ)-m := Int.toNat_of_nonneg (le_of_not_gt hneg)
    have huF : u ∈ grade M.D (F : ℤ) := by rw [hF]; exact hu
    have hFr : (F : ℝ) = (E : ℝ)-(m : ℝ) := by exact_mod_cast hF
    have hscalar : (F : ℝ)+1 ≤ (1+|(m : ℝ)|)*((E : ℝ)+1) := by
      rw [hFr]
      nlinarith [neg_le_abs (m : ℝ), abs_nonneg (m : ℝ),
        mul_nonneg (abs_nonneg (m : ℝ)) (Nat.cast_nonneg (α := ℝ) E)]
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (F : ℝ)+1) hscalar k
    have hb := base_bound M a m v
    rw [sobolev_grade_norm M (M.order a) E v hv] at hb
    change normD ((M.energyOperator ^ k) u) ≤ _
    rw [sobolev_grade_norm M k F u huF]
    calc
      _ ≤ ((1+|(m : ℝ)|)*((E : ℝ)+1))^k *
          (M.modeConstant a * (1+|(m : ℝ)|)^(M.order a) *
            (((E : ℝ)+1)^(M.order a) * normD v)) :=
        mul_le_mul hp hb (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow, pow_add, pow_add]; ring

private theorem higher_bound (a : Charge M.D) (m : ℤ) (k : ℕ) (v : Carrier M.D) :
    normD ((M.energyOperator ^ k) (M.mode a m v)) ≤
      M.modeConstant a * (1+|(m : ℝ)|)^(M.order a+k) *
        normD ((M.energyOperator ^ (M.order a+k)) v) := by
  apply energy_bound_of_grades M.positive M.inverse M.inverse_left M.inverse_right
    ((M.energyOperator ^ k) * M.mode a m) (-m)
    (M.modeConstant a * (1+|(m : ℝ)|)^(M.order a+k))
    (by have hC := modeConstant_pos M a; positivity) (M.order a+k) ?_ ?_ v
  · intro E u hu
    have hmode := charged_mode_grade a E m u hu
    change M.mode a m u ∈ grade M.D (E-m) at hmode
    rw [Module.End.mul_apply]
    change ((1+sugawaraMode M.D M.inverse 0)^k) (M.mode a m u) ∈ _
    rw [energy_power_grade M.inverse M.inverse_left M.inverse_right _ _ hmode k]
    simpa [sub_eq_add_neg] using (grade M.D (E-m)).smul_mem
      ((((E-m : ℤ) : ℂ)+1)^k) hmode
  · exact fun E u hu => higher_grade_bound M a m k E u hu

/-- The dense extension is an actual bounded operator between Sobolev completions. -/
def Model.modeExtension (a : Charge M.D) (k : ℕ) (m : ℤ) :
    M.Sobolev (M.order a+k) →L[ℂ] M.Sobolev k :=
  ((M.embed k).comp (M.mode a m)).extendOfNorm (M.embed (M.order a+k))

private theorem modeExtension_embed (a : Charge M.D) (k : ℕ) (m : ℤ)
    (v : Carrier M.D) :
    M.modeExtension a k m (M.embed (M.order a+k) v) = M.embed k (M.mode a m v) := by
  apply LinearMap.extendOfNorm_eq (embed_dense M _)
  refine ⟨M.modeConstant a * (1+|(m : ℝ)|)^(M.order a+k), fun u => ?_⟩
  simpa only [LinearMap.comp_apply, embed_norm] using higher_bound M a m k u

private theorem modeExtension_norm (a : Charge M.D) (k : ℕ) (m : ℤ) :
    ‖M.modeExtension a k m‖ ≤ M.modeConstant a * (1+|(m : ℝ)|)^(M.order a+k) := by
  apply LinearMap.opNorm_extendOfNorm_le (embed_dense M _)
    (by have hC := modeConstant_pos M a; positivity)
  intro v
  simpa only [LinearMap.comp_apply, embed_norm] using higher_bound M a m k v

private theorem modeExtension_compatible (a : Charge M.D) (j k : ℕ) (hjk : j ≤ k)
    (m : ℤ) :
    (M.inclusion j k hjk).comp (M.modeExtension a k m) =
      (M.modeExtension a j m).comp
        (M.inclusion (M.order a+j) (M.order a+k) (Nat.add_le_add_left hjk _)) := by
  ext x
  refine (embed_dense M _).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [ContinuousLinearMap.comp_apply, modeExtension_embed, inclusion_embed]

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
