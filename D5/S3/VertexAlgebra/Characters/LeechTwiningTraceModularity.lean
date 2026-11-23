/- GID: D5/S3/VertexAlgebra/Characters/LeechTwiningTraceModularity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LeechTwiningTraceModularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The rank-24 twining and twisted discriminant quotients at level one. -/

import D5.S3.Arith.ModularForms.IntegralDiscriminant
import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.LatticeHalfFockParityT

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Filter Function ModularForm ModularFormClass SlashInvariantFormClass
open UpperHalfPlane hiding I
open scoped MatrixGroups Manifold ModularForm Topology

namespace D5.S3.VertexAlgebra.LeechTwiningTraceModularity

local notation "Δ" => ModularForm.discriminant
local notation "S" => ModularGroup.S
local notation "T" => ModularGroup.T
local notation "𝕢" => Function.Periodic.qParam

/-- The argument of the discriminant in the untwisted insertion. -/
def double (τ : ℍ) : ℍ :=
  ⟨2 * (τ : ℂ), by
    change 0 < (2 * (τ : ℂ)).im
    simpa [Complex.mul_im] using mul_pos (by norm_num : (0 : ℝ) < 2) τ.im_pos⟩

/-- The unshifted argument in the twisted trace. -/
def half (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) / 2, by simpa [Complex.div_ofNat_im] using half_pos τ.im_pos⟩

/-- The shifted argument in the parity-inserted trace. -/
def halfShift (τ : ℍ) : ℍ := half (T • τ)

@[simp] private lemma coe_double (τ : ℍ) : (double τ : ℂ) = 2 * (τ : ℂ) := rfl
@[simp] private lemma coe_half (τ : ℍ) : (half τ : ℂ) = (τ : ℂ) / 2 := rfl

private lemma coe_S (τ : ℍ) : (↑(S • τ) : ℂ) = -1 / (τ : ℂ) := by
  rw [coe_specialLinearGroup_apply S τ]
  simp [ModularGroup.S]

private lemma coe_T (τ : ℍ) : (↑(T • τ) : ℂ) = (τ : ℂ) + 1 := by
  rw [coe_specialLinearGroup_apply T τ]
  simp [ModularGroup.T]

@[simp] private lemma coe_halfShift (τ : ℍ) :
    (halfShift τ : ℂ) = ((τ : ℂ) + 1) / 2 := by
  rw [halfShift, coe_half, coe_T]

/-- The untwisted trace with the lattice involution inserted. -/
def B (τ : ℍ) : ℂ := Δ τ / Δ (double τ)

/-- The twisted trace with identity insertion. -/
def U (τ : ℍ) : ℂ := 4096 * (Δ τ / Δ (half τ))

/-- The twisted trace with oscillator parity inserted. -/
def P (τ : ℍ) : ℂ := -(4096 * (Δ τ / Δ (halfShift τ)))

/-- The three terms in the rank-24 twining contribution. -/
def twiningSum (τ : ℍ) : ℂ := B τ + U τ - P τ

private lemma delta_sl (γ : SL(2, ℤ)) (τ : ℍ) :
    Δ (γ • τ) = ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 12 * Δ τ := by
  have h := SlashInvariantForm.slash_action_generators_SL2Z
    discriminant_S_invariant discriminant_T_invariant γ
  have hp := (ModularForm.slash_action_eq'_iff (12 : ℤ) Δ γ τ).mp
    (congrFun h τ)
  simpa only [zpow_ofNat] using hp

private lemma delta_S (τ : ℍ) : Δ (S • τ) = (τ : ℂ) ^ 12 * Δ τ := by
  simpa [ModularGroup.S] using delta_sl S τ

private lemma delta_T (τ : ℍ) : Δ (T • τ) = Δ τ := by
  simpa [ModularGroup.T] using delta_sl T τ

private lemma double_S (τ : ℍ) : double (S • τ) = S • half τ := by
  apply UpperHalfPlane.ext
  rw [coe_double, coe_S, coe_S, coe_half]
  field_simp [τ.ne_zero] <;> ring

private lemma half_S (τ : ℍ) : half (S • τ) = S • double τ := by
  apply UpperHalfPlane.ext
  rw [coe_half, coe_S, coe_S, coe_double]
  field_simp [τ.ne_zero] <;> ring

private def halfShiftMatrix : SL(2, ℤ) :=
  ⟨!![1, -1; 2, -1], by norm_num [Matrix.det_fin_two_of]⟩

private lemma halfShift_S (τ : ℍ) : halfShift (S • τ) = halfShiftMatrix • halfShift τ := by
  apply UpperHalfPlane.ext
  rw [coe_halfShift, coe_S, coe_specialLinearGroup_apply, coe_halfShift]
  have h00 : algebraMap ℤ ℝ (halfShiftMatrix 0 0) = 1 := by
    change algebraMap ℤ ℝ (1 : ℤ) = 1
    simp
  have h01 : algebraMap ℤ ℝ (halfShiftMatrix 0 1) = -1 := by
    change algebraMap ℤ ℝ (-1 : ℤ) = -1
    simp
  have h10 : algebraMap ℤ ℝ (halfShiftMatrix 1 0) = 2 := by
    change algebraMap ℤ ℝ (2 : ℤ) = 2
    norm_num
  have h11 : algebraMap ℤ ℝ (halfShiftMatrix 1 1) = -1 := by
    change algebraMap ℤ ℝ (-1 : ℤ) = -1
    simp
  have hd : (2 : ℂ) * (((τ : ℂ) + 1) / 2) + -1 = τ := by ring
  simp only [h00, h01, h10, h11, Complex.ofReal_one, Complex.ofReal_neg,
    Complex.ofReal_ofNat, one_mul, hd]
  field_simp [τ.ne_zero] <;> ring

private lemma delta_halfShift_S (τ : ℍ) :
    Δ (halfShift (S • τ)) = (τ : ℂ) ^ 12 * Δ (halfShift τ) := by
  rw [halfShift_S, delta_sl]
  have h : ((halfShiftMatrix 1 0 : ℤ) : ℂ) * (halfShift τ : ℂ) +
      ((halfShiftMatrix 1 1 : ℤ) : ℂ) = τ := by
    change ((2 : ℤ) : ℂ) * (halfShift τ : ℂ) + ((-1 : ℤ) : ℂ) = τ
    push_cast
    rw [coe_halfShift]
    ring
  rw [h]

private lemma double_T (τ : ℍ) : double (T • τ) = T • (T • double τ) := by
  apply UpperHalfPlane.ext
  rw [coe_double, coe_T, coe_T, coe_T, coe_double]
  ring

private lemma halfShift_T (τ : ℍ) : halfShift (T • τ) = T • half τ := by
  apply UpperHalfPlane.ext
  rw [coe_halfShift, coe_T, coe_T, coe_half]
  ring

theorem B_S (τ : ℍ) : B (S • τ) = U τ := by
  rw [B, U, double_S, delta_S, delta_S, coe_half, div_pow]
  norm_num
  field_simp [τ.ne_zero, discriminant_ne_zero] <;> ring

theorem U_S (τ : ℍ) : U (S • τ) = B τ := by
  rw [U, B, half_S, delta_S, delta_S, coe_double, mul_pow]
  norm_num
  field_simp [τ.ne_zero, discriminant_ne_zero] <;> ring

theorem P_S (τ : ℍ) : P (S • τ) = P τ := by
  simp only [P, delta_S, delta_halfShift_S]
  rw [mul_div_mul_left _ _ (pow_ne_zero 12 τ.ne_zero)]

theorem B_T (τ : ℍ) : B (T • τ) = B τ := by
  simp only [B, double_T, delta_T]

theorem U_T (τ : ℍ) : U (T • τ) = -P τ := by
  simp only [U, P, delta_T, halfShift, neg_neg]

theorem P_T (τ : ℍ) : P (T • τ) = -U τ := by
  simp only [P, U, halfShift_T, delta_T]

theorem twiningSum_S (τ : ℍ) : twiningSum (S • τ) = twiningSum τ := by
  simp only [twiningSum, B_S, U_S, P_S]
  ring

theorem twiningSum_T (τ : ℍ) : twiningSum (T • τ) = twiningSum τ := by
  simp only [twiningSum, B_T, U_T, P_T]
  ring

private def deltaOnComplex (z : ℂ) : ℂ := ModularForm.eta z ^ 24

private lemma differentiableAt_deltaOnComplex {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ deltaOnComplex z :=
  (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 24

theorem twiningSum_holo : MDiff twiningSum := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  let f : ℂ → ℂ := fun z =>
    deltaOnComplex z / deltaOnComplex (2 * z) +
      4096 * (deltaOnComplex z / deltaOnComplex (z / 2)) -
      -(4096 * (deltaOnComplex z / deltaOnComplex ((z + 1) / 2)))
  have hf : DifferentiableOn ℂ f {z | 0 < z.im} := by
    intro z hz
    let τ : ℍ := ⟨z, hz⟩
    have hid : DifferentiableAt ℂ (fun x : ℂ => x) z := differentiableAt_id
    have hdpos : 0 < (2 * z).im := (double τ).im_pos
    have hhpos : 0 < (z / 2).im := (half τ).im_pos
    have hd : DifferentiableAt ℂ (fun x : ℂ => deltaOnComplex (2 * x)) z :=
      DifferentiableAt.fun_comp' (f := fun x : ℂ => 2 * x) z
        (differentiableAt_deltaOnComplex hdpos) (hid.const_mul (2 : ℂ))
    have hh : DifferentiableAt ℂ (fun x : ℂ => deltaOnComplex (x / 2)) z :=
      DifferentiableAt.fun_comp' (f := fun x : ℂ => x / 2) z
        (differentiableAt_deltaOnComplex hhpos) (hid.div_const (2 : ℂ))
    have hsc : (halfShift τ : ℂ) = (z + 1) / 2 := coe_halfShift τ
    have hspos : 0 < ((z + 1) / 2).im := by
      rw [← hsc]
      exact (halfShift τ).im_pos
    have hs : DifferentiableAt ℂ (fun x : ℂ => deltaOnComplex ((x + 1) / 2)) z :=
      DifferentiableAt.fun_comp' (f := fun x : ℂ => (x + 1) / 2) z
        (differentiableAt_deltaOnComplex hspos) ((hid.add_const (1 : ℂ)).div_const (2 : ℂ))
    have hsn : deltaOnComplex ((z + 1) / 2) ≠ 0 := by
      rw [← hsc]
      exact discriminant_ne_zero (halfShift τ)
    have h := differentiableAt_deltaOnComplex hz
    have hB := h.div hd (discriminant_ne_zero (double τ))
    have hU := (h.div hh (discriminant_ne_zero (half τ))).const_mul (4096 : ℂ)
    have hP := (h.div hs hsn).const_mul (4096 : ℂ)
    exact ((hB.add hU).sub hP.neg).differentiableWithinAt
  refine hf.congr ?_
  intro z hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, twiningSum, B, U, P,
    ModularForm.discriminant, deltaOnComplex, coe_double, coe_half, coe_halfShift, f]

private def twiningProduct (τ : ℍ) : ℂ := twiningSum τ * Δ τ

private lemma twiningProduct_slash (γ : SL(2, ℤ)) :
    twiningProduct ∣[(12 : ℤ)] γ = twiningProduct := by
  have hS : twiningSum ∣[(0 : ℤ)] S = twiningSum := by
    funext τ
    simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using twiningSum_S τ
  have hT : twiningSum ∣[(0 : ℤ)] T = twiningSum := by
    funext τ
    simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using twiningSum_T τ
  have hh := SlashInvariantForm.slash_action_generators_SL2Z hS hT γ
  funext τ
  have hτ : twiningSum (γ • τ) = twiningSum τ := by
    simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using congrFun hh τ
  apply (ModularForm.slash_action_eq'_iff (12 : ℤ) twiningProduct γ τ).mpr
  simp only [twiningProduct, hτ, delta_sl, zpow_ofNat]
  ring

private def deltaFactor (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

@[simp] private lemma deltaFactor_zero : deltaFactor 0 = 1 := by
  simp [deltaFactor, pow_succ]

private lemma delta_eq_factor (τ : ℍ) : Δ τ = 𝕢 1 τ * deltaFactor (𝕢 1 τ) := by
  exact discriminant_eq_q_prod τ

private lemma deltaFactor_ne_zero (τ : ℍ) : deltaFactor (𝕢 1 τ) ≠ 0 := by
  intro h
  exact discriminant_ne_zero τ (by simp [delta_eq_factor, h])

private lemma analyticAt_deltaFactor_zero : AnalyticAt ℂ deltaFactor 0 :=
  (differentiableOn_tprod_one_sub_pow_pow 24).analyticAt
    (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

private lemma delta_coeff_two : (qExpansion 1 Δ).coeff 2 = -24 := by
  rw [D5.S3.Arith.ModularForms.discriminantCoefficient_correct]
  have h : D5.S3.Arith.ModularForms.discriminantCoefficient 2 = -24 := by decide +kernel
  rw [h]
  norm_num

private lemma deltaFactor_hasDerivAt : HasDerivAt deltaFactor (-24) 0 := by
  have he : cuspFunction 1 Δ =ᶠ[𝓝 (0 : ℂ)] (fun q => q * deltaFactor q) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    exact discriminant_cuspFunction_eqOn hq
  have hi : ContDiffAt ℂ 2 (fun q : ℂ => q) 0 := by fun_prop
  have h := delta_coeff_two
  rw [qExpansion_coeff, Filter.EventuallyEq.iteratedDeriv_eq 2 he,
    iteratedDeriv_fun_mul hi analyticAt_deltaFactor_zero.contDiffAt] at h
  have hd : deriv deltaFactor 0 = -24 := by
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id_zero, iteratedDeriv_one] at h
    linear_combination h
  simpa only [hd] using analyticAt_deltaFactor_zero.differentiableAt.hasDerivAt

private def untwistedProduct (q : ℂ) : ℂ := deltaFactor q ^ 2 / deltaFactor (q ^ 2)

@[simp] private lemma untwistedProduct_zero : untwistedProduct 0 = 1 := by
  simp [untwistedProduct]

private lemma untwistedProduct_hasDerivAt : HasDerivAt untwistedProduct (-48) 0 := by
  have hsq : HasDerivAt (fun q : ℂ => q ^ 2) 0 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).fun_pow 2
  have hc : HasDerivAt (fun q : ℂ => deltaFactor (q ^ 2)) 0 0 := by
    simpa only [Function.comp_def, mul_zero] using
      (deltaFactor_hasDerivAt.comp_of_eq (0 : ℂ) hsq (by simp))
  have h := (deltaFactor_hasDerivAt.fun_pow 2).fun_div hc (by simp)
  norm_num [untwistedProduct] at h ⊢
  exact h

private lemma q_double (τ : ℍ) : 𝕢 1 (double τ) = (𝕢 1 τ) ^ 2 := by
  simp only [Function.Periodic.qParam, coe_double, ← Complex.exp_nat_mul,
    Nat.cast_ofNat, Complex.ofReal_one]
  congr 1
  ring

private lemma q_half (τ : ℍ) : 𝕢 1 (half τ) = 𝕢 2 τ := by
  simp only [Function.Periodic.qParam, coe_half, Complex.ofReal_one, Complex.ofReal_ofNat]
  congr 1
  ring

private lemma q_two_square (τ : ℍ) : (𝕢 2 τ) ^ 2 = 𝕢 1 τ := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, Nat.cast_ofNat,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  congr 1
  ring

private lemma q_halfShift (τ : ℍ) : 𝕢 1 (halfShift τ) = -𝕢 2 τ := by
  rw [Function.Periodic.qParam, coe_halfShift]
  have h : 2 * (Real.pi : ℂ) * I * (((τ : ℂ) + 1) / 2) / (1 : ℝ) =
      2 * (Real.pi : ℂ) * I * τ / (2 : ℝ) + (Real.pi : ℂ) * I := by
    push_cast
    ring
  rw [h, exp_add, exp_pi_mul_I]
  simp [Function.Periodic.qParam]

private lemma B_mul_delta (τ : ℍ) : B τ * Δ τ = untwistedProduct (𝕢 1 τ) := by
  rw [B, untwistedProduct, ← q_double, delta_eq_factor τ, delta_eq_factor (double τ),
    q_double]
  have hd : deltaFactor (𝕢 1 τ ^ 2) ≠ 0 := by
    rw [← q_double]
    exact deltaFactor_ne_zero (double τ)
  field_simp [Function.Periodic.qParam_ne_zero, hd] <;> ring

private lemma twisted_div_q_tendsto (a : ℍ → ℍ)
    (hsq : ∀ τ, (𝕢 1 (a τ)) ^ 2 = 𝕢 1 τ)
    (ha : Tendsto (fun τ => 𝕢 1 (a τ)) atImInfty (𝓝 0)) :
    Tendsto (fun τ => (Δ τ / Δ (a τ) * Δ τ) / 𝕢 1 τ) atImInfty (𝓝 0) := by
  have hq := qParam_tendsto_atImInfty one_pos
  have hd := analyticAt_deltaFactor_zero.continuousAt.tendsto
  have hda : Tendsto (fun τ => deltaFactor (𝕢 1 (a τ))) atImInfty (𝓝 1) := by
    simpa only [Function.comp_def, deltaFactor_zero] using hd.comp ha
  have hdq : Tendsto (fun τ : ℍ => deltaFactor (𝕢 1 τ)) atImInfty (𝓝 1) := by
    simpa only [Function.comp_def, deltaFactor_zero] using hd.comp hq
  have h := (ha.mul (hdq.pow 2)).div hda one_ne_zero
  simp only [zero_mul, zero_div] at h
  refine h.congr fun τ => ?_
  change (𝕢 1 (a τ) * deltaFactor (𝕢 1 τ) ^ 2) / deltaFactor (𝕢 1 (a τ)) =
    (Δ τ / Δ (a τ) * Δ τ) / 𝕢 1 τ
  rw [delta_eq_factor τ, delta_eq_factor (a τ), ← hsq τ]
  field_simp [Function.Periodic.qParam_ne_zero, deltaFactor_ne_zero] <;> ring

private lemma twisted_part_div_q_tendsto :
    Tendsto (fun τ : ℍ => ((U τ - P τ) * Δ τ) / 𝕢 1 τ) atImInfty (𝓝 0) := by
  have ht := qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 2)
  have hu := twisted_div_q_tendsto half
    (fun τ => by rw [q_half, q_two_square]) (by simpa only [q_half] using ht)
  have hp := twisted_div_q_tendsto halfShift
    (fun τ => by rw [q_halfShift, neg_sq, q_two_square])
    (by simpa only [q_halfShift, neg_zero] using ht.neg)
  have h := (hu.const_mul (4096 : ℂ)).add (hp.const_mul (4096 : ℂ))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun τ => ?_
  simp only [U, P, sub_neg_eq_add, add_mul, add_div, mul_div_assoc, mul_assoc]

private lemma twiningProduct_sub_one_div_q_tendsto :
    Tendsto (fun τ : ℍ => (twiningProduct τ - 1) / 𝕢 1 τ) atImInfty (𝓝 (-48)) := by
  have hq : Tendsto (fun τ : ℍ => 𝕢 1 τ) atImInfty (𝓝[≠] (0 : ℂ)) :=
    (Function.Periodic.qParam_tendsto one_pos).comp tendsto_coe_atImInfty
  have h := (untwistedProduct_hasDerivAt.tendsto_slope_zero.comp hq).add
    twisted_part_div_q_tendsto
  simp only [add_zero, zero_add, untwistedProduct_zero, smul_eq_mul, Function.comp_def] at h
  refine h.congr fun τ => ?_
  rw [twiningProduct, twiningSum, show B τ + U τ - P τ = B τ + (U τ - P τ) by ring,
    add_mul, B_mul_delta]
  simp only [div_eq_mul_inv]
  ring

private lemma twiningProduct_tendsto : Tendsto twiningProduct atImInfty (𝓝 1) := by
  have h := (twiningProduct_sub_one_div_q_tendsto.mul
    (qParam_tendsto_atImInfty one_pos)).add
      (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 1))
  simp only [mul_zero, zero_add] at h
  refine h.congr fun τ => ?_
  rw [div_mul_cancel₀ _ (Function.Periodic.qParam_ne_zero τ), sub_add_cancel]

/-- Multiplication by the discriminant gives a holomorphic level-one form of weight 12. -/
def twiningForm : ModularForm 𝒮ℒ 12 where
  toFun := twiningProduct
  slash_action_eq' _ hA := by
    obtain ⟨A, rfl⟩ := hA
    exact twiningProduct_slash A
  holo' := twiningSum_holo.mul (ModularFormClass.holo CuspForm.discriminant)
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [twiningProduct_slash]
    exact twiningProduct_tendsto.isBigO_one ℝ

theorem twiningForm_coeff_zero : (qExpansion 1 twiningForm).coeff 0 = 1 :=
  tendsto_nhds_unique
    (ModularFormClass.tendsto_atImInfty twiningForm one_pos one_mem_strictPeriods_SL)
    twiningProduct_tendsto

theorem twiningForm_coeff_one : (qExpansion 1 twiningForm).coeff 1 = -48 := by
  let g := cuspFunction 1 twiningForm
  have hdiff : DifferentiableAt ℂ g 0 :=
    (ModularFormClass.analyticAt_cuspFunction_zero twiningForm one_pos
      one_mem_strictPeriods_SL).differentiableAt
  have hg0 : g 0 = 1 := by
    simpa [g, qExpansion_coeff] using twiningForm_coeff_zero
  have hq : Tendsto (fun τ : ℍ => 𝕢 1 τ) atImInfty (𝓝[≠] (0 : ℂ)) :=
    (Function.Periodic.qParam_tendsto one_pos).comp tendsto_coe_atImInfty
  have h := hdiff.hasDerivAt.tendsto_slope_zero.comp hq
  have h' : Tendsto (fun τ : ℍ => (twiningProduct τ - 1) / 𝕢 1 τ)
      atImInfty (𝓝 (deriv g 0)) := by
    refine h.congr fun τ => ?_
    simp only [Function.comp_apply, zero_add, smul_eq_mul, hg0, div_eq_mul_inv]
    rw [show g (𝕢 1 τ) = twiningProduct τ from
      SlashInvariantFormClass.eq_cuspFunction twiningForm τ one_mem_strictPeriods_SL one_ne_zero]
    exact mul_comm _ _
  simpa [qExpansion_coeff, iteratedDeriv_one, g] using
    tendsto_nhds_unique h' twiningProduct_sub_one_div_q_tendsto

private def eisensteinCube : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3)

private lemma eisensteinCube_qExpansion :
    qExpansion 1 eisensteinCube = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ := by
  rw [eisensteinCube, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

private lemma eisensteinCube_coeff_zero : (qExpansion 1 eisensteinCube).coeff 0 = 1 := by
  simp [eisensteinCube_qExpansion, PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
    EisensteinSeries.E_qExpansion_coeff_zero (by decide : 3 ≤ 4) ⟨2, rfl⟩]

private lemma eisensteinCube_coeff_one : (qExpansion 1 eisensteinCube).coeff 1 = 720 := by
  rw [eisensteinCube_qExpansion]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    -PowerSeries.coeff_zero_eq_constantCoeff, ModularForm.E₄_qExpansion_coeff_one,
    EisensteinSeries.E_qExpansion_coeff_zero (by decide : 3 ≤ 4) ⟨2, rfl⟩]

/-- The rank-24 twining sum is the indicated normalized level-one function. -/
theorem twiningSum_eq (τ : ℍ) : twiningSum τ = E₄ τ ^ 3 / Δ τ - 768 := by
  let f := twiningForm - eisensteinCube
  have hf0 : (qExpansion 1 f).coeff 0 = 0 := by
    simp only [f, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      map_sub, twiningForm_coeff_zero, eisensteinCube_coeff_zero, sub_self]
  have hf1 : (qExpansion 1 f).coeff 1 = -768 := by
    norm_num [f, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      twiningForm_coeff_one, eisensteinCube_coeff_one]
  let g := ModularForm.toCuspForm f hf0
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hfun : (c • CuspForm.discriminant : ℍ → ℂ) = f := by
    exact congrArg DFunLike.coe hc
  have hq := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c
    CuspForm.discriminant
  rw [hfun] at hq
  have hcoef := congrArg (PowerSeries.coeff 1) hq
  have hc' : c = -768 := by
    simpa [PowerSeries.coeff_smul, discriminant_qExpansion_coeff_one, hf1] using hcoef.symm
  have ht : c * Δ τ = twiningSum τ * Δ τ - E₄ τ ^ 3 := by
    change (c • CuspForm.discriminant : ℍ → ℂ) τ = _
    rw [hfun]
    simp only [f, FunLike.coe_sub, Pi.sub_apply, eisensteinCube, ModularForm.coe_mcast,
      ModularForm.coe_pow, Pi.pow_apply] <;> rfl
  rw [hc'] at ht
  exact eq_sub_of_add_eq (by
    apply (eq_div_iff (discriminant_ne_zero τ)).mpr
    linear_combination -ht)

section ActualTraces

open ActualLeechHyperbolic HalfFockSpectralFiberSource LatticeThetaCharacter
open LatticeHalfFockCharacter LatticeHalfFockParityT LatticeHalfFockGradedTrace

/-- The discriminant quotient is the full theta-inserted trace on the actual Leech grades. -/
theorem actual_theta_eq_B (τ : ℍ) :
    positiveFullThetaCharacter leechData (actualInverse leechData)
      (actualInverse_left leechData leech_spec.2.1)
      (actualInverse_right leechData leech_spec.2.1) leech_spec.2.2.1 τ = B τ := by
  have h := (positive_full_theta_character leechData (actualInverse leechData)
    (actualInverse_left leechData leech_spec.2.1)
    (actualInverse_right leechData leech_spec.2.1) leech_spec.2.2.1
    (q := 0) (by simp)).2.2.2 τ τ.im_pos
  calc
    _ = actualThetaCharacter leechData (actualInverse leechData)
        (actualInverse_left leechData leech_spec.2.1)
        (actualInverse_right leechData leech_spec.2.1) τ := h.2.2.1
    _ = (ModularForm.eta τ / ModularForm.eta (2 * (τ : ℂ))) ^ 24 := by
      simpa only [leech_spec.1] using
        (actual_theta_character_eta leechData (actualInverse leechData)
          (actualInverse_left leechData leech_spec.2.1)
          (actualInverse_right leechData leech_spec.2.1) τ τ.im_pos).2.2
    _ = B τ := by simp only [B, div_pow, ModularForm.discriminant, coe_double]

/-- The unshifted discriminant quotient is the trace on the actual twisted grades. -/
theorem actual_twisted_eq_U (τ : ℍ) :
    actualInsertedCharacter leechData leech_spec.2.1 LinearMap.id τ = U τ := by
  have h := (actual_character_modular leechData leech_spec.2.1 LinearMap.id τ τ.im_pos).2.2.1
  rw [LinearMap.trace_id, actual_ground_finrank] at h
  calc
    _ = _ := h
    _ = U τ := by
      rw [leech_spec.1]
      norm_num [U, ModularForm.discriminant, div_pow, coe_half]

/-- The signed half-shift is the actual parity trace, with the rank-24 phase. -/
theorem actual_parity_eq_P (τ : ℍ) :
    actualParityInsertedCharacter leechData leech_spec.2.1 LinearMap.id τ = P τ := by
  have h := (actual_paired_T leechData leech_spec.2.1 LinearMap.id τ τ.im_pos).1
  have hphase : exp (2 * (Real.pi : ℂ) * I * (leechData.rank : ℂ) / 48) = -1 := by
    rw [leech_spec.1]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  rw [hphase, neg_one_mul, ← coe_T τ, actual_twisted_eq_U, U_T] at h
  exact (neg_inj.mp h).symm

/-- The identity applied to the three original trace characters. -/
theorem actual_twining_trace_identity (τ : ℍ) :
    positiveFullThetaCharacter leechData (actualInverse leechData)
        (actualInverse_left leechData leech_spec.2.1)
        (actualInverse_right leechData leech_spec.2.1) leech_spec.2.2.1 τ +
      actualInsertedCharacter leechData leech_spec.2.1 LinearMap.id τ -
      actualParityInsertedCharacter leechData leech_spec.2.1 LinearMap.id τ =
      E₄ τ ^ 3 / Δ τ - 768 := by
  rw [actual_theta_eq_B, actual_twisted_eq_U, actual_parity_eq_P]
  exact twiningSum_eq τ

end ActualTraces

end D5.S3.VertexAlgebra.LeechTwiningTraceModularity

#print axioms D5.S3.VertexAlgebra.LeechTwiningTraceModularity.P_S
#print axioms D5.S3.VertexAlgebra.LeechTwiningTraceModularity.twiningSum_eq
#print axioms D5.S3.VertexAlgebra.LeechTwiningTraceModularity.actual_twining_trace_identity
