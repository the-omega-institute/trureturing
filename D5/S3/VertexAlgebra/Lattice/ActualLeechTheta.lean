/- GID: D5/S3/VertexAlgebra/Lattice/ActualLeechTheta
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualLeechTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Golay-Leech charge theta series is E4 cubed minus 720 times the discriminant. -/

import D5.S3.Arith.Lattices.LatticeThetaTransformation
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralPower
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-! The theta series uses the same integral charges and Gram form as the actual
Golay-Leech lattice fields. Gaussian summability gives a common majorant on each
closed q-disk inside the unit disk. -/

set_option autoImplicit false

open Filter Function Metric ModularForm ModularGroup UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm Topology

namespace D5.S3.VertexAlgebra.Lattice.ActualLeechTheta

open D5.S3.Arith.Lattices.LatticeThetaTransformation
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticePositiveEnergy
open D5.S3.VertexAlgebra.ActualLeechHyperbolic (leechData leech_spec)
open D5.S3.VertexAlgebra.Lattice.ActualFixedC2 (leech_charge_norm_ge_four)

noncomputable section

private def energy (a : Charge leechData) : ℕ := (chargeEnergy leechData a).toNat

private lemma intCast_energy (a : Charge leechData) :
    (energy a : ℤ) = chargeEnergy leechData a :=
  Int.toNat_of_nonneg (chargeEnergy_nonneg leechData leech_spec.2.2.1 a)

private lemma energy_eq_zero_iff (a : Charge leechData) : energy a = 0 ↔ a = 0 := by
  have h : (energy a : ℤ) = 0 ↔ a = 0 := by
    rw [intCast_energy, chargeEnergy_eq_zero_iff leechData leech_spec.2.2.1]
  exact_mod_cast h

private lemma energy_ge_two (a : Charge leechData) (ha : a ≠ 0) : 2 ≤ energy a := by
  have hnorm := leech_charge_norm_ge_four a ha
  have hhalf := two_chargeEnergy leechData a
  rw [← intCast_energy a] at hhalf
  omega

private def thetaQ (q : ℂ) : ℂ := ∑' a : Charge leechData, q ^ energy a

private lemma gaussian_eq_q_pow (z : ℂ) (a : Charge leechData) :
    Complex.exp (Real.pi * Complex.I * z * (bilinear leechData a a : ℂ)) =
      Periodic.qParam 1 z ^ energy a := by
  have hnorm : (bilinear leechData a a : ℂ) = 2 * (energy a : ℂ) := by
    have h := (two_chargeEnergy leechData a).symm
    rw [← intCast_energy a] at h
    exact_mod_cast h
  rw [Periodic.qParam, ← Complex.exp_nat_mul, hnorm]
  simp only [Complex.ofReal_one, div_one]
  apply congrArg Complex.exp
  ring

private lemma summable_radius {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) :
    Summable (fun a : Charge leechData => ρ ^ energy a) := by
  let y : ℝ := -Real.log ρ / (2 * Real.pi)
  let z : ℂ := (y : ℂ) * Complex.I
  have hy : 0 < y := div_pos (neg_pos.mpr (Real.log_neg hρ hρ')) (by positivity)
  have hz : z.im = y := by simp [z]
  have hexponent : -2 * Real.pi * y = Real.log ρ := by
    dsimp [y]
    field_simp [Real.pi_ne_zero]
  have hq : ‖Periodic.qParam 1 z‖ = ρ := by
    rw [Periodic.norm_qParam, hz, div_one, hexponent, Real.exp_log hρ]
  have hs := (lattice_theta_S leechData leech_spec.2.2.1 leech_spec.2.1 12
    leech_spec.1 z (hz.symm ▸ hy)).1
  simpa only [gaussian_eq_q_pow, norm_pow, hq] using hs

private lemma norm_term_le (a : Charge leechData) {q : ℂ} {ρ : ℝ} (hq : ‖q‖ ≤ ρ) :
    ‖q ^ energy a‖ ≤ ρ ^ energy a := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hq _

private lemma thetaQ_differentiableOn {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) :
    DifferentiableOn ℂ thetaQ (Metric.ball 0 ρ) :=
  Complex.differentiableOn_tsum_of_summable_norm
    (U := Metric.ball (0 : ℂ) ρ)
    (F := fun (a : Charge leechData) (q : ℂ) => q ^ energy a) (summable_radius hρ hρ')
    (fun a => (differentiable_id.pow (energy a)).differentiableOn) Metric.isOpen_ball
    (fun a _ hq => norm_term_le a (mem_ball_zero_iff.mp hq).le)

private lemma thetaQ_analytic {q : ℂ} (hq : ‖q‖ < 1) : AnalyticAt ℂ thetaQ q := by
  obtain ⟨ρ, hqρ, hρ⟩ := exists_between hq
  exact (thetaQ_differentiableOn ((norm_nonneg q).trans_lt hqρ) hρ).analyticAt
    (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hqρ))

private lemma thetaQ_zero : thetaQ 0 = 1 := by
  classical
  unfold thetaQ
  rw [tsum_eq_single (0 : Charge leechData)]
  · rw [(energy_eq_zero_iff 0).mpr rfl, pow_zero]
  · intro a ha
    exact zero_pow (fun h => ha ((energy_eq_zero_iff a).mp h))

private lemma thetaQ_deriv_zero : deriv thetaQ 0 = 0 := by
  have hderiv := Complex.hasSum_deriv_of_summable_norm
    (U := Metric.ball (0 : ℂ) (1 / 2))
    (F := fun (a : Charge leechData) (q : ℂ) => q ^ energy a)
    (summable_radius (ρ := 1 / 2) (by norm_num) (by norm_num))
    (fun a => (differentiable_id.pow (energy a)).differentiableOn) Metric.isOpen_ball
    (fun a _ hq => norm_term_le a (mem_ball_zero_iff.mp hq).le)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hterms : (fun a : Charge leechData => deriv (fun q : ℂ => q ^ energy a) 0) =
      (fun _ => 0) := by
    funext a
    rw [deriv_pow_field]
    by_cases ha : a = 0
    · rw [ha, (energy_eq_zero_iff 0).mpr rfl]
      simp
    · have hgap := energy_ge_two a ha
      rw [zero_pow (show energy a - 1 ≠ 0 by omega), mul_zero]
  rw [hterms] at hderiv
  exact hderiv.unique hasSum_zero

private def thetaFun (τ : ℍ) : ℂ := latticeTheta leechData (τ : ℂ)

private lemma thetaFun_eq_thetaQ (τ : ℍ) :
    thetaFun τ = thetaQ (Periodic.qParam 1 (τ : ℂ)) :=
  tsum_congr (gaussian_eq_q_pow (τ : ℂ))

private lemma thetaFun_mdifferentiable : MDiff thetaFun := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : DifferentiableOn ℂ (thetaQ ∘ Periodic.qParam 1) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact ((thetaQ_analytic (Periodic.norm_qParam_lt_one one_pos hz)).differentiableAt.comp z
      (Periodic.differentiable_qParam (h := 1)).differentiableAt).differentiableWithinAt
  refine h.congr fun z hz => ?_
  have him : 0 < z.im := hz
  simpa only [Function.comp_apply, ofComplex_apply_of_im_pos him]
    using thetaFun_eq_thetaQ (⟨z, him⟩ : ℍ)

private lemma thetaFun_tendsto : Tendsto thetaFun atImInfty (𝓝 1) := by
  have heq : thetaFun = thetaQ ∘ (fun τ : ℍ => Periodic.qParam 1 (τ : ℂ)) :=
    funext thetaFun_eq_thetaQ
  rw [heq, ← thetaQ_zero]
  exact (thetaQ_analytic (by simp : ‖(0 : ℂ)‖ < 1)).continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty one_pos)

private lemma thetaFun_S (τ : ℍ) :
    thetaFun (S • τ) = (τ : ℂ) ^ (12 : ℕ) * thetaFun τ := by
  have h := (lattice_theta_S leechData leech_spec.2.2.1 leech_spec.2.1 12
    leech_spec.1 (τ : ℂ) τ.im_pos).2
  have hphase : (-Complex.I) ^ (12 : ℕ) = 1 := by
    rw [show (12 : ℕ) = 2 * 6 by decide, pow_mul, neg_sq, Complex.I_sq]
    norm_num
  simpa only [thetaFun, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
    inv_neg, neg_div, one_div, mul_pow, hphase, one_mul] using h

private lemma thetaFun_slash_S : thetaFun ∣[(12 : ℤ)] S = thetaFun := by
  funext τ
  rw [SL_slash_apply, thetaFun_S, ModularGroup.denom_S, zpow_neg]
  change (τ : ℂ) ^ (12 : ℕ) * thetaFun τ * ((τ : ℂ) ^ (12 : ℕ))⁻¹ = thetaFun τ
  rw [mul_comm ((τ : ℂ) ^ (12 : ℕ)) (thetaFun τ), mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ τ.ne_zero), mul_one]

private lemma qParam_add_one (z : ℂ) : Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := by
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one,
    Complex.exp_add, Complex.exp_two_pi_mul_I]

private lemma thetaFun_slash_T : thetaFun ∣[(12 : ℤ)] T = thetaFun := by
  funext τ
  have hdenom : denom T τ = 1 := by
    rw [ModularGroup.denom_apply]
    simp [ModularGroup.T]
  rw [SL_slash_apply, hdenom, one_zpow, mul_one, thetaFun_eq_thetaQ (T • τ),
    thetaFun_eq_thetaQ τ, UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd,
    Complex.ofReal_one, add_comm 1 (τ : ℂ), qParam_add_one]

/-- The theta series of the actual Golay-Leech charges as a weight-twelve form. -/
def leechTheta : ModularForm 𝒮ℒ 12 where
  toFun := thetaFun
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    exact SlashInvariantForm.slash_action_generators_SL2Z thetaFun_slash_S thetaFun_slash_T γ
  holo' := thetaFun_mdifferentiable
  bdd_at_cusps' hc := by
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z thetaFun_slash_S thetaFun_slash_T γ]
    exact thetaFun_tendsto.isBigO_one ℝ

@[simp] theorem leechTheta_apply (τ : ℍ) :
    leechTheta τ = latticeTheta leechData (τ : ℂ) := rfl

private lemma cuspFunction_eq_thetaQ : Set.EqOn (cuspFunction 1 leechTheta) thetaQ
    (Metric.ball 0 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · subst q
    rw [UpperHalfPlane.cuspFunction_apply_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero leechTheta one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex leechTheta one_mem_strictPeriods_SL),
      thetaQ_zero]
    exact thetaFun_tendsto.limUnder_eq
  · let τ : ℍ := ⟨Periodic.invQParam 1 q,
      Periodic.im_invQParam_pos_of_norm_lt_one one_pos (mem_ball_zero_iff.mp hq) hq0⟩
    have hparam : Periodic.qParam 1 (τ : ℂ) = q := Periodic.qParam_right_inv one_ne_zero hq0
    calc
      cuspFunction 1 leechTheta q = leechTheta τ := by
        rw [← hparam]
        exact SlashInvariantFormClass.eq_cuspFunction leechTheta τ one_mem_strictPeriods_SL
          one_ne_zero
      _ = thetaQ q := (thetaFun_eq_thetaQ τ).trans (congrArg thetaQ hparam)

private lemma leechTheta_coeff_zero : (qExpansion 1 leechTheta).coeff 0 = 1 := by
  have h := cuspFunction_eq_thetaQ (Metric.mem_ball_self (zero_lt_one : (0 : ℝ) < 1))
  simpa [qExpansion_coeff, thetaQ_zero] using h

private lemma leechTheta_coeff_one : (qExpansion 1 leechTheta).coeff 1 = 0 := by
  have h : cuspFunction 1 leechTheta =ᶠ[𝓝 (0 : ℂ)] thetaQ :=
    Filter.Eventually.mono
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one :
        ∀ᶠ q : ℂ in 𝓝 0, q ∈ Metric.ball 0 1)
      fun _ hq => cuspFunction_eq_thetaQ hq
  simpa [qExpansion_coeff, h.deriv_eq] using thetaQ_deriv_zero

private def E4Cube : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3)

private lemma E4Cube_apply (τ : ℍ) : E4Cube τ = E₄ τ ^ (3 : ℕ) := by
  simp only [E4Cube, coe_mcast, coe_pow, Pi.pow_apply]

private lemma E4Cube_qExpansion :
    qExpansion 1 E4Cube = (qExpansion 1 E₄) ^ 3 := by
  rw [E4Cube, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

private lemma E4_constantCoeff : PowerSeries.constantCoeff (qExpansion 1 E₄) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact EisensteinSeries.E_qExpansion_coeff_zero (by decide : 3 ≤ (4 : ℕ)) ⟨2, rfl⟩

private lemma E4Cube_coeff_zero : (qExpansion 1 E4Cube).coeff 0 = 1 := by
  rw [E4Cube_qExpansion, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [E4_constantCoeff]

private lemma E4Cube_coeff_one : (qExpansion 1 E4Cube).coeff 1 = 720 := by
  rw [E4Cube_qExpansion, PowerSeries.coeff_one_pow]
  norm_num [E4_constantCoeff, E₄_qExpansion_coeff_one]

/-- The Leech theta identity in the space of weight-twelve modular forms. -/
theorem leechTheta_eq_E4Cube_sub_discriminant :
    leechTheta = ModularForm.mcast (by decide) (E₄.pow 3) -
      (720 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12) := by
  let f : ModularForm 𝒮ℒ 12 := leechTheta - E4Cube
  have hqf : qExpansion 1 f = qExpansion 1 leechTheta - qExpansion 1 E4Cube := by
    simpa only [f, FunLike.coe_sub] using
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL leechTheta E4Cube
  have hf0 : (qExpansion 1 f).coeff 0 = 0 := by
    rw [hqf, map_sub, leechTheta_coeff_zero, E4Cube_coeff_zero, sub_self]
  let g := ModularForm.toCuspForm f hf0
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hco : (c • CuspForm.discriminant : ℍ → ℂ) = (f : ℍ → ℂ) :=
    congrArg DFunLike.coe hc
  have hqΔ := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant
  rw [hco] at hqΔ
  have hcval : c = -720 := by
    have h := congrArg (fun P : PowerSeries ℂ => P.coeff 1) hqΔ
    simpa [hqf, leechTheta_coeff_one, E4Cube_coeff_one, PowerSeries.coeff_smul,
      CuspForm.coe_discriminant, discriminant_qExpansion_coeff_one] using h.symm
  have hform := congrArg (CuspForm.toModularFormₗ (Γ := 𝒮ℒ) (k := 12)) hc
  change c • (CuspForm.discriminant : ModularForm 𝒮ℒ 12) = leechTheta - E4Cube at hform
  rw [hcval] at hform
  change leechTheta = E4Cube - (720 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  calc
    leechTheta = (leechTheta - E4Cube) + E4Cube := (sub_add_cancel _ _).symm
    _ = E4Cube - (720 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12) := by
      rw [← hform]
      simpa only [sub_eq_add_neg, add_comm] using
        congrArg (E4Cube + ·) (neg_smul (720 : ℂ)
          (CuspForm.discriminant : ModularForm 𝒮ℒ 12))

/-- The all-charge theta series of the actual Leech lattice is
`E₄³ - 720 Δ` on the upper half-plane. -/
theorem latticeTheta_leech_eq_E4_cube_sub_discriminant (τ : ℍ) :
    latticeTheta leechData (τ : ℂ) = E₄ τ ^ (3 : ℕ) - (720 : ℂ) * discriminant τ := by
  have h := DFunLike.congr_fun leechTheta_eq_E4Cube_sub_discriminant τ
  change leechTheta τ = E4Cube τ - (720 : ℂ) * discriminant τ at h
  simpa only [leechTheta_apply, E4Cube_apply] using h

end
end D5.S3.VertexAlgebra.Lattice.ActualLeechTheta
