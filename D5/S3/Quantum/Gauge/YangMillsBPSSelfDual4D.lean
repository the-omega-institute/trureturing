/- GID: D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/YangMillsBPSSelfDual4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euclidean two-form splitting, Yang-Mills action bound, stress cancellation and normalized BPST charge. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D
import D5.S3.Geometry.Lorentz.DimensionSelection4D
import OmegaMath.Analysis.BPSTRadialIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.FinCases

/-! Euclidean electric and magnetic coordinates for Lie-algebra-valued two-forms.
The orientation is (0,1,2,3), and the color inner product initially uses unit
coordinate weights. The BPST action uses the trace pairing with weight one half. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Quantum.Gauge.YangMillsBPSSelfDual4D

abbrev E4 := NullConeGravity.E4

abbrev Components (r : ℕ) := Fin 3 → Fin r → ℝ

abbrev TwoForm4 (r : ℕ) := Components r × Components r

variable {r : ℕ}

/-- Exchange the electric and oriented magnetic components. -/
def hodge4 (F : TwoForm4 r) : TwoForm4 r := (F.2, F.1)

/-- Euclidean inner product in the six independent two-form coordinates. -/
def inner4 (F H : TwoForm4 r) : ℝ :=
  ∑ a, ∑ i, (F.1 i a * H.1 i a + F.2 i a * H.2 i a)

def normSq (F : TwoForm4 r) : ℝ := inner4 F F

def topDensity (F : TwoForm4 r) : ℝ := inner4 F (hodge4 F)

def selfDualPart (F : TwoForm4 r) : TwoForm4 r := (1 / 2 : ℝ) • (F + hodge4 F)

def antiSelfDualPart (F : TwoForm4 r) : TwoForm4 r := (1 / 2 : ℝ) • (F - hodge4 F)

/-- The complementary degree is two exactly when the coordinate index admits
    a four-coordinate frame. -/
theorem hodge4_coordinate_iff (D : ℕ) : D - 2 = 2 ↔ Nonempty (Fin D ≃ Fin 4) := by
  rw [D5.S3.Geometry.Lorentz.DimensionSelection4D.hodge_two_form_degree_iff]
  constructor
  · rintro rfl
    exact ⟨Equiv.refl _⟩
  · rintro ⟨e⟩
    simpa using Fintype.card_congr e

/-- Euclidean Hodge duality is involutive on two-forms. -/
theorem hodge4_involutive (F : TwoForm4 r) : hodge4 (hodge4 F) = F := by
  cases F
  rfl

theorem hodge4_isometry (F H : TwoForm4 r) :
    inner4 (hodge4 F) (hodge4 H) = inner4 F H := by
  unfold inner4
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  simp [hodge4, add_comm]

theorem sd_asd_orthogonal (F : TwoForm4 r) :
    inner4 (selfDualPart F) (antiSelfDualPart F) = 0 := by
  unfold inner4
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro i _
  simp [selfDualPart, antiSelfDualPart, hodge4]
  ring

theorem sd_asd_orthogonal_split (F : TwoForm4 r) :
    selfDualPart F + antiSelfDualPart F = F ∧
      hodge4 (selfDualPart F) = selfDualPart F ∧
      hodge4 (antiSelfDualPart F) = -antiSelfDualPart F ∧
      inner4 (selfDualPart F) (antiSelfDualPart F) = 0 := by
  refine ⟨?_, ?_, ?_, sd_asd_orthogonal F⟩
  all_goals
    apply Prod.ext <;> funext i a <;>
      simp [selfDualPart, antiSelfDualPart, hodge4] <;> ring

theorem norm_sq_eq_sd_add_asd (F : TwoForm4 r) :
    normSq F = normSq (selfDualPart F) + normSq (antiSelfDualPart F) := by
  unfold normSq inner4
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  simp [selfDualPart, antiSelfDualPart, hodge4]
  ring

theorem topological_density_eq_sd_sub_asd (F : TwoForm4 r) :
    topDensity F = normSq (selfDualPart F) - normSq (antiSelfDualPart F) := by
  unfold topDensity normSq inner4
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  simp [selfDualPart, antiSelfDualPart, hodge4]
  ring

private theorem normSq_nonneg (F : TwoForm4 r) : 0 ≤ normSq F := by
  unfold normSq inner4
  exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun i _ ↦
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

private theorem normSq_eq_zero (F : TwoForm4 r) : normSq F = 0 ↔ F = 0 := by
  constructor
  · intro h
    have hcolor : ∀ a : Fin r, ∑ i : Fin 3,
        (F.1 i a * F.1 i a + F.2 i a * F.2 i a) = 0 :=
      congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun a ↦ Finset.sum_nonneg fun i _ ↦
        add_nonneg (mul_self_nonneg (F.1 i a)) (mul_self_nonneg (F.2 i a))).mp h)
    have hcoord (a : Fin r) (i : Fin 3) :
        F.1 i a * F.1 i a + F.2 i a * F.2 i a = 0 :=
      congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun j ↦
        add_nonneg (mul_self_nonneg (F.1 j a)) (mul_self_nonneg (F.2 j a))).mp
        (hcolor a)) i
    apply Prod.ext <;> funext i a <;> change _ = (0 : ℝ)
    · nlinarith [hcoord a i, sq_nonneg (F.2 i a)]
    · nlinarith [hcoord a i, sq_nonneg (F.1 i a)]
  · rintro rfl
    simp [normSq, inner4]

theorem ym_bps_pointwise_identity (F : TwoForm4 r) :
    normSq F = (1 / 2) * normSq (F - hodge4 F) + topDensity F ∧
    normSq F = (1 / 2) * normSq (F + hodge4 F) - topDensity F := by
  unfold normSq topDensity inner4
  constructor
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    simp [hodge4]
    ring
  · simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    simp [hodge4]
    ring

theorem ym_bps_pointwise_bound (F : TwoForm4 r) : |topDensity F| ≤ normSq F := by
  have h := ym_bps_pointwise_identity F
  exact abs_le.mpr ⟨by linarith [normSq_nonneg (F + hodge4 F)],
    by linarith [normSq_nonneg (F - hodge4 F)]⟩

theorem ym_bps_equality_iff (F : TwoForm4 r) :
    (normSq F = topDensity F ↔ hodge4 F = F) ∧
    (normSq F = -topDensity F ↔ hodge4 F = -F) := by
  have h := ym_bps_pointwise_identity F
  constructor
  · constructor
    · intro he
      have hz : normSq (F - hodge4 F) = 0 := by linarith [h.1]
      exact (sub_eq_zero.mp ((normSq_eq_zero _).mp hz)).symm
    · intro he
      simp [he, normSq, topDensity]
  · constructor
    · intro he
      have hz : normSq (F + hodge4 F) = 0 := by linarith [h.2]
      exact eq_neg_of_add_eq_zero_right ((normSq_eq_zero _).mp hz)
    · intro he
      have hz : normSq (F + hodge4 F) = 0 := by
        rw [he, add_neg_cancel]
        exact (normSq_eq_zero _).mpr rfl
      linarith [h.2]

private theorem continuous_inner4 : Continuous (fun p : TwoForm4 r × TwoForm4 r ↦ inner4 p.1 p.2) := by
  unfold inner4
  fun_prop

private theorem continuous_normSq : Continuous (normSq : TwoForm4 r → ℝ) :=
  continuous_inner4.comp (continuous_id.prodMk continuous_id)

private theorem continuous_topDensity : Continuous (topDensity : TwoForm4 r → ℝ) :=
  continuous_inner4.comp (continuous_id.prodMk (continuous_snd.prodMk continuous_fst))

/-- Finite action and measurable curvature suffice for absolute integrability of the charge. -/
theorem ym_bps_action_bound (F : E4 → TwoForm4 r) (hF : Measurable F)
    (hact : Integrable (fun x ↦ normSq (F x))) :
    |∫ x, topDensity (F x)| ≤ ∫ x, normSq (F x) := by
  have ht : Integrable (fun x ↦ topDensity (F x)) :=
    hact.mono' (continuous_topDensity.measurable.comp hF).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]
        exact ym_bps_pointwise_bound (F x))
  exact abs_integral_le_integral_abs.trans
    (integral_mono ht.abs hact (fun x ↦ ym_bps_pointwise_bound (F x)))

theorem ym_bps_action_equality_iff (F : E4 → TwoForm4 r) (hF : Continuous F)
    (hact : Integrable (fun x ↦ normSq (F x))) :
    (∫ x, normSq (F x)) = (∫ x, topDensity (F x)) ↔
      ∀ x, hodge4 (F x) = F x := by
  have ht : Integrable (fun x ↦ topDensity (F x)) :=
    hact.mono' (continuous_topDensity.comp hF).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]
        exact ym_bps_pointwise_bound (F x))
  constructor
  · intro h
    have hd : (∫ x, normSq (F x) - topDensity (F x)) = 0 := by
      rw [integral_sub hact ht, h, sub_self]
    have ha := (integral_eq_zero_iff_of_nonneg
      (fun x ↦ sub_nonneg.mpr ((abs_le.mp (ym_bps_pointwise_bound (F x))).2))
      (hact.sub ht)).mp hd
    have he : (fun x ↦ normSq (F x) - topDensity (F x)) = fun _ ↦ 0 :=
      Measure.eq_of_ae_eq ha ((continuous_normSq.comp hF).sub (continuous_topDensity.comp hF))
        continuous_const
    intro x
    exact (ym_bps_equality_iff (F x)).1.mp (sub_eq_zero.mp (congrFun he x))
  · intro h
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
      (ym_bps_equality_iff (F x)).1.mpr (h x))

/-- The oriented antisymmetric matrix for each color component. -/
def toTwoForm (F : TwoForm4 r) (a : Fin r) : Fin 4 → Fin 4 → ℝ :=
  ![![0, F.1 0 a, F.1 1 a, F.1 2 a],
    ![-F.1 0 a, 0, F.2 2 a, -F.2 1 a],
    ![-F.1 1 a, -F.2 2 a, 0, F.2 0 a],
    ![-F.1 2 a, F.2 1 a, -F.2 0 a, 0]]

theorem toTwoForm_antisymmetric (F : TwoForm4 r) (a : Fin r) (μ ν : Fin 4) :
    toTwoForm F a μ ν = -toTwoForm F a ν μ := by
  fin_cases μ <;> fin_cases ν <;> simp [toTwoForm]

theorem normSq_tensor (F : TwoForm4 r) :
    normSq F = (1 / 2) * ∑ a, ∑ μ, ∑ ν, toTwoForm F a μ ν ^ 2 := by
  unfold normSq inner4
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp [Fin.sum_univ_three, Fin.sum_univ_four, toTwoForm]
  ring

/-- Stress in the unit color pairing, with the four-dimensional trace subtraction. -/
def ymStress (F : TwoForm4 r) (μ ν : Fin 4) : ℝ :=
  ∑ a, ((∑ α, toTwoForm F a μ α * toTwoForm F a ν α) -
    (1 / 4) * (if μ = ν then 1 else 0) * ∑ α, ∑ β, toTwoForm F a α β ^ 2)

theorem ym_stress_trace_zero (F : TwoForm4 r) : ∑ μ, ymStress F μ μ = 0 := by
  unfold ymStress
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  simp [Fin.sum_univ_four, toTwoForm]
  ring

theorem selfDual_ym_stress_zero (F : TwoForm4 r) (h : hodge4 F = F) (μ ν : Fin 4) :
    ymStress F μ ν = 0 := by
  have hb : F.2 = F.1 := congrArg Prod.fst h
  unfold ymStress
  apply Finset.sum_eq_zero
  intro a _
  fin_cases μ <;> fin_cases ν <;> simp [Fin.sum_univ_four, toTwoForm, hb] <;> ring

theorem antiSelfDual_ym_stress_zero (F : TwoForm4 r) (h : hodge4 F = -F) (μ ν : Fin 4) :
    ymStress F μ ν = 0 := by
  have hb : F.2 = -F.1 := congrArg Prod.fst h
  unfold ymStress
  apply Finset.sum_eq_zero
  intro a _
  fin_cases μ <;> fin_cases ν <;> simp [Fin.sum_univ_four, toTwoForm, hb] <;> ring

private def colorDelta (i a : Fin 3) : ℝ := if i = a then 1 else 0

/-- The self-dual 't Hooft symbols in the stated orientation. -/
def thooftEta : TwoForm4 3 := (colorDelta, colorDelta)

theorem thooftEta_selfDual : hodge4 thooftEta = thooftEta := rfl

/-- BPST curvature in the basis with trace pairing one half of the unit color pairing. -/
def bpstField (ρ : ℝ) (x : E4) : TwoForm4 3 :=
  (4 * ρ ^ 2 / (‖x‖ ^ 2 + ρ ^ 2) ^ 2) • thooftEta

theorem bpst_instanton_selfDual (ρ : ℝ) (x : E4) :
    hodge4 (bpstField ρ x) = bpstField ρ x := rfl

theorem bpst_instanton_stress_zero (ρ : ℝ) (x : E4) (μ ν : Fin 4) :
    ymStress (bpstField ρ x) μ ν = 0 :=
  selfDual_ym_stress_zero _ (bpst_instanton_selfDual ρ x) μ ν

/-- The trace-normalized action density, with the same normalization for the charge. -/
def traceActionDensity (F : TwoForm4 r) : ℝ := normSq F / 2

def traceTopDensity (F : TwoForm4 r) : ℝ := topDensity F / 2

theorem bpst_density (ρ : ℝ) (x : E4) :
    traceActionDensity (bpstField ρ x) = 48 * (ρ ^ 4 / (‖x‖ ^ 2 + ρ ^ 2) ^ 4) := by
  unfold traceActionDensity normSq inner4 bpstField thooftEta colorDelta
  simp [Fin.sum_univ_three]
  by_cases h : ‖x‖ ^ 2 + ρ ^ 2 = 0
  · simp [h]
  · field_simp
    ring

private theorem bpst_profile_integral {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun x : E4 ↦ ρ ^ 4 / (‖x‖ ^ 2 + ρ ^ 2) ^ 4) ∧
      (∫ x : E4, ρ ^ 4 / (‖x‖ ^ 2 + ρ ^ 2) ^ 4) = Real.pi ^ 2 / 6 := by
  let f : ℝ → ℝ := fun r ↦ ρ ^ 4 / (r ^ 2 + ρ ^ 2) ^ 4
  have hdim : Module.finrank ℝ E4 = 4 := by simp
  have hprofile (r : ℝ) : r ^ 3 • f r = ρ ^ 4 * r ^ 3 / (r ^ 2 + ρ ^ 2) ^ 4 := by
    simp [f, smul_eq_mul]
    ring
  change Integrable (fun x : E4 ↦ f ‖x‖) ∧ (∫ x : E4, f ‖x‖) = _
  refine ⟨?_, ?_⟩
  · rw [integrable_fun_norm_addHaar volume, hdim]
    simpa using (Omega.bpst_radial_integral hρ).1.congr_fun
      (fun r _ ↦ (hprofile r).symm) measurableSet_Ioi
  · rw [integral_fun_norm_addHaar volume, hdim]
    simp only [Nat.reduceSubDiff]
    rw [show (∫ r in Ioi (0 : ℝ), r ^ 3 • f r) = 1 / 12 by
      simp_rw [hprofile]; exact (Omega.bpst_radial_integral hρ).2]
    have hs : Module.finrank ℝ E4 • (volume : Measure E4).real (Metric.ball 0 1) =
        NullConeGravity.sphere5DMeasure.real univ := by
      rw [nsmul_eq_mul, NullConeGravity.sphere5DMeasure, Measure.toSphere_real_apply_univ]
    rw [hdim] at hs
    rw [← smul_assoc, hs]
    change NullConeGravity.sphere5DMeasure.real univ • (1 / 12 : ℝ) = _
    rw [Measure.real, NullConeGravity.sphere5D_measure_univ, ENNReal.toReal_ofReal (by positivity)]
    simp [smul_eq_mul]
    ring

def bpstAction (ρ : ℝ) : ℝ := ∫ x, traceActionDensity (bpstField ρ x)

def bpstCharge (ρ : ℝ) : ℝ := (∫ x, traceTopDensity (bpstField ρ x)) / (8 * Real.pi ^ 2)

theorem bpst_instanton_finite_action {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun x ↦ traceActionDensity (bpstField ρ x)) := by
  simp_rw [bpst_density]
  exact (bpst_profile_integral hρ).1.const_mul 48

theorem bpst_instanton_exact_action {ρ : ℝ} (hρ : 0 < ρ) :
    bpstAction ρ = 8 * Real.pi ^ 2 := by
  unfold bpstAction
  simp_rw [bpst_density]
  rw [integral_const_mul, (bpst_profile_integral hρ).2]
  ring

theorem bpst_instanton_exact_charge_one {ρ : ℝ} (hρ : 0 < ρ) :
    bpstCharge ρ = 1 := by
  have htop (x : E4) :
      traceTopDensity (bpstField ρ x) = traceActionDensity (bpstField ρ x) := by
    simp [traceTopDensity, traceActionDensity, topDensity, normSq, bpst_instanton_selfDual]
  unfold bpstCharge
  simp_rw [htop]
  change bpstAction ρ / (8 * Real.pi ^ 2) = 1
  rw [bpst_instanton_exact_action hρ, div_self]
  positivity

end D5.S3.Quantum.Gauge.YangMillsBPSSelfDual4D
