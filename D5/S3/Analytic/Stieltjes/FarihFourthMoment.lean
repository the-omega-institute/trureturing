/- GID: D5/S3/Analytic/Stieltjes/FarihFourthMoment
   generality: I
   mirror-B: D5/B/S3/Analytic/Stieltjes/FarihFourthMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.Basic]
   utility: none
   digest: An exact attained resolvent maximum exhibits strict fourth-moment tightening and excludes all two-point laws. -/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! An exact instance of the fourth-moment question in Farih, arXiv:2609.15443v3,
§10.6 and Eqs. (13) and (30). The laws are Borel measures on the real line. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace D5.S3.Analytic.Stieltjes.FarihFourthMoment

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The `k`-th raw moment of a law on the reals. -/
def rawMoment (μ : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, x ^ k ∂μ

/-- A prescribed raw moment includes integrability, since the Bochner integral is total. -/
def HasRawMoment (μ : Measure ℝ) (k : ℕ) (m : ℝ) : Prop :=
  Integrable (fun x : ℝ => x ^ k) μ ∧ rawMoment μ k = m

structure FirstThreeMoments (μ : Measure ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  nonnegative : ∀ᵐ x ∂μ, 0 ≤ x
  first : HasRawMoment μ 1 1
  second : HasRawMoment μ 2 (5 / 3)
  third : HasRawMoment μ 3 3

def FirstFourMoments (μ : Measure ℝ) : Prop :=
  FirstThreeMoments μ ∧ HasRawMoment μ 4 (17 / 3)

/-- Efficiency at α = 1. -/
def efficiency (x : ℝ) : ℝ := (1 + x)⁻¹

def meanEfficiency (μ : Measure ℝ) : ℝ := ∫ x, efficiency x ∂μ

private def quartic (x : ℝ) : ℝ :=
  (x ^ 4 - 7 * x ^ 3 + 20 * x ^ 2 - 32 * x + 36) / 36

private theorem quartic_gap {x : ℝ} (hx : 0 ≤ x) :
    quartic x - efficiency x = x * (x - 1) ^ 2 * (x - 2) ^ 2 / (36 * (1 + x)) := by
  have hden : 1 + x ≠ 0 := by positivity
  unfold quartic efficiency
  field_simp
  ring

private theorem efficiency_le_quartic {x : ℝ} (hx : 0 ≤ x) : efficiency x ≤ quartic x := by
  apply sub_nonneg.mp
  rw [quartic_gap hx]
  positivity

private theorem integrable_efficiency {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) : Integrable efficiency μ := by
  have hm : Measurable (fun x : ℝ => 1 + x) := measurable_const.add measurable_id
  refine (integrable_const (1 : ℝ)).mono' hm.inv.aestronglyMeasurable ?_
  filter_upwards [hμ] with x hx
  have hden : 0 < 1 + x := by positivity
  rw [efficiency, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hden.le)]
  exact (inv_le_one₀ hden).2 (by linarith)

private theorem integral_quartic {μ : Measure ℝ} (h : FirstFourMoments μ) :
    Integrable quartic μ ∧ (∫ x, quartic x ∂μ) = 11 / 18 := by
  let : IsProbabilityMeasure μ := h.1.probability
  have h1 : Integrable (fun x : ℝ => x) μ := by
    simpa only [pow_one] using h.1.first.1
  have h43 : Integrable (fun x : ℝ => x ^ 4 - 7 * x ^ 3) μ :=
    h.2.1.sub (h.1.third.1.const_mul 7)
  have h432 : Integrable (fun x : ℝ => x ^ 4 - 7 * x ^ 3 + 20 * x ^ 2) μ :=
    h43.add (h.1.second.1.const_mul 20)
  have h4321 : Integrable (fun x : ℝ => x ^ 4 - 7 * x ^ 3 + 20 * x ^ 2 - 32 * x) μ :=
    h432.sub (h1.const_mul 32)
  have h36 : Integrable (fun _ : ℝ => (36 : ℝ)) μ := integrable_const 36
  refine ⟨(h4321.add h36).div_const 36, ?_⟩
  unfold quartic
  rw [integral_div, integral_add h4321 h36, integral_sub h432 (h1.const_mul 32),
    integral_add h43 (h.1.second.1.const_mul 20), integral_sub h.2.1 (h.1.third.1.const_mul 7)]
  simp only [integral_const_mul, integral_const, smul_eq_mul, Measure.real, measure_univ,
    ENNReal.toReal_one, one_mul]
  have m1 : (∫ x : ℝ, x ∂μ) = 1 := by
    simpa only [rawMoment, pow_one] using h.1.first.2
  rw [integral_const_mul 32 (fun x : ℝ => x), m1]
  change (rawMoment μ 4 - 7 * rawMoment μ 3 + 20 * rawMoment μ 2 - 32 * 1 + 36) / 36 = _
  rw [h.2.2, h.1.third.2, h.1.second.2]
  norm_num

/-- The upper bound holds for every real probability measure satisfying the moment constraints. -/
private theorem meanEfficiency_le {μ : Measure ℝ} (h : FirstFourMoments μ) :
    meanEfficiency μ ≤ 11 / 18 := by
  let : IsProbabilityMeasure μ := h.1.probability
  have hQ := integral_quartic h
  rw [← hQ.2]
  exact integral_mono_ae (integrable_efficiency h.1.nonnegative) hQ.1
    (h.1.nonnegative.mono fun _ hx => efficiency_le_quartic hx)

private def threeAtoms (a b c p q r : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac a + ENNReal.ofReal q • Measure.dirac b +
    ENNReal.ofReal r • Measure.dirac c

private theorem integrable_atom (x w : ℝ) (f : ℝ → ℝ) :
    Integrable f (ENNReal.ofReal w • Measure.dirac x) :=
  (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private theorem integrable_threeAtoms (a b c p q r : ℝ) (f : ℝ → ℝ) :
    Integrable f (threeAtoms a b c p q r) :=
  ((integrable_atom a p f).add_measure (integrable_atom b q f)).add_measure
    (integrable_atom c r f)

private theorem integral_threeAtoms {a b c p q r : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (f : ℝ → ℝ) :
    (∫ x, f x ∂threeAtoms a b c p q r) = p * f a + q * f b + r * f c := by
  unfold threeAtoms
  rw [integral_add_measure ((integrable_atom a p f).add_measure (integrable_atom b q f))
    (integrable_atom c r f), integral_add_measure (integrable_atom a p f) (integrable_atom b q f)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal hr, smul_eq_mul]

private theorem threeAtoms_probability {a b c p q r : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : p + q + r = 1) :
    IsProbabilityMeasure (threeAtoms a b c p q r) := by
  constructor
  simp only [threeAtoms, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp hq, ← ENNReal.ofReal_add (add_nonneg hp hq) hr, hs]
  simp

private theorem threeAtoms_nonnegative {a b c p q r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : ∀ᵐ x ∂threeAtoms a b c p q r, 0 ≤ x := by
  rw [threeAtoms, ae_add_measure_iff, ae_add_measure_iff]
  have atAtom (z : ℝ) (hz : 0 ≤ z) : ∀ᵐ x ∂Measure.dirac z, 0 ≤ x := by
    simpa [ae_dirac_eq] using hz
  exact ⟨⟨Measure.ae_smul_measure (atAtom a ha) _, Measure.ae_smul_measure (atAtom b hb) _⟩,
    Measure.ae_smul_measure (atAtom c hc) _⟩

/-- The uniform law on the three real numbers 0, 1, and 2. -/
def uniform012 : Measure ℝ :=
  ENNReal.ofReal (1 / 3) • Measure.dirac 0 + ENNReal.ofReal (1 / 3) • Measure.dirac 1 +
    ENNReal.ofReal (1 / 3) • Measure.dirac 2

private theorem uniform012_feasible : FirstFourMoments uniform012 := by
  change FirstFourMoments (threeAtoms 0 1 2 (1 / 3) (1 / 3) (1 / 3))
  refine ⟨⟨threeAtoms_probability (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    threeAtoms_nonnegative (by norm_num) (by norm_num) (by norm_num), ?_, ?_, ?_⟩, ?_⟩
  all_goals
    refine ⟨integrable_threeAtoms _ _ _ _ _ _ _, ?_⟩
    rw [rawMoment, integral_threeAtoms (by norm_num) (by norm_num) (by norm_num)]
    norm_num

private theorem uniform012_attains : meanEfficiency uniform012 = 11 / 18 := by
  change (∫ x, efficiency x ∂threeAtoms 0 1 2 (1 / 3) (1 / 3) (1 / 3)) = _
  rw [integral_threeAtoms (by norm_num) (by norm_num) (by norm_num)]
  norm_num [efficiency, inv_eq_one_div]

/-- Any law concentrated almost everywhere on two real points satisfies the quadratic
recurrence for its raw moments. The first three moments fix both recurrence coefficients. -/
private theorem two_point_fourth_moment {μ : Measure ℝ} (h : FirstThreeMoments μ) {a b : ℝ}
    (hsupport : ∀ᵐ x ∂μ, x = a ∨ x = b) : HasRawMoment μ 4 (49 / 9) := by
  let : IsProbabilityMeasure μ := h.probability
  have h0 : HasRawMoment μ 0 1 := by
    simp [HasRawMoment, rawMoment, Measure.real]
  have recurrence (n : ℕ) (hn : Integrable (fun x : ℝ => x ^ n) μ)
      (hs : Integrable (fun x : ℝ => x ^ (n + 1)) μ) :
      HasRawMoment μ (n + 2) ((a + b) * rawMoment μ (n + 1) - (a * b) * rawMoment μ n) := by
    have hrec : (fun x : ℝ => x ^ (n + 2)) =ᵐ[μ]
        fun x => (a + b) * x ^ (n + 1) - (a * b) * x ^ n := by
      filter_upwards [hsupport] with x hx
      rcases hx with rfl | rfl <;> simp only [pow_succ] <;> ring
    refine ⟨((hs.const_mul (a + b)).sub (hn.const_mul (a * b))).congr hrec.symm, ?_⟩
    unfold rawMoment
    calc
      (∫ x : ℝ, x ^ (n + 2) ∂μ) =
          ∫ x : ℝ, (a + b) * x ^ (n + 1) - (a * b) * x ^ n ∂μ := integral_congr_ae hrec
      _ = _ := by
        rw [integral_sub (hs.const_mul (a + b)) (hn.const_mul (a * b)), integral_const_mul,
          integral_const_mul]
  have h2eq : (5 : ℝ) / 3 = (a + b) * 1 - (a * b) * 1 := by
    simpa only [h0.2, h.first.2, h.second.2] using (recurrence 0 h0.1 h.first.1).2
  have h3eq : (3 : ℝ) = (a + b) * (5 / 3) - (a * b) * 1 := by
    simpa only [h.first.2, h.second.2, h.third.2] using (recurrence 1 h.first.1 h.second.1).2
  have hsum : a + b = 2 := by linarith
  have hprod : a * b = 1 / 3 := by linarith
  have h4eq := recurrence 2 h.second.1 h.third.1
  refine ⟨h4eq.1, ?_⟩
  calc
    rawMoment μ 4 = (a + b) * rawMoment μ 3 - (a * b) * rawMoment μ 2 := h4eq.2
    _ = 49 / 9 := by
      rw [hsum, hprod, h.third.2, h.second.2]
      norm_num

private theorem no_two_point_feasible {μ : Measure ℝ} (h : FirstFourMoments μ) (a b : ℝ) :
    ¬(∀ᵐ x ∂μ, x = a ∨ x = b) := by
  intro hsupport
  have heq := (two_point_fourth_moment h.1 hsupport).2
  rw [h.2.2] at heq
  norm_num at heq

/-- A law satisfying the first three moment constraints with larger mean efficiency. -/
def threeMomentWitness : Measure ℝ :=
  ENNReal.ofReal (10 / 27) • Measure.dirac 0 +
    ENNReal.ofReal (16 / 27) • Measure.dirac (3 / 2) +
    ENNReal.ofReal (1 / 27) • Measure.dirac 3

private theorem threeMomentWitness_feasible : FirstThreeMoments threeMomentWitness := by
  change FirstThreeMoments (threeAtoms 0 (3 / 2) 3 (10 / 27) (16 / 27) (1 / 27))
  refine ⟨threeAtoms_probability (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    threeAtoms_nonnegative (by norm_num) (by norm_num) (by norm_num), ?_, ?_, ?_⟩
  all_goals
    refine ⟨integrable_threeAtoms _ _ _ _ _ _ _, ?_⟩
    rw [rawMoment, integral_threeAtoms (by norm_num) (by norm_num) (by norm_num)]
    norm_num

private theorem threeMomentWitness_value : meanEfficiency threeMomentWitness = 37 / 60 := by
  change (∫ x, efficiency x ∂threeAtoms 0 (3 / 2) 3 (10 / 27) (16 / 27) (1 / 27)) = _
  rw [integral_threeAtoms (by norm_num) (by norm_num) (by norm_num)]
  norm_num [efficiency, inv_eq_one_div]

/-- The exact four-moment answer and the strict comparison after dropping the fourth moment. -/
theorem result :
    FirstFourMoments uniform012 ∧ meanEfficiency uniform012 = 11 / 18 ∧
    (∀ μ : Measure ℝ, FirstFourMoments μ → meanEfficiency μ ≤ 11 / 18) ∧
    (∀ μ : Measure ℝ, FirstFourMoments μ → ∀ a b : ℝ, ¬(∀ᵐ x ∂μ, x = a ∨ x = b)) ∧
    FirstThreeMoments threeMomentWitness ∧ meanEfficiency threeMomentWitness = 37 / 60 ∧
    (∀ ν : Measure ℝ, FirstFourMoments ν → meanEfficiency ν < meanEfficiency threeMomentWitness) := by
  refine ⟨uniform012_feasible, uniform012_attains, fun _ h => meanEfficiency_le h,
    fun _ h => no_two_point_feasible h, threeMomentWitness_feasible, threeMomentWitness_value, ?_⟩
  intro ν hν
  rw [threeMomentWitness_value]
  exact (meanEfficiency_le hν).trans_lt (by norm_num)

end

end D5.S3.Analytic.Stieltjes.FarihFourthMoment
