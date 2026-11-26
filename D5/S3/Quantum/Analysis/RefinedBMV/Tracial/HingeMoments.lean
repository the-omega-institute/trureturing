/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/HingeMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/Tracial/HingeMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive quadratic forms from the four-mark binomial hinge moments. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace RefinedBMV.Tracial

noncomputable section

private def leftNumerator (n : ℕ) : ℝ :=
  96 - (n + 3 : ℝ) * (n + 4) * (n + 5) / 4 ^ n

private def middleNumerator (n : ℕ) : ℝ :=
  24 - (n + 4 : ℝ) * (n + 5) / 2 ^ n

private def rightNumerator (n : ℕ) : ℝ :=
  16 - 3 * (n + 5 : ℝ) * (3 / 4 : ℝ) ^ n

/-- A common positive rescaling of the moments of the hinge corrections
at one, two, and three marks. -/
private def scaledHingeMoments (n : ℕ) : ℝ × ℝ × ℝ :=
  (leftNumerator n / (4 * (n + 3 : ℝ)), middleNumerator n,
    3 * (n + 4 : ℝ) * rightNumerator n / 4)

private theorem left_tail (n : ℕ) (hn : 6 ≤ n) :
    (n + 3 : ℝ) * (n + 4) * (n + 5) ≤ 4 ^ n := by
  refine Nat.le_induction ?_ ?_ n hn
  · norm_num
  · intro k _ ih
    have h : (k + 6 : ℝ) ≤ 4 * (k + 3 : ℝ) := by
      have hk : 0 ≤ (k : ℝ) := by positivity
      linarith
    simp only [Nat.cast_succ, pow_succ]
    calc
      _ = ((k + 4 : ℝ) * (k + 5)) * (k + 6) := by ring
      _ ≤ ((k + 4 : ℝ) * (k + 5)) * (4 * (k + 3)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((k + 3 : ℝ) * (k + 4) * (k + 5)) * 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ih (by norm_num)

private theorem middle_tail (n : ℕ) :
    (n + 4 : ℝ) * (n + 5) ≤ 24 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h : (k + 6 : ℝ) ≤ 2 * (k + 4 : ℝ) := by
      have hk : 0 ≤ (k : ℝ) := by positivity
      linarith
    simp only [Nat.cast_succ, pow_succ]
    calc
      _ = (k + 5 : ℝ) * (k + 6) := by ring
      _ ≤ (k + 5 : ℝ) * (2 * (k + 4)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((k + 4 : ℝ) * (k + 5)) * 2 := by ring
      _ ≤ (24 * 2 ^ k) * 2 := mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = _ := by ring

private theorem right_tail (n : ℕ) (hn : 6 ≤ n) :
    3 * (n + 5 : ℝ) * (3 / 4 : ℝ) ^ n ≤ 6 := by
  refine Nat.le_induction ?_ ?_ n hn
  · norm_num
  · intro k _ ih
    have h : (k + 6 : ℝ) * (3 / 4) ≤ k + 5 := by
      have hk : 0 ≤ (k : ℝ) := by positivity
      linarith
    simp only [Nat.cast_succ, pow_succ]
    calc
      _ = (3 * (3 / 4 : ℝ) ^ k) * ((k + 6 : ℝ) * (3 / 4)) := by ring
      _ ≤ (3 * (3 / 4 : ℝ) ^ k) * (k + 5) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 * (k + 5 : ℝ) * (3 / 4 : ℝ) ^ k := by ring
      _ ≤ 6 := ih

private theorem scaledHingeMoments_margin (n : ℕ) :
    0 < (scaledHingeMoments n).1 ∧
    (scaledHingeMoments n).2.1 ^ 2 ≤
      (81 / 25 : ℝ) * (scaledHingeMoments n).1 * (scaledHingeMoments n).2.2 := by
  by_cases hn : n < 6
  · interval_cases n <;> norm_num [scaledHingeMoments, leftNumerator,
      middleNumerator, rightNumerator]
  have hn' : 6 ≤ n := Nat.le_of_not_gt hn
  have hleft : 95 ≤ leftNumerator n := by
    unfold leftNumerator
    have h := (div_le_one (by positivity : (0 : ℝ) < 4 ^ n)).mpr (left_tail n hn')
    linarith
  have hright : 10 ≤ rightNumerator n := by
    unfold rightNumerator
    linarith only [right_tail n hn']
  have hm0 : 0 ≤ middleNumerator n := by
    unfold middleNumerator
    exact sub_nonneg.mpr ((div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr (middle_tail n))
  have hm1 : middleNumerator n ≤ 24 := by
    unfold middleNumerator
    exact sub_le_self _ (by positivity)
  let a : ℝ := 4 * (n + 3 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have h₁ : 95 / a ≤ leftNumerator n / a := div_le_div_of_nonneg_right hleft ha.le
  have h₂ : (30 * (n + 3 : ℝ)) / 4 ≤ 3 * (n + 4 : ℝ) * rightNumerator n / 4 := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).mpr
    calc
      _ ≤ (3 * (n + 4 : ℝ)) * 10 := by ring_nf; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hright (by positivity)
  have hprod := mul_le_mul h₁ h₂ (by positivity : 0 ≤ 30 * (n + 3 : ℝ) / 4)
    (div_nonneg (by linarith only [hleft]) ha.le)
  have hconst : 95 / a * (30 * (n + 3 : ℝ) / 4) = (1425 / 8 : ℝ) := by
    dsimp [a]
    have hn3 : (n + 3 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hconst] at hprod
  constructor
  · exact div_pos (by linarith only [hleft]) ha
  · change middleNumerator n ^ 2 ≤ (81 / 25 : ℝ) *
      (leftNumerator n / a) * (3 * (n + 4 : ℝ) * rightNumerator n / 4)
    nlinarith only [pow_le_pow_left₀ hm0 hm1 2, hprod]

/-- The moment quadratic form has a uniform relative diagonal margin,
with no restriction on the signs of the two spectral values. -/
private theorem scaledHingeMoments_quadratic_lower (n : ℕ) (x y : ℝ) :
    let (a, b, c) := scaledHingeMoments n
    (a * x ^ 2 + c * y ^ 2) / 10 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  rcases he : scaledHingeMoments n with ⟨a, b, c⟩
  obtain ⟨ha, habc⟩ := scaledHingeMoments_margin n
  simp only [he] at ha habc
  dsimp
  have hdisc : 0 ≤ 4 * (9 / 10 * a) * (9 / 10 * c) - b ^ 2 := by
    linarith only [habc]
  have hs : 0 ≤ (2 * (9 / 10 * a) * x + b * y) ^ 2 +
      (4 * (9 / 10 * a) * (9 / 10 * c) - b ^ 2) * y ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hdisc (sq_nonneg _))
  have heq : (2 * (9 / 10 * a) * x + b * y) ^ 2 +
      (4 * (9 / 10 * a) * (9 / 10 * c) - b ^ 2) * y ^ 2 =
      4 * (9 / 10 * a) * (9 / 10 * a * x ^ 2 + b * x * y + 9 / 10 * c * y ^ 2) := by
    ring
  rw [heq] at hs
  have hpos : 0 < 4 * (9 / 10 * a) := by positivity
  have hq := nonneg_of_mul_nonneg_right hs hpos
  linarith only [hq]


open intervalIntegral

/-- The expected hinge corrections for four independent uniform marks,
relative to the count obtained from four equally spaced marks. -/
private def fourMarkHingeDefect (s x y : ℝ) : ℝ :=
  ((1 - s) ^ 4 - 4 * max (1 / 4 - s) 0) * x ^ 2 +
    (4 * s ^ 3 - 2 * s ^ 4 - 4 * s + 2 - 4 * max (1 / 2 - s) 0) * x * y +
    (s ^ 4 - 4 * s + 3 - 4 * max (3 / 4 - s) 0) * y ^ 2

private theorem integral_weighted_leftHinge (n : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∫ s in (0 : ℝ)..1, s ^ n * max (a - s) 0) =
      a ^ (n + 2) / ((n + 1 : ℝ) * (n + 2)) := by
  have hc : Continuous (fun s : ℝ ↦ s ^ n * max (a - s) 0) := by fun_prop
  have h₁ : (∫ s in (0 : ℝ)..a, s ^ n * max (a - s) 0) =
      ∫ s in (0 : ℝ)..a, a * s ^ n - s ^ (n + 1) := by
    apply integral_congr
    intro s hs
    rw [Set.uIcc_of_le ha] at hs
    dsimp only
    rw [max_eq_left (sub_nonneg.mpr hs.2), pow_succ]
    ring
  have h₂ : (∫ s in a..1, s ^ n * max (a - s) 0) = 0 := by
    rw [← integral_zero (a := a) (b := 1)]
    apply integral_congr
    intro s hs
    rw [Set.uIcc_of_le ha'] at hs
    simp [max_eq_right (sub_nonpos.mpr hs.1)]
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a 1),
    h₁, h₂, add_zero,
    integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 a)
      (Continuous.intervalIntegrable (by fun_prop) 0 a),
    integral_const_mul, integral_pow, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one, pow_succ]
  have hd₁ : (n + 1 : ℝ) ≠ 0 := by positivity
  have hd₂ : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem integral_weighted_quartic (n : ℕ) (c : Fin 5 → ℝ) :
    (∫ s in (0 : ℝ)..1, s ^ n * ∑ i, c i * s ^ (i : ℕ)) =
      ∑ i, c i / ((n : ℝ) + (i : ℕ) + 1) := by
  simp only [Finset.mul_sum]
  rw [integral_finsetSum (fun _ _ ↦ Continuous.intervalIntegrable (by fun_prop) 0 1)]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun s : ℝ ↦ s ^ n * (c i * s ^ (i : ℕ))) =
      fun s ↦ c i * s ^ (n + (i : ℕ)) := by
    funext s
    rw [pow_add]
    ring
  simp only [he, integral_const_mul, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _),
    sub_zero, Nat.cast_add, div_eq_mul_inv, one_mul]

private theorem integral_hinge_component (n : ℕ) (c : Fin 5 → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∫ s in (0 : ℝ)..1, s ^ n * ((∑ i, c i * s ^ (i : ℕ)) - 4 * max (a - s) 0)) =
      (∑ i, c i / ((n : ℝ) + (i : ℕ) + 1)) -
        4 * (a ^ (n + 2) / ((n + 1 : ℝ) * (n + 2))) := by
  have h₁ : Continuous (fun s : ℝ ↦ s ^ n * ∑ i, c i * s ^ (i : ℕ)) := by fun_prop
  have h₂ : Continuous (fun s : ℝ ↦ s ^ n * max (a - s) 0) := by fun_prop
  have h : (fun s : ℝ ↦ s ^ n * ((∑ i, c i * s ^ (i : ℕ)) - 4 * max (a - s) 0)) =
      fun s ↦ s ^ n * (∑ i, c i * s ^ (i : ℕ)) - 4 * (s ^ n * max (a - s) 0) := by
    funext s
    ring
  rw [h, integral_sub (h₁.intervalIntegrable 0 1) ((h₂.const_mul 4).intervalIntegrable 0 1),
    integral_const_mul, integral_weighted_quartic, integral_weighted_leftHinge n ha ha']

private theorem hinge_components (n : ℕ) :
    let d : ℝ := (n + 1 : ℝ) * (n + 2) * (n + 4) * (n + 5)
    (∫ s in (0 : ℝ)..1, s ^ n * ((1 - s) ^ 4 - 4 * max (1 / 4 - s) 0)) =
      (scaledHingeMoments n).1 / d ∧
    (∫ s in (0 : ℝ)..1,
      s ^ n * (4 * s ^ 3 - 2 * s ^ 4 - 4 * s + 2 - 4 * max (1 / 2 - s) 0)) =
      (scaledHingeMoments n).2.1 / d ∧
    (∫ s in (0 : ℝ)..1, s ^ n * (s ^ 4 - 4 * s + 3 - 4 * max (3 / 4 - s) 0)) =
      (scaledHingeMoments n).2.2 / d := by
  dsimp only [scaledHingeMoments, leftNumerator, middleNumerator, rightNumerator]
  have h₁ : (fun s : ℝ ↦ (1 - s) ^ 4) =
      fun s ↦ ∑ i : Fin 5, (![1, -4, 6, -4, 1] : Fin 5 → ℝ) i * s ^ (i : ℕ) := by
    funext s
    simp [Fin.sum_univ_succ]
    ring
  have h₂ : (fun s : ℝ ↦ 4 * s ^ 3 - 2 * s ^ 4 - 4 * s + 2) =
      fun s ↦ ∑ i : Fin 5, (![2, -4, 0, 4, -2] : Fin 5 → ℝ) i * s ^ (i : ℕ) := by
    funext s
    simp [Fin.sum_univ_succ]
    ring
  have h₃ : (fun s : ℝ ↦ s ^ 4 - 4 * s + 3) =
      fun s ↦ ∑ i : Fin 5, (![3, -4, 0, 0, 1] : Fin 5 → ℝ) i * s ^ (i : ℕ) := by
    funext s
    simp [Fin.sum_univ_succ]
    ring
  have hd₁ : (n + 1 : ℝ) ≠ 0 := by positivity
  have hd₂ : (n + 2 : ℝ) ≠ 0 := by positivity
  have hd₃ : (n + 3 : ℝ) ≠ 0 := by positivity
  have hd₄ : (n + 4 : ℝ) ≠ 0 := by positivity
  have hd₅ : (n + 5 : ℝ) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [congrFun h₁]
    rw [integral_hinge_component n _ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1)]
    simp [Fin.sum_univ_succ, pow_add]
    field_simp
    ring
  · simp_rw [congrFun h₂]
    rw [integral_hinge_component n _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    simp [Fin.sum_univ_succ, pow_add]
    field_simp
    ring
  · simp_rw [congrFun h₃]
    rw [integral_hinge_component n _ (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) ≤ 1)]
    simp [Fin.sum_univ_succ, pow_add]
    field_simp
    ring

private theorem integral_pow_mul_fourMarkHingeDefect (n : ℕ) (x y : ℝ) :
    (∫ s in (0 : ℝ)..1, s ^ n * fourMarkHingeDefect s x y) =
      ((scaledHingeMoments n).1 * x ^ 2 + (scaledHingeMoments n).2.1 * x * y +
        (scaledHingeMoments n).2.2 * y ^ 2) /
        ((n + 1 : ℝ) * (n + 2) * (n + 4) * (n + 5)) := by
  obtain ⟨h₁, h₂, h₃⟩ := hinge_components n
  unfold fourMarkHingeDefect
  simp only [mul_add, ← mul_assoc]
  have hh₁ : Continuous (fun s : ℝ ↦ s ^ n * ((1 - s) ^ 4 - 4 * max (1 / 4 - s) 0)) := by
    fun_prop
  have hh₂ : Continuous (fun s : ℝ ↦
    s ^ n * (4 * s ^ 3 - 2 * s ^ 4 - 4 * s + 2 - 4 * max (1 / 2 - s) 0)) := by fun_prop
  have hh₃ : Continuous (fun s : ℝ ↦
    s ^ n * (s ^ 4 - 4 * s + 3 - 4 * max (3 / 4 - s) 0)) := by fun_prop
  have hi₁ := (hh₁.mul_const (x ^ 2)).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have hi₂ := ((hh₂.mul_const x).mul_const y).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  have hi₃ := (hh₃.mul_const (y ^ 2)).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [integral_add (hi₁.add hi₂) hi₃, integral_add hi₁ hi₂]
  simp only [integral_mul_const, h₁, h₂, h₃]
  ring

/-- Every power-weighted four-mark hinge defect is a nonnegative quadratic
form on two real spectral values of arbitrary signs. -/
private theorem integral_pow_mul_fourMarkHingeDefect_nonneg (n : ℕ) (x y : ℝ) :
    0 ≤ ∫ s in (0 : ℝ)..1, s ^ n * fourMarkHingeDefect s x y := by
  rw [integral_pow_mul_fourMarkHingeDefect]
  let d : ℝ := (n + 1 : ℝ) * (n + 2) * (n + 4) * (n + 5)
  have hd : 0 < d := by dsimp [d]; positivity
  have hl := scaledHingeMoments_quadratic_lower n x y
  have hpos : 0 ≤ (scaledHingeMoments n).1 ∧ 0 ≤ (scaledHingeMoments n).2.2 := by
    obtain ⟨ha, h⟩ := scaledHingeMoments_margin n
    have hh : 0 ≤ (81 / 25 : ℝ) * (scaledHingeMoments n).1 *
        (scaledHingeMoments n).2.2 := (sq_nonneg _).trans h
    exact ⟨ha.le, nonneg_of_mul_nonneg_right hh (by positivity)⟩
  have hdiag : 0 ≤ ((scaledHingeMoments n).1 * x ^ 2 + (scaledHingeMoments n).2.2 * y ^ 2) / 10 :=
    div_nonneg (add_nonneg (mul_nonneg hpos.1 (sq_nonneg _)) (mul_nonneg hpos.2 (sq_nonneg _)))
      (by norm_num)
  exact div_nonneg (hdiag.trans hl) hd.le


open Filter Topology in
/-- After orienting a spectral pair by its ordered drift eigenvalues, the
exponentially weighted hinge defect retains the zero-order spectral margin. -/
private theorem integral_exp_mul_fourMarkHingeDefect_lower {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    (x ^ 2 + y ^ 2) / 40 ≤
      ∫ s in (0 : ℝ)..1, Real.exp (r * s) * fourMarkHingeDefect s x y := by
  let f : ℕ → ℝ → ℝ := fun n s ↦
    (r * s) ^ n / (n.factorial : ℝ) * fourMarkHingeDefect s x y
  have hf (n : ℕ) : Continuous (f n) := by
    unfold f fourMarkHingeDefect
    fun_prop
  have hφ : Continuous fun s ↦ fourMarkHingeDefect s x y := by
    unfold fourMarkHingeDefect
    fun_prop
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image hφ.norm.continuousOn
  have hbound (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) :
      ‖fourMarkHingeDefect s x y‖ ≤ C := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hC ⟨s, hs, rfl⟩
  have hsum := ((NormedSpace.expSeries_div_hasSum_exp r).summable.mul_right C)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) :
      ‖f n s‖ ≤ r ^ n / (n.factorial : ℝ) * C := by
    have hφs := hbound s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hrs : 0 ≤ r * s := mul_nonneg hr hs.1
    have hr1 : r * s ≤ r := mul_le_of_le_one_right hr hs.2
    simp only [f, norm_mul, norm_div, norm_pow, Real.norm_of_nonneg hrs,
      Real.norm_of_nonneg (Nat.cast_nonneg n.factorial)]
    exact mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hrs hr1 n)
      (Nat.cast_nonneg n.factorial)) hφs (norm_nonneg _) (by positivity)
  have hunif := tendstoUniformlyOn_tsum_nat hsum hb
  have ht (s : ℝ) : (∑' n, f n s) = Real.exp (r * s) * fourMarkHingeDefect s x y := by
    have hh := (NormedSpace.expSeries_div_hasSum_exp (r * s)).mul_right (fourMarkHingeDefect s x y)
    rw [← Real.exp_eq_exp_ℝ] at hh
    exact hh.tsum_eq
  simp_rw [ht] at hunif
  have hcont (N : ℕ) : Continuous (fun s ↦ ∑ n ∈ Finset.range N, f n s) :=
    continuous_finsetSum _ fun n _ ↦ hf n
  have hlim := hunif.tendsto_intervalIntegral_of_continuousOn (μ := MeasureTheory.volume)
    (.of_forall fun N ↦ (hcont N).continuousOn)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [integral_finsetSum (fun n _ ↦ (hf n).intervalIntegrable 0 1)]
  have hi (n : ℕ) : (∫ s in (0 : ℝ)..1, f n s) =
      (r ^ n / (n.factorial : ℝ)) *
        (∫ s in (0 : ℝ)..1, s ^ n * fourMarkHingeDefect s x y) := by
    rw [← integral_const_mul]
    apply integral_congr
    intro s _
    dsimp only [f]
    rw [mul_pow]
    ring
  have hi0 : (x ^ 2 + y ^ 2) / 40 ≤ ∫ s in (0 : ℝ)..1, f 0 s := by
    rw [hi, integral_pow_mul_fourMarkHingeDefect]
    norm_num [scaledHingeMoments, leftNumerator, middleNumerator, rightNumerator]
    nlinarith only [sq_nonneg (x + y)]
  refine hi0.trans (Finset.single_le_sum (f := fun n ↦ ∫ s in (0 : ℝ)..1, f n s)
    ?_ (Finset.mem_range.mpr hN))
  intro n _
  rw [hi]
  exact mul_nonneg (by positivity) (integral_pow_mul_fourMarkHingeDefect_nonneg n x y)


/-- The quartic product averaged over the two possible arc counts of
a uniformly rotated four-point grid. -/
def fourMarkPeriodicMean (s x y : ℝ) : ℝ :=
  if s ≤ 1 / 4 then (1 - 4 * s) * x ^ 4 + (4 * s) * x ^ 3 * y
  else if s ≤ 1 / 2 then (2 - 4 * s) * x ^ 3 * y + (4 * s - 1) * x ^ 2 * y ^ 2
  else if s ≤ 3 / 4 then (3 - 4 * s) * x ^ 2 * y ^ 2 + (4 * s - 2) * x * y ^ 3
  else (4 - 4 * s) * x * y ^ 3 + (4 * s - 3) * y ^ 4

private theorem fourMark_defect_eq (s x y : ℝ) :
    ((1 - s) * x + s * y) ^ 4 - fourMarkPeriodicMean s x y =
      (x - y) ^ 2 * fourMarkHingeDefect s x y := by
  unfold fourMarkPeriodicMean fourMarkHingeDefect
  split_ifs with h₁ h₂ h₃
  · rw [max_eq_left (by linarith : 0 ≤ (1 / 4 : ℝ) - s),
      max_eq_left (by linarith : 0 ≤ (1 / 2 : ℝ) - s),
      max_eq_left (by linarith : 0 ≤ (3 / 4 : ℝ) - s)]
    ring
  · rw [max_eq_right (by linarith : (1 / 4 : ℝ) - s ≤ 0),
      max_eq_left (by linarith : 0 ≤ (1 / 2 : ℝ) - s),
      max_eq_left (by linarith : 0 ≤ (3 / 4 : ℝ) - s)]
    ring
  · rw [max_eq_right (by linarith : (1 / 4 : ℝ) - s ≤ 0),
      max_eq_right (by linarith : (1 / 2 : ℝ) - s ≤ 0),
      max_eq_left (by linarith : 0 ≤ (3 / 4 : ℝ) - s)]
    ring
  · rw [max_eq_right (by linarith : (1 / 4 : ℝ) - s ≤ 0),
      max_eq_right (by linarith : (1 / 2 : ℝ) - s ≤ 0),
      max_eq_right (by linarith : (3 / 4 : ℝ) - s ≤ 0)]
    ring

/-- The two affine pieces at each arc-count transition agree. -/
theorem continuous_fourMarkPeriodicMean (x y : ℝ) :
    Continuous fun s ↦ fourMarkPeriodicMean s x y := by
  have h (s : ℝ) : fourMarkPeriodicMean s x y =
      ((1 - s) * x + s * y) ^ 4 - (x - y) ^ 2 * fourMarkHingeDefect s x y := by
    linarith only [fourMark_defect_eq s x y]
  simp_rw [h, fourMarkHingeDefect]
  fun_prop

/-- The binomial arc-count mean dominates the periodic arc-count mean
after integration with an exponential weight, including signed inputs. -/
theorem integral_fourMarkSignedDefect_lower {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    (x - y) ^ 2 * ((x ^ 2 + y ^ 2) / 40) ≤
      ∫ s in (0 : ℝ)..1, Real.exp (r * s) *
        (((1 - s) * x + s * y) ^ 4 - fourMarkPeriodicMean s x y) := by
  simp_rw [fourMark_defect_eq, mul_left_comm (Real.exp _) ((x - y) ^ 2)]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_exp_mul_fourMarkHingeDefect_lower hr x y) (sq_nonneg _)

end

end RefinedBMV.Tracial
