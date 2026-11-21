/- GID: D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/ThreeAtomZeroFilter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three positive atoms remove conjugate modes while preserving a protected mode. -/

import D5.S3.Analytic.Asymptotics.PositiveSpectralKernel
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A choice of spacing avoids the two possible exponential collisions. -/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace PositiveSpectralKernel

private def threeAtomMiddle (r γ a : ℝ) : ℝ :=
  -(2 * Real.cos (γ * a)) * Real.exp (-(r * a))

private def threeAtomLast (r a : ℝ) : ℝ :=
  Real.exp (-2 * r * a)

private def threeAtomTotal (r γ a : ℝ) : ℝ :=
  1 + threeAtomMiddle r γ a + threeAtomLast r a

/-- The normalized weights at `0`, `a`, and `2 * a` are strictly positive when
`Real.cos (γ * a) < 0`. -/
def threeAtom (r γ a : ℝ) : Measure ℝ :=
  let d := threeAtomTotal r γ a
  ENNReal.ofReal (1 / d) • Measure.dirac 0 +
    ENNReal.ofReal (threeAtomMiddle r γ a / d) • Measure.dirac a +
    ENNReal.ofReal (threeAtomLast r a / d) • Measure.dirac (2 * a)

private theorem threeAtomMiddle_pos {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0) :
    0 < threeAtomMiddle r γ a :=
  mul_pos (neg_pos.mpr (mul_neg_of_pos_of_neg (by norm_num) hcos)) (Real.exp_pos _)

private theorem threeAtomTotal_pos {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0) :
    0 < threeAtomTotal r γ a :=
  add_pos (add_pos zero_lt_one (threeAtomMiddle_pos (r := r) hcos)) (Real.exp_pos _)

private theorem threeAtom_weights_pos {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0) :
    0 < 1 / threeAtomTotal r γ a ∧
    0 < threeAtomMiddle r γ a / threeAtomTotal r γ a ∧
    0 < threeAtomLast r a / threeAtomTotal r γ a := by
  have hd := threeAtomTotal_pos (r := r) hcos
  exact ⟨div_pos zero_lt_one hd, div_pos (threeAtomMiddle_pos (r := r) hcos) hd,
    div_pos (Real.exp_pos _) hd⟩

private theorem threeAtom_apply {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0)
    {s : Set ℝ} (h₀ : (0 : ℝ) ∈ s) (h₁ : a ∈ s) (h₂ : 2 * a ∈ s) :
    threeAtom r γ a s = 1 := by
  let d := threeAtomTotal r γ a
  let m := threeAtomMiddle r γ a
  let c := threeAtomLast r a
  obtain ⟨hp, hq, ht⟩ := threeAtom_weights_pos (r := r) hcos
  have hsum : 1 / d + m / d + c / d = 1 := by
    rw [← add_div, ← add_div]
    exact div_self (threeAtomTotal_pos (r := r) hcos).ne'
  change ((ENNReal.ofReal (1 / d) • Measure.dirac (0 : ℝ) +
    ENNReal.ofReal (m / d) • Measure.dirac a +
    ENNReal.ofReal (c / d) • Measure.dirac (2 * a)) : Measure ℝ) s = 1
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem h₀,
    Measure.dirac_apply_of_mem h₁, Measure.dirac_apply_of_mem h₂]
  change ENNReal.ofReal (1 / d) * 1 + ENNReal.ofReal (m / d) * 1 +
    ENNReal.ofReal (c / d) * 1 = 1
  simp only [mul_one]
  rw [← ENNReal.ofReal_add hp.le hq.le, ← ENNReal.ofReal_add (add_nonneg hp.le hq.le) ht.le,
    hsum, ENNReal.ofReal_one]

theorem threeAtom_isProbabilityMeasure {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0) :
    IsProbabilityMeasure (threeAtom r γ a) :=
  ⟨threeAtom_apply hcos (mem_univ _) (mem_univ _) (mem_univ _)⟩

theorem threeAtom_Icc {r γ a A : ℝ} (hcos : Real.cos (γ * a) < 0) (ha : 0 ≤ a)
    (hA : 2 * a ≤ A) : threeAtom r γ a (Icc 0 A) = 1 := by
  have ha₂ : a ≤ 2 * a := by linarith
  exact threeAtom_apply hcos ⟨le_rfl, (ha.trans ha₂).trans hA⟩
    ⟨ha, ha₂.trans hA⟩ ⟨ha.trans ha₂, hA⟩

private theorem threeAtom_expMoment {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0) (z : ℂ) :
    expMoment (threeAtom r γ a) z =
      (1 + (threeAtomMiddle r γ a : ℂ) * Complex.exp (z * (a : ℂ)) +
        (threeAtomLast r a : ℂ) * Complex.exp (z * ((2 * a : ℝ) : ℂ))) /
        (threeAtomTotal r γ a : ℂ) := by
  let f : ℝ → ℂ := fun x => Complex.exp (z * (x : ℂ))
  let d := threeAtomTotal r γ a
  let m := threeAtomMiddle r γ a
  let c := threeAtomLast r a
  let μ₀ : Measure ℝ := ENNReal.ofReal (1 / d) • Measure.dirac 0
  let μ₁ : Measure ℝ := ENNReal.ofReal (m / d) • Measure.dirac a
  let μ₂ : Measure ℝ := ENNReal.ofReal (c / d) • Measure.dirac (2 * a)
  have h₀ : Integrable f μ₀ :=
    (integrable_dirac (a := 0) (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top
  have h₁ : Integrable f μ₁ :=
    (integrable_dirac (a := a) (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top
  have h₂ : Integrable f μ₂ :=
    (integrable_dirac (a := 2 * a) (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top
  obtain ⟨hp, hq, ht⟩ := threeAtom_weights_pos (r := r) hcos
  change (∫ x, f x ∂(μ₀ + μ₁ + μ₂)) =
    (1 + (m : ℂ) * f a + (c : ℂ) * f (2 * a)) / (d : ℂ)
  rw [integral_add_measure (h₀.add_measure h₁) h₂, integral_add_measure h₀ h₁]
  dsimp only [μ₀, μ₁, μ₂]
  have hp' : 0 ≤ 1 / d := hp.le
  have hq' : 0 ≤ m / d := hq.le
  have ht' : 0 ≤ c / d := ht.le
  simp only [integral_smul_measure, integral_dirac, f, Complex.real_smul]
  rw [ENNReal.toReal_ofReal hp', ENNReal.toReal_ofReal hq', ENNReal.toReal_ofReal ht']
  simp only [
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, div_mul_eq_mul_div₀, ← add_div]

private theorem threeAtom_expMoment_factored {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0)
    (z : ℂ) : expMoment (threeAtom r γ a) z =
      ((Complex.exp ((z - (r : ℂ)) * (a : ℂ)) -
          Complex.exp (((γ : ℂ) * Complex.I) * (a : ℂ))) *
        (Complex.exp ((z - (r : ℂ)) * (a : ℂ)) -
          Complex.exp ((-((γ : ℂ) * Complex.I)) * (a : ℂ)))) /
        (threeAtomTotal r γ a : ℂ) := by
  let x := Complex.exp ((z - (r : ℂ)) * (a : ℂ))
  let p := Complex.exp (((γ : ℂ) * Complex.I) * (a : ℂ))
  let q := Complex.exp ((-((γ : ℂ) * Complex.I)) * (a : ℂ))
  have hphase : ((γ : ℂ) * Complex.I) * (a : ℂ) = ((γ * a : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_mul]
    ring
  have hsum : p + q = 2 * (Real.cos (γ * a) : ℂ) := by
    simp only [p, q, neg_mul, hphase, Complex.ofReal_cos, Complex.two_cos]
  have hprod : p * q = 1 := by
    dsimp only [p, q]
    rw [neg_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hscale : (Real.exp (-(r * a)) : ℂ) * Complex.exp (z * (a : ℂ)) = x := by
    dsimp only [x]
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_mul]
    congr 1 <;> ring
  have hmiddle : (threeAtomMiddle r γ a : ℂ) * Complex.exp (z * (a : ℂ)) =
      -(2 * (Real.cos (γ * a) : ℂ)) * x := by
    simp only [threeAtomMiddle, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    rw [mul_assoc, hscale]
  have hlast : (threeAtomLast r a : ℂ) * Complex.exp (z * ((2 * a : ℝ) : ℂ)) = x ^ 2 := by
    have harg : ((-2 * r * a : ℝ) : ℂ) + z * ((2 * a : ℝ) : ℂ) =
        (z - (r : ℂ)) * (a : ℂ) + (z - (r : ℂ)) * (a : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
      ring
    dsimp only [threeAtomLast, x]
    rw [Complex.ofReal_exp, ← Complex.exp_add, harg, Complex.exp_add, pow_two]
  have hfactor : 1 + -(2 * (Real.cos (γ * a) : ℂ)) * x + x ^ 2 = (x - p) * (x - q) := by
    calc
      _ = x ^ 2 - (p + q) * x + p * q := by rw [hsum, hprod]; ring
      _ = _ := by ring
  rw [threeAtom_expMoment hcos, hmiddle, hlast, hfactor]

/-- The only possible zeros of the moment come from the two exponential collisions. -/
theorem threeAtom_expMoment_eq_zero_iff {r γ a : ℝ} (hcos : Real.cos (γ * a) < 0) (z : ℂ) :
    expMoment (threeAtom r γ a) z = 0 ↔
      Complex.exp ((z - (r : ℂ)) * (a : ℂ)) = Complex.exp (((γ : ℂ) * Complex.I) * (a : ℂ)) ∨
      Complex.exp ((z - (r : ℂ)) * (a : ℂ)) = Complex.exp ((-((γ : ℂ) * Complex.I)) * (a : ℂ)) := by
  have hden : (threeAtomTotal r γ a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (threeAtomTotal_pos (r := r) hcos).ne'
  simp only [threeAtom_expMoment_factored hcos, div_eq_zero_iff, hden, or_false, mul_eq_zero,
    sub_eq_zero]

private theorem countable_exp_collision {u v : ℂ} (huv : u ≠ v) :
    {a : ℝ | Complex.exp (u * (a : ℂ)) = Complex.exp (v * (a : ℂ))}.Countable := by
  let f : ℤ → ℝ := fun n => (((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) / (u - v)).re
  apply (Set.countable_range f).mono
  intro a ha
  change Complex.exp (u * (a : ℂ)) = Complex.exp (v * (a : ℂ)) at ha
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp ha
  have hdiv : (a : ℂ) = ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) / (u - v) := by
    apply (eq_div_iff (sub_ne_zero.mpr huv)).2
    calc
      _ = u * (a : ℂ) - v * (a : ℂ) := by ring
      _ = _ := by rw [hn]; ring
  exact ⟨n, by simpa only [f, Complex.ofReal_re] using congrArg Complex.re hdiv.symm⟩

/-- A positive three-atom probability measure cancels the prescribed conjugate pair and
preserves any specified mode distinct from the pair. -/
theorem exists_threeAtom_zero_filter (r : ℝ) {γ : ℝ} (hγ : 0 < γ) (w : ℂ)
    (hwPlus : w ≠ (r : ℂ) + (γ : ℂ) * Complex.I)
    (hwMinus : w ≠ star ((r : ℂ) + (γ : ℂ) * Complex.I)) :
    ∃ a ∈ Ioo (Real.pi / 2 / γ) (Real.pi / γ),
      IsProbabilityMeasure (threeAtom r γ a) ∧
      (threeAtom r γ a) (Icc 0 (2 * Real.pi / γ)) = 1 ∧
      (threeAtom r γ a).support ⊆ Icc 0 (2 * Real.pi / γ) ∧
      expMoment (threeAtom r γ a) ((r : ℂ) + (γ : ℂ) * Complex.I) = 0 ∧
      expMoment (threeAtom r γ a) (star ((r : ℂ) + (γ : ℂ) * Complex.I)) = 0 ∧
      expMoment (threeAtom r γ a) w ≠ 0 := by
  let b : ℂ := (γ : ℂ) * Complex.I
  change w ≠ (r : ℂ) + b at hwPlus
  change w ≠ star ((r : ℂ) + b) at hwMinus
  have hstar : star ((r : ℂ) + b) = (r : ℂ) - b := by
    simp [b, sub_eq_add_neg]
  have hnePlus : w - (r : ℂ) ≠ b := by
    intro h
    apply hwPlus
    calc
      w = (w - (r : ℂ)) + (r : ℂ) := (sub_add_cancel _ _).symm
      _ = _ := by rw [h, add_comm]
  have hneMinus : w - (r : ℂ) ≠ -b := by
    intro h
    apply hwMinus
    rw [hstar]
    calc
      w = (w - (r : ℂ)) + (r : ℂ) := (sub_add_cancel _ _).symm
      _ = _ := by rw [h]; ring
  let badPlus : Set ℝ := {a | Complex.exp ((w - (r : ℂ)) * (a : ℂ)) = Complex.exp (b * (a : ℂ))}
  let badMinus : Set ℝ := {a | Complex.exp ((w - (r : ℂ)) * (a : ℂ)) = Complex.exp (-b * (a : ℂ))}
  have hbad : (badPlus ∪ badMinus).Countable :=
    (countable_exp_collision hnePlus).union (countable_exp_collision hneMinus)
  have hinterval : Real.pi / 2 / γ < Real.pi / γ :=
    div_lt_div_of_pos_right (by linarith [Real.pi_pos]) hγ
  have hnot : ¬ Ioo (Real.pi / 2 / γ) (Real.pi / γ) ⊆ badPlus ∪ badMinus := by
    intro h
    exact (not_le_of_gt hinterval) ((Cardinal.Real.Ioo_countable_iff).mp (hbad.mono h))
  obtain ⟨a, ha, havoid⟩ := Set.not_subset.mp hnot
  have ha₀ : 0 < a := (div_pos (div_pos Real.pi_pos (by norm_num)) hγ).trans ha.1
  have hlo : Real.pi / 2 < γ * a := (div_lt_iff₀' hγ).mp ha.1
  have hhi : γ * a < Real.pi := (lt_div_iff₀' hγ).mp ha.2
  have hcos : Real.cos (γ * a) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hlo (by linarith [Real.pi_pos])
  have hwidth : 2 * a ≤ 2 * Real.pi / γ := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha.2.le (by norm_num)
  letI : IsProbabilityMeasure (threeAtom r γ a) := threeAtom_isProbabilityMeasure hcos
  have hmass : threeAtom r γ a (Icc 0 (2 * Real.pi / γ)) = 1 :=
    threeAtom_Icc hcos ha₀.le hwidth
  have hsupport : (threeAtom r γ a).support ⊆ Icc 0 (2 * Real.pi / γ) :=
    Measure.support_subset_of_isClosed isClosed_Icc
      ((mem_ae_iff_prob_eq_one measurableSet_Icc).2 hmass)
  refine ⟨a, ha, inferInstance, hmass, hsupport, ?_, ?_, ?_⟩
  · change expMoment (threeAtom r γ a) ((r : ℂ) + b) = 0
    apply (threeAtom_expMoment_eq_zero_iff hcos _).2
    have hshift : (r : ℂ) + b - (r : ℂ) = b := by ring
    exact Or.inl (by rw [hshift])
  · change expMoment (threeAtom r γ a) (star ((r : ℂ) + b)) = 0
    rw [hstar]
    apply (threeAtom_expMoment_eq_zero_iff hcos _).2
    have hshift : (r : ℂ) - b - (r : ℂ) = -b := by ring
    exact Or.inr (by rw [hshift])
  · intro hzero
    exact havoid ((threeAtom_expMoment_eq_zero_iff hcos w).1 hzero)

/-- Build a single compact probability measure annihilating the selected sequence of
modes, with a support-length budget given by their reciprocal ordinates. -/
theorem exists_selective_spectral_filter {r γ : ℕ → ℝ} {w : ℂ} (selected : ℕ → Prop)
    [DecidablePred selected] (hγ : ∀ j, selected j → 0 < γ j)
    (hsparse : Summable (fun j => if selected j then (γ j)⁻¹ else 0))
    (havoid : ∀ j, selected j →
      w ≠ (r j : ℂ) + (γ j : ℂ) * Complex.I ∧
      w ≠ star ((r j : ℂ) + (γ j : ℂ) * Complex.I)) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ν (Icc 0 (∑' j, if selected j then 2 * Real.pi / γ j else 0)) = 1 ∧
      (∀ j, selected j →
        expMoment ν ((r j : ℂ) + (γ j : ℂ) * Complex.I) = 0 ∧
        expMoment ν (star ((r j : ℂ) + (γ j : ℂ) * Complex.I)) = 0) ∧
      expMoment ν w ≠ 0 := by
  let width (j : ℕ) : ℝ := if selected j then 2 * Real.pi / γ j else 0
  let mode (j : ℕ) : ℂ := (r j : ℂ) + (γ j : ℂ) * Complex.I
  have factor (j : ℕ) :
      ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Icc 0 (width j)) = 1 ∧
        (selected j → expMoment μ (mode j) = 0 ∧ expMoment μ (star (mode j)) = 0) ∧
        expMoment μ w ≠ 0 := by
    by_cases hj : selected j
    · obtain ⟨a, -, hprob, hmass, -, hplus, hminus, hn⟩ :=
        exists_threeAtom_zero_filter (r j) (hγ j hj) w (havoid j hj).1 (havoid j hj).2
      exact ⟨threeAtom (r j) (γ j) a, hprob, by simpa [width, hj] using hmass,
        fun _ => ⟨hplus, hminus⟩, hn⟩
    · refine ⟨Measure.dirac 0, inferInstance, ?_, fun h => (hj h).elim, ?_⟩
      · simp [width, hj, Measure.dirac_apply_of_mem]
      · change (∫ x : ℝ, Complex.exp (w * (x : ℂ)) ∂Measure.dirac 0) ≠ 0
        simp
  choose μ hprob hmass hcut hnonzero using factor
  letI : ∀ j, IsProbabilityMeasure (μ j) := hprob
  have hwidth (j : ℕ) : 0 ≤ width j := by
    by_cases hj : selected j
    · simpa [width, hj] using (div_pos (by positivity : 0 < 2 * Real.pi) (hγ j hj)).le
    · simp [width, hj]
  have hwidthSum : Summable width := by
    refine (hsparse.mul_left (2 * Real.pi)).congr ?_
    intro j
    by_cases hj : selected j <;> simp [width, hj, div_eq_mul_inv]
  obtain ⟨ν, hν, hνmass, hprod⟩ :=
    exists_probability_hasProd_expMoment hwidth hwidthSum hmass
  have zero_of_factor (z : ℂ) (j : ℕ) (hj : expMoment (μ j) z = 0) :
      expMoment ν z = 0 :=
    (hprod z).tprod_eq.symm.trans (tprod_of_exists_eq_zero ⟨j, hj⟩)
  exact ⟨ν, hν, hνmass, fun j hj => ⟨zero_of_factor _ j (hcut j hj).1,
    zero_of_factor _ j (hcut j hj).2⟩,
    expMoment_ne_zero_of_factor_ne_zero hwidth hwidthSum hmass (hprod w) hnonzero⟩

end PositiveSpectralKernel
