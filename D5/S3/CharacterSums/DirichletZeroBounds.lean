/- GID: D5/S3/CharacterSums/DirichletZeroBounds
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletZeroBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the full Dirichlet zero divisor including its simple parity lattice. -/

import D5.S3.CharacterSums.DirichletTrivialZeros
import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SumIntegralComparisons
import D5.S3.Weil.Mertens.Cryptids.DigammaBinet.Foundation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open Complex Filter Set Topology MeasureTheory
open scoped Classical
namespace D5.S3.CharacterSums.DirichletZeroBounds
open D5.S3.CharacterSums.DirichletTrivialZeros
open D5.S3.Analytic.Dilation.ScalarUnitDressing
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes
open ConjectureMachines.Semantics.Riemann.DigammaBinet

private theorem logarithmic_series_bound :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) ∧
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ≤
      Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 ∧
    Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 < 1 := by
  let f : ℝ → ℝ := fun x => Real.log (x + 2) / (x + 2) ^ 2
  have hanti : AntitoneOn f (Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    have hex : Real.exp (2 : ℝ)⁻¹ ≤ 2 := by
      rw [← Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
      linarith [Real.log_two_gt_d9]
    simpa only [Real.rpow_two] using
      Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 2)
        (show Real.exp (2 : ℝ)⁻¹ ≤ x + 2 from by linarith [hx])
        (show Real.exp (2 : ℝ)⁻¹ ≤ y + 2 from by linarith [hy])
        (show x + 2 ≤ y + 2 from by linarith)
  have hn (n : ℕ) : 0 ≤ Real.log (n + 4) / (n + 4) ^ 2 :=
    div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
      (sq_nonneg _)
  have hfinite (N : ℕ) :
      ∑ n ∈ Finset.range N, Real.log (n + 4) / (n + 4) ^ 2 ≤
        (Real.log 3 + 1) / 3 := by
    have hi0 : IntervalIntegrable f volume 0 1 :=
      (hanti.mono (by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Icc_subset_Ici_self)).intervalIntegrable
    have hi1 : IntervalIntegrable f volume 1 (1 + (N : ℝ)) :=
      (hanti.mono (by
        rw [uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) N])]
        intro x hx; exact le_trans (by norm_num) hx.1)).intervalIntegrable
    have hi := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
    have hsum := (hanti.mono (show Icc (1 : ℝ) (1 + N) ⊆ Ici 0 from
      fun x hx => le_trans (by norm_num) hx.1)).sum_le_integral (a := N)
    have hzero := intervalIntegral_log_add_two_div_sq_eq
      (show (0 : ℝ) ≤ 1 + N from by positivity) 1 0
    have hone := intervalIntegral_log_add_two_div_sq_eq (by norm_num : (0 : ℝ) ≤ 1) 1 0
    have hrem : 0 ≤ (1 + Real.log ((1 + (N : ℝ)) + 2)) /
        ((1 + (N : ℝ)) + 2) := by
      apply div_nonneg _ (by positivity)
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (1 + (N : ℝ)) + 2 by
        linarith [Nat.cast_nonneg (α := ℝ) N])]
    have heq (n : ℕ) : f (1 + ((n + 1 : ℕ) : ℝ)) =
        Real.log (n + 4) / (n + 4) ^ 2 := by
      dsimp [f]
      have h : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 4 := by
        push_cast
        ring
      rw [h]
    simp_rw [heq] at hsum
    dsimp [f] at hi
    norm_num [add_assoc] at hzero hone hi hrem
    linarith
  have htail : Summable (fun n : ℕ => Real.log (n + 4) / (n + 4) ^ 2) :=
    summable_of_sum_range_le hn hfinite
  have hall : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
    apply (summable_nat_add_iff 4).mp
    simpa only [Nat.cast_add, Nat.cast_ofNat] using htail
  have hb : (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ≤
      Real.log 2 / 4 + Real.log 3 / 9 + (Real.log 3 + 1) / 3 := by
    have htbound := htail.tsum_le_of_sum_range_le hfinite
    have hsplit := hall.sum_add_tsum_nat_add 4
    norm_num [Finset.sum_range_succ] at hsplit
    norm_num [Nat.cast_add] at hsplit
    linarith
  refine ⟨hall, ?_, ?_⟩
  · linarith [hb]
  · have h2 : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
    have h3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
    linarith
private theorem digamma_re_lt_log_height {z : ℂ} (hz : 1 ≤ z.re) (hz' : z.re ≤ 3 / 2) :
    (Complex.digamma z).re ≤ Real.log (2 * |z.im| + 3) - Real.log 2 + 1 / 2 -
      (1 / (2 * z)).re := by
  have hp : 0 < z.re := by linarith
  have hb := norm_digamma_sub_log_add_half_inv_le_re hp
  have hrep := (Complex.re_le_norm _).trans hb
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; simp [h] at hp)
  have hhalf : 1 / (2 * z.re) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hnorm : 2 * ‖z‖ ≤ 2 * |z.im| + 3 := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hp] at hh
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 * ‖z‖) hnorm
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn.ne'] at hlog
  simp only [add_re, sub_re, Complex.log_re] at hrep
  linarith
private theorem norm_logDeriv_LFunction_two {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖logDeriv χ.LFunction (2 + t * I)‖ ≤
      (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  let s : ℂ := 2 + t * I
  have hs : 1 < s.re := by simp [s]
  have he : logDeriv χ.LFunction s = -LSeries ((fun n : ℕ => χ n) *
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
    rw [logDeriv_apply, χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs,
      χ.LSeries_twist_vonMangoldt_eq hs]
    ring
  have hterm (n : ℕ) : ‖LSeries.term ((fun n : ℕ => χ n) *
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s n‖ ≤ Real.log n / (n : ℝ) ^ 2 := by
    by_cases hn : n = 0
    · simp [hn]
    rw [LSeries.norm_term_eq, if_neg hn]
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hb : ‖χ n‖ * ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
      (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
        ArithmeticFunction.vonMangoldt_le_log
    simpa [s, Real.rpow_two] using
      div_le_div_of_nonneg_right hb (sq_nonneg (n : ℝ))
  rw [he, norm_neg]
  exact (norm_tsum_le_tsum_norm
    (χ.LSeriesSummable_twist_vonMangoldt hs).norm).trans
    ((χ.LSeriesSummable_twist_vonMangoldt hs).norm.tsum_le_tsum hterm
      logarithmic_series_bound.1)
private theorem completion_vertical_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (logDeriv (completion χ) (2 + t * I)).re ≤
        (Real.log (q : ℝ) - Real.log Real.pi + Real.log (|t| + 3) - Real.log 2 + 1 / 2 -
          (1 / ((2 + t * I) + (if χ.Even then 0 else 1))).re) / 2 +
          (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ∧
      (χ.IsPrimitive → χ ≠ 1 → 0 ≤ (logDeriv (completion χ) (2 + t * I)).re) := by
  constructor
  · let z : ℂ := ((2 + t * I) + (if χ.Even then 0 else 1)) / 2
    have hz : 1 ≤ z.re ∧ z.re ≤ 3 / 2 := by
      dsimp [z]; split_ifs <;> norm_num
    have him : 2 * |z.im| = |t| := by
      dsimp [z]; split_ifs <;> simp [abs_div] <;> ring
    have hp := digamma_re_lt_log_height hz.1 hz.2
    have hinv : 2 * z = (2 + t * I) + (if χ.Even then 0 else 1) := by
      dsimp [z]; ring
    rw [him, hinv] at hp
    have hL := (Complex.re_le_norm _).trans (norm_logDeriv_LFunction_two χ t)
    have he := congrArg Complex.re
      (completion_logDeriv χ (s := 2 + t * I) (by simp)
        (χ.LFunction_ne_zero_of_one_le_re (.inr (by
          intro h; have := congrArg Complex.re h; norm_num at this)) (by simp))
        (.inl (by intro h; have := congrArg Complex.re h; norm_num at this)))
    change _ = _ + ((1 / 2 : ℂ) * Complex.digamma z).re + _ at he
    norm_num [Complex.add_re, Complex.mul_re, Complex.log_re] at he
    linarith
  · intro hχ hne
    have hs := completion_vertical_resolvent hχ hne 2 t
      (by
        apply mul_ne_zero (Complex.exp_ne_zero _)
        intro hz
        apply χ.LFunction_ne_zero_of_one_le_re (s := ((2 : ℝ) : ℂ) + t * I)
          (.inl hne) (by norm_num)
        rw [χ.LFunction_eq_completed_div_gammaFactor _
          (.inr (fun h => hne (DirichletCharacter.level_one' χ h))), hz, zero_div])
    norm_num at hs
    rw [← hs.tsum_eq]
    apply tsum_nonneg
    intro ρ
    have hr := (completion_zero_strip hχ ρ.2).2
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The entire completion's inverse-square zero divisor has an explicit height bound. -/
def completionBudget {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  (Real.log (q : ℝ) - Real.log Real.pi + Real.log (|t| + 3) - Real.log 2 + 1 / 2 -
    (1 / ((2 + t * I) + (if χ.Even then 0 else 1))).re) / 2 +
    (Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3)

private theorem completion_square_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (t : ℝ) :
    Summable (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ∧
    (∑' ρ : {z : ℂ // completion χ z = 0},
      (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ≤
      completionBudget χ t ∧
    (∑' ρ : {z : ℂ // completion χ z = 0},
      (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) <
      Real.log ((q : ℝ) * (|t| + 3)) / 2 + 5 / 4 := by
  let f := fun ρ : {z : ℂ // completion χ z = 0} =>
    (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2
  let g := fun ρ : {z : ℂ // completion χ z = 0} =>
    (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * (2 - ρ.1.re) /
      ((2 - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2)
  have hg := completion_vertical_resolvent hχ hne 2 t
      (by
        apply mul_ne_zero (Complex.exp_ne_zero _)
        intro hz
        apply χ.LFunction_ne_zero_of_one_le_re (s := ((2 : ℝ) : ℂ) + t * I)
          (.inl hne) (by norm_num)
        rw [χ.LFunction_eq_completed_div_gammaFactor _
          (.inr (fun h => hne (DirichletCharacter.level_one' χ h))), hz, zero_div])
  norm_num at hg
  change HasSum g _ at hg
  have hfg (ρ : {z : ℂ // completion χ z = 0}) : f ρ ≤ g ρ := by
    have hr := (completion_zero_strip hχ ρ.2).2
    have he : ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2 =
        1 / ((2 - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2) := by
      rw [norm_inv, inv_pow, Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]
    dsimp [f, g]
    rw [he, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt (completion χ) ρ.1)]
  have hf : Summable f := Summable.of_nonneg_of_le (fun _ => by dsimp [f]; positivity)
    hfg hg.summable
  have hsum := hf.tsum_le_tsum hfg hg.summable
  rw [hg.tsum_eq] at hsum
  have hb := (completion_vertical_bound χ t).1
  refine ⟨hf, ?_, ?_⟩
  · dsimp [completionBudget]
    exact hsum.trans (by linarith [logarithmic_series_bound.2.1])
  · have hi : 0 ≤ (1 / ((2 + t * I) + (if χ.Even then 0 else 1))).re := by
      rw [one_div, Complex.inv_re]
      apply div_nonneg _ (Complex.normSq_nonneg _)
      split_ifs <;> norm_num
    have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    rw [Real.log_mul hq.ne' (by positivity : |t| + 3 ≠ 0)]
    linarith [hsum, logarithmic_series_bound.2.1, logarithmic_series_bound.2.2]


private theorem trivial_re {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (trivialPoint χ n).re ≤ 0 := by
  unfold trivialPoint
  split_ifs <;> norm_num <;> linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem trivial_injective {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Function.Injective (trivialPoint χ) := by
  intro n m h
  have hh := congrArg Complex.re h
  simp only [trivialPoint, sub_re, neg_re, mul_re, ofReal_re, natCast_re,
    natCast_im, mul_zero, sub_zero] at hh
  norm_num at hh
  exact hh

private theorem completion_zero_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    completion χ s = 0 ↔ χ.completedLFunction s = 0 := by
  simp only [completion, mul_eq_zero, Complex.exp_ne_zero, false_or]

private theorem completion_order {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (completion χ) s = analyticOrderAt χ.completedLFunction s := by
  exact (nonzero_scalar_dressing_preserves_zero_and_analytic_order
    (f := χ.completedLFunction)
    (g := fun z => Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * z))
    ((DirichletCharacter.differentiable_completedLFunction hne).analyticAt s)
    (by fun_prop) (Complex.exp_ne_zero _)).2

private def zeroMap {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) : {z : ℂ // completion χ z = 0} ⊕ ℕ → {z : ℂ // χ.LFunction z = 0}
  | .inl ρ => ⟨ρ.1, (LFunction_zero_divisor χ ρ.1
      (.inr (fun h => hne (DirichletCharacter.level_one' χ h))) (.inr hne)).1.mpr
      (.inl ((completion_zero_iff χ ρ.1).mp ρ.2))⟩
  | .inr n => ⟨trivialPoint χ n, (LFunction_zero_divisor χ _
      (.inr (fun h => hne (DirichletCharacter.level_one' χ h))) (.inr hne)).1.mpr (.inr ⟨n, rfl⟩)⟩

private def zeroEquiv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    {z : ℂ // completion χ z = 0} ⊕ ℕ ≃ {z : ℂ // χ.LFunction z = 0} :=
  Equiv.ofBijective (zeroMap hne) ⟨by
    intro x y h
    have hv := congrArg Subtype.val h
    cases x with
    | inl ρ =>
      cases y with
      | inl σ => exact congrArg Sum.inl (Subtype.ext hv)
      | inr n =>
        have hr := (completion_zero_strip hχ ρ.2).1
        change ρ.1 = trivialPoint χ n at hv
        rw [hv] at hr
        exact (not_lt_of_ge (trivial_re χ n) hr).elim
    | inr n =>
      cases y with
      | inl ρ =>
        have hr := (completion_zero_strip hχ ρ.2).1
        change trivialPoint χ n = ρ.1 at hv
        rw [← hv] at hr
        exact (not_lt_of_ge (trivial_re χ n) hr).elim
      | inr m => exact congrArg Sum.inr (trivial_injective χ hv), by
    intro ρ
    rcases (LFunction_zero_divisor χ ρ.1
      (.inr (fun h => hne (DirichletCharacter.level_one' χ h))) (.inr hne)).1.mp ρ.2
      with hc | ⟨n, hn⟩
    · exact ⟨.inl ⟨ρ.1, (completion_zero_iff χ ρ.1).mpr hc⟩, rfl⟩
    · exact ⟨.inr n, Subtype.ext hn.symm⟩⟩

private theorem zeroMap_order_left {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (ρ : {z : ℂ // completion χ z = 0}) :
    analyticOrderNatAt χ.LFunction ρ.1 = analyticOrderNatAt (completion χ) ρ.1 := by
  have hn : ¬ ∃ n : ℕ, ρ.1 = trivialPoint χ n := by
    rintro ⟨n, hn⟩
    have hr := (completion_zero_strip hχ ρ.2).1
    rw [hn] at hr
    exact not_lt_of_ge (trivial_re χ n) hr
  have ho := (LFunction_zero_divisor χ ρ.1
      (.inr (fun h => hne (DirichletCharacter.level_one' χ h))) (.inr hne)).2
  rw [if_neg hn, add_zero, ← completion_order χ hne ρ.1] at ho
  exact congrArg ENat.toNat ho

private theorem zeroMap_order_right {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (n : ℕ) :
    analyticOrderNatAt χ.LFunction (trivialPoint χ n) = 1 := by
  have hc : χ.completedLFunction (trivialPoint χ n) ≠ 0 := by
    intro hz
    have hr := (completion_zero_strip hχ
      ((completion_zero_iff χ _).mpr hz)).1
    exact not_lt_of_ge (trivial_re χ n) hr
  have ho := (LFunction_zero_divisor χ (trivialPoint χ n)
    (.inr (fun h => hne (DirichletCharacter.level_one' χ h))) (.inr hne)).2
  have ha := (DirichletCharacter.differentiable_completedLFunction hne).analyticAt
    (trivialPoint χ n)
  rw [if_pos ⟨n, rfl⟩, ha.analyticOrderAt_eq_zero.mpr hc, zero_add] at ho
  simpa only [analyticOrderNatAt, ho, ENat.toNat_one]

private theorem lattice_square_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    Summable (fun n : ℕ => ‖(2 + t * I - trivialPoint χ n)⁻¹‖ ^ 2) ∧
    (∑' n : ℕ, ‖(2 + t * I - trivialPoint χ n)⁻¹‖ ^ 2) ≤ 1 / 2 := by
  let f : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-(2 : ℝ))
  have hs : Summable f := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  have ha : AntitoneOn (fun x : ℝ => x ^ (-(2 : ℝ))) (Ici 1) := by
    intro x hx y hy hxy
    change 1 ≤ x at hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by norm_num)
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-(2 : ℝ))) 1
    (by simpa only [Nat.cast_one] using ha)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg
      (by simp only [Nat.cast_one, mem_Ioi] at hx; linarith) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num)] at ht
  have hsum : (∑' n, f n) ≤ 2 := by
    have he := hs.sum_add_tsum_nat_add 1
    norm_num [f, Finset.sum_range_succ, Nat.cast_add] at he ht
    norm_num [f]
    linarith
  have hb (n : ℕ) : ‖(2 + t * I - trivialPoint χ n)⁻¹‖ ^ 2 ≤ (1 / 4 : ℝ) * f n := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hr : 2 * ((n : ℝ) + 1) ≤ (2 + t * I - trivialPoint χ n).re := by
      unfold trivialPoint
      split_ifs <;> simp <;> linarith
    have hnorm := Complex.re_le_norm (2 + t * I - trivialPoint χ n)
    rw [norm_inv, inv_pow]
    have hd : 4 * ((n : ℝ) + 1) ^ 2 ≤ ‖2 + t * I - trivialPoint χ n‖ ^ 2 := by
      nlinarith [norm_nonneg (2 + t * I - trivialPoint χ n)]
    calc
      _ ≤ (4 * ((n : ℝ) + 1) ^ 2)⁻¹ :=
        (inv_le_inv₀ (by nlinarith) (by positivity)).mpr hd
      _ = _ := by dsimp [f]; rw [Real.rpow_neg (by positivity), Real.rpow_two, mul_inv_rev]; ring
  have hlat := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb
    (hs.mul_left (1 / 4 : ℝ))
  refine ⟨hlat, (hlat.tsum_le_tsum hb (hs.mul_left _)).trans ?_⟩
  rw [tsum_mul_left]
  linarith

/-- All zeros, with their analytic multiplicities, obey a uniform inverse-square budget. -/
theorem zero_square_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (T t : ℝ) (ht : |t| ≤ T) :
    (∀ ρ : {z : ℂ // χ.LFunction z = 0}, ρ.1.re < 1) ∧
    Summable (fun ρ : {z : ℂ // χ.LFunction z = 0} =>
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ∧
    (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) <
      Real.log ((q : ℝ) * (|t| + 3)) / 2 + 7 / 4 ∧
    (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ≤
      Real.log ((q : ℝ) * (T + 3)) + 4 ∧
    (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ≤
      completionBudget χ t + 1 / 2 := by
  let e := zeroEquiv hχ hne
  let f := fun ρ : {z : ℂ // χ.LFunction z = 0} =>
    (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2
  let fc := fun ρ : {z : ℂ // completion χ z = 0} =>
    (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2
  let ft := fun n : ℕ => ‖(2 + t * I - trivialPoint χ n)⁻¹‖ ^ 2
  have he : (fun x => f (e x)) = Sum.elim fc ft := by
    funext x
    cases x with
    | inl ρ =>
      change (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2 = _
      rw [zeroMap_order_left hχ hne]
      rfl
    | inr n =>
      change (analyticOrderNatAt χ.LFunction (trivialPoint χ n) : ℝ) *
        ‖(2 + t * I - trivialPoint χ n)⁻¹‖ ^ 2 = _
      rw [zeroMap_order_right hχ hne]
      simp [ft]
  have hc := completion_square_bound hχ hne t
  have hl := lattice_square_bound χ t
  have hs : Summable (fun x => f (e x)) := by rw [he]; exact Summable.sum (Sum.elim fc ft) hc.1 hl.1
  have hf : Summable f := e.summable_iff.mp hs
  refine ⟨?_, hf, ?_⟩
  · intro ρ
    obtain ⟨x, rfl⟩ := e.surjective ρ
    cases x with
    | inl ρ => exact (completion_zero_strip hχ ρ.2).2
    | inr n => exact (trivial_re χ n).trans_lt (by norm_num)
  · have hv : (∑' ρ, f ρ) = (∑' ρ, fc ρ) + ∑' n, ft n := by
      rw [← e.tsum_eq f, he]
      exact Summable.tsum_sum hc.1 hl.1
    change (∑' ρ, f ρ) < _ ∧ (∑' ρ, f ρ) ≤ _ ∧ (∑' ρ, f ρ) ≤ _
    rw [hv]
    refine ⟨by linarith [hc.2.2, hl.2], ?_, by linarith [hc.2.1, hl.2]⟩
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hT : 0 ≤ T := (abs_nonneg t).trans ht
    have hlog : Real.log ((q : ℝ) * (|t| + 3)) ≤ Real.log ((q : ℝ) * (T + 3)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hq.le)
    have hn : 0 ≤ Real.log ((q : ℝ) * (T + 3)) := by
      apply Real.log_nonneg
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      nlinarith
    linarith [hc.2.2, hl.2]

end D5.S3.CharacterSums.DirichletZeroBounds
