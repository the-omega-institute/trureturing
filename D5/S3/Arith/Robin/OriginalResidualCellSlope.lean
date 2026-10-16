/- GID: D5/S3/Arith/Robin/OriginalResidualCellSlope
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalResidualCellSlope
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual Mobius prefixes pay a finite cell slope with real endpoint phases. -/

import D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
import D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature
import D5.S3.Arith.Robin.QuotientIntegralBudget
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Finset
open D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix prefix_abel)
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature

namespace D5.S3.Arith.Robin.OriginalResidualCellSlope

def logKernel (N : ℕ) (x : ℝ) : ℝ := Real.log ((N : ℝ) / x) / x

def reciprocalPrefix (N j : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 j, (ArithmeticFunction.moebius d : ℝ) * logKernel N d

def abelTail (N h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico h N, (mobiusPrefix k + 2) * (logKernel N k - logKernel N (k + 1 : ℕ))

def weightedTail (N h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico h N, (k : ℝ) * (logKernel N k - logKernel N (k + 1 : ℕ))

/-- Actual finite extrema; the empty-range convention is unused by the theorem. -/
def rho (N h : ℕ) : ℝ :=
  if hs : h < N then (Finset.Ico h N).sup' ⟨h, Finset.mem_Ico.mpr ⟨le_rfl, hs⟩⟩
    (fun k => |mobiusPrefix k + 2| / (k : ℝ)) else 0

def alpha (N h : ℕ) : ℝ :=
  if hs : h < N then (Finset.Ico h N).inf' ⟨h, Finset.mem_Ico.mpr ⟨le_rfl, hs⟩⟩
    (fun k => (mobiusPrefix k + 2) / (k : ℝ)) else 0

def beta (N h : ℕ) : ℝ :=
  if hs : h < N then (Finset.Ico h N).sup' ⟨h, Finset.mem_Ico.mpr ⟨le_rfl, hs⟩⟩
    (fun k => (mobiusPrefix k + 2) / (k : ℝ)) else 0

def cellMass (a b : ℝ) : ℝ := ∫ t in a..b, weight t

def cellMoment (a b : ℝ) : ℝ := ∫ t in a..b, Int.fract t * weight t

def discrepancy (N q : ℕ) (a b : ℝ) : ℝ :=
  reciprocalPrefix N N * (cellMoment a b - cellMass a b / 2) +
    (cellMass a b / 2) * (reciprocalPrefix N N - reciprocalPrefix N q) +
    (cellMass a b / 2) * (mobiusPrefix q + 2) * logKernel N (q + 1 : ℕ)

def phaseCentre (N : ℕ) (a b : ℝ) : ℝ :=
  reciprocalPrefix N N * (weight b * centeredPrimitive b - weight a * centeredPrimitive a)

private lemma kernel_end {N : ℕ} (hN : 0 < N) : logKernel N N = 0 := by
  simp [logKernel, div_self (show (N : ℝ) ≠ 0 by positivity)]

private lemma kernel_nonneg {N : ℕ} {x : ℝ} (hx : 0 < x) (hxN : x ≤ N) :
    0 ≤ logKernel N x := by
  exact div_nonneg (Real.log_nonneg ((one_le_div hx).mpr hxN)) hx.le

private lemma kernel_antitone {N : ℕ} {h : ℝ} (hh : 0 < h) :
    AntitoneOn (logKernel N) (Icc h N) := by
  intro x hx y hy hxy
  have hx0 := hh.trans_le hx.1
  have hy0 := hh.trans_le hy.1
  have hN0 : (0 : ℝ) < N := hy0.trans_le hy.2
  have hratio : (N : ℝ) / y ≤ N / x := div_le_div_of_nonneg_left hN0.le hx0 hxy
  have hlog := Real.log_le_log (div_pos hN0 hy0) hratio
  exact (div_le_div_of_nonneg_right hlog hy0.le).trans
    (div_le_div_of_nonneg_left (Real.log_nonneg ((one_le_div hx0).mpr hx.2)) hx0 hxy)

private lemma kernel_integral {N h : ℕ} (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in (h : ℝ)..(N : ℝ), logKernel N x) =
      (Real.log ((N : ℝ) / h)) ^ 2 / 2 := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hh hhN)
  have he : (∫ x in (h : ℝ)..(N : ℝ), logKernel N x) =
      ∫ x in (h : ℝ)..(N : ℝ), (Real.log N + (-1) * Real.log x) / x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hhN)] at hx
    have hx0 := hh0.trans_le hx.1
    simp [logKernel, Real.log_div hN0.ne' hx0.ne', sub_eq_add_neg]
  rw [he, QuotientIntegralBudget.integral_affine_log_div hh0
    (by exact_mod_cast hhN), Real.log_div hN0.ne' hh0.ne']
  ring

private lemma abel_identity {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N - 2) :
    reciprocalPrefix N N - reciprocalPrefix N q +
      (mobiusPrefix q + 2) * logKernel N (q + 1 : ℕ) = abelTail N (q + 1) := by
  have hend := kernel_end (N := N) (by omega)
  have ha := prefix_abel (fun k => logKernel N k) (N - 1)
  have hb := prefix_abel (fun k => logKernel N k) q
  rw [show N - 1 + 1 = N by omega, hend, mul_zero, sub_zero] at ha
  have hu : reciprocalPrefix N N = reciprocalPrefix N (N - 1) := by
    unfold reciprocalPrefix
    conv_lhs => rw [show N = (N - 1) + 1 by omega]
    rw [sum_Ioc_succ_top (Nat.zero_le (N - 1))]
    simp [show N - 1 + 1 = N by omega, hend]
  have hset : Finset.Ioc q (N - 1) = Finset.Ico (q + 1) N := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  have hs := sum_Ioc_consecutive (f := fun k => mobiusPrefix k *
    (logKernel N k - logKernel N (k + 1 : ℕ))) (Nat.zero_le q) (by omega : q ≤ N - 1)
  rw [hset, ha, hb] at hs
  have ht : (∑ k ∈ Finset.Ico (q + 1) N,
      (logKernel N k - logKernel N (k + 1 : ℕ))) = logKernel N (q + 1 : ℕ) := by
    have he := sum_Ico_sub (fun k : ℕ => logKernel N k) (by omega : q + 1 ≤ N)
    have he' : (∑ k ∈ Finset.Ico (q + 1) N, (logKernel N k - logKernel N (k + 1 : ℕ))) =
        -(∑ k ∈ Finset.Ico (q + 1) N, (logKernel N (k + 1 : ℕ) - logKernel N k)) := by
      rw [← sum_neg_distrib]; apply sum_congr rfl; intro k _; ring
    rw [he', he, hend]; ring
  unfold abelTail
  simp_rw [add_mul]
  rw [sum_add_distrib, ← mul_sum, ht, hu]
  dsimp [reciprocalPrefix] at *
  linarith

private lemma weighted_identity {N h : ℕ} (hh : 0 < h) (hhN : h < N) :
    weightedTail N h = Real.log ((N : ℝ) / h) +
      ∑ k ∈ Finset.Ico (h + 1) N, logKernel N k := by
  have hend := kernel_end (N := N) (by omega)
  have he := sum_Ico_sub (fun k : ℕ => (k : ℝ) * logKernel N k) hhN.le
  have hs : weightedTail N h =
      -(∑ k ∈ Finset.Ico h N, (((k + 1 : ℕ) : ℝ) * logKernel N (k + 1 : ℕ) -
        (k : ℝ) * logKernel N k)) + ∑ k ∈ Finset.Ico h N, logKernel N (k + 1 : ℕ) := by
    rw [← sum_neg_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hshift : (∑ k ∈ Finset.Ico h N, logKernel N (k + 1 : ℕ)) =
      ∑ k ∈ Finset.Ico (h + 1) N, logKernel N k := by
    have ht := sum_Ico_add' (fun k : ℕ => logKernel N k) h N 1
    rw [sum_Ico_succ_top (by omega : h + 1 ≤ N), hend, add_zero] at ht
    exact ht
  rw [hs, he, hend, mul_zero, hshift]
  have hh0 : (h : ℝ) ≠ 0 := by positivity
  have heq : (h : ℝ) * logKernel N h = Real.log ((N : ℝ) / h) := by
    unfold logKernel
    exact mul_div_cancel₀ _ hh0
  rw [zero_sub, neg_neg, heq]

private lemma weight_bounds {N h : ℕ} (hh : 0 < h) (hhN : h < N) :
    Real.log ((N : ℝ) / h) ≤ weightedTail N h ∧
    weightedTail N h ≤ Real.log ((N : ℝ) / h) + (Real.log ((N : ℝ) / h)) ^ 2 / 2 := by
  have hs := AntitoneOn.sum_le_integral_Ico hhN.le
    (kernel_antitone (N := N) (h := (h : ℝ)) (by exact_mod_cast hh))
  have hshift : (∑ k ∈ Finset.Ico h N, logKernel N (k + 1 : ℕ)) =
      ∑ k ∈ Finset.Ico (h + 1) N, logKernel N k := by
    have ht := sum_Ico_add' (fun k : ℕ => logKernel N k) h N 1
    rw [sum_Ico_succ_top (by omega : h + 1 ≤ N), kernel_end (by omega), add_zero] at ht
    exact ht
  rw [hshift, kernel_integral hh hhN.le] at hs
  rw [weighted_identity hh hhN]
  constructor
  · exact le_add_of_nonneg_right (sum_nonneg (fun k hk =>
      kernel_nonneg (by exact_mod_cast (show 0 < k by have := Finset.mem_Ico.mp hk; omega))
        (by exact_mod_cast (Finset.mem_Ico.mp hk).2.le)))
  · linarith

private lemma extremum_bounds {N h k : ℕ} (hh : 0 < h) (hhN : h < N)
    (hk : k ∈ Finset.Ico h N) :
    |mobiusPrefix k + 2| ≤ rho N h * k ∧
    alpha N h * k ≤ mobiusPrefix k + 2 ∧ mobiusPrefix k + 2 ≤ beta N h * k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hh (Finset.mem_Ico.mp hk).1)
  unfold rho alpha beta
  simp only [dif_pos hhN]
  exact ⟨(div_le_iff₀ hk0).mp (le_sup' (fun j => |mobiusPrefix j + 2| / (j : ℝ)) hk),
    (le_div_iff₀ hk0).mp (inf'_le (fun j => (mobiusPrefix j + 2) / (j : ℝ)) hk),
    (div_le_iff₀ hk0).mp (le_sup' (fun j => (mobiusPrefix j + 2) / (j : ℝ)) hk)⟩

private lemma tail_bounds {N h : ℕ} (hh : 0 < h) (hhN : h < N) :
    |abelTail N h| ≤ rho N h * weightedTail N h ∧
    alpha N h * weightedTail N h ≤ abelTail N h ∧
    abelTail N h ≤ beta N h * weightedTail N h := by
  have hd (k : ℕ) (hk : k ∈ Finset.Ico h N) :
      0 ≤ logKernel N k - logKernel N (k + 1 : ℕ) := by
    apply sub_nonneg.mpr
    apply kernel_antitone (h := (h : ℝ)) (by exact_mod_cast hh)
    · exact ⟨by exact_mod_cast (Finset.mem_Ico.mp hk).1, by exact_mod_cast (Finset.mem_Ico.mp hk).2.le⟩
    · exact ⟨by exact_mod_cast (show h ≤ k + 1 by have := Finset.mem_Ico.mp hk; omega),
        by exact_mod_cast (show k + 1 ≤ N by have := Finset.mem_Ico.mp hk; omega)⟩
    · exact_mod_cast (by omega : k ≤ k + 1)
  unfold abelTail weightedTail
  constructor
  · calc
      _ ≤ ∑ k ∈ Finset.Ico h N, |(mobiusPrefix k + 2) *
          (logKernel N k - logKernel N (k + 1 : ℕ))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico h N, rho N h * ((k : ℝ) *
          (logKernel N k - logKernel N (k + 1 : ℕ))) := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (hd k hk)]
        exact (mul_le_mul_of_nonneg_right (extremum_bounds hh hhN hk).1
          (hd k hk)).trans_eq (by ring)
      _ = _ := by rw [mul_sum]
  · constructor
    · rw [mul_sum]
      apply sum_le_sum
      intro k hk
      exact (mul_le_mul_of_nonneg_right (extremum_bounds hh hhN hk).2.1
        (hd k hk)).trans_eq' (by ring)
    · rw [mul_sum]
      apply sum_le_sum
      intro k hk
      exact (mul_le_mul_of_nonneg_right (extremum_bounds hh hhN hk).2.2
        (hd k hk)).trans_eq (by ring)

private lemma cell_centering {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    cellMoment a b - cellMass a b / 2 = ∫ x in a..b, weight x * betaOne x := by
  have hc : ContinuousOn weight (Icc a b) := by
    intro x hx
    have hx1 := ha.trans_le hx.1
    have hx0 : x ≠ 0 := by linarith
    have hl := (Real.log_pos hx1).ne'
    unfold weight
    fun_prop (disch := aesop)
  have hw : IntervalIntegrable weight volume a b :=
    (Set.uIcc_of_le hab ▸ hc).intervalIntegrable
  have hfract : IntervalIntegrable (fun x : ℝ => Int.fract x) volume a b := by
    rw [intervalIntegrable_iff']
    apply Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  have hm := hfract.mul_continuousOn (Set.uIcc_of_le hab ▸ hc)
  unfold cellMoment cellMass
  calc
    _ = ∫ x in a..b, (Int.fract x * weight x - weight x / 2) := by
      rw [intervalIntegral.integral_sub hm (hw.div_const 2), intervalIntegral.integral_div]
    _ = _ := by apply intervalIntegral.integral_congr; intro x _; unfold betaOne; ring

/-- Finite payment with the exact actual Mobius cancellation, the proved logarithmic
budget, and the signed phase interval. No global sign assertion is made. -/
theorem cell_slope_payment {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N - 2)
    {a b : ℝ} (ha : (N : ℝ) < a) (hab : a < b) (_hb : b < 2 * (N : ℝ)) :
    reciprocalPrefix N N - reciprocalPrefix N q +
        (mobiusPrefix q + 2) * logKernel N (q + 1 : ℕ) = abelTail N (q + 1) ∧
    weightedTail N (q + 1) = Real.log ((N : ℝ) / (q + 1 : ℕ)) +
      ∑ k ∈ Finset.Ico (q + 2) N, logKernel N k ∧
    (Real.log ((N : ℝ) / (q + 1 : ℕ)) ≤ weightedTail N (q + 1) ∧
      weightedTail N (q + 1) ≤ Real.log ((N : ℝ) / (q + 1 : ℕ)) +
        (Real.log ((N : ℝ) / (q + 1 : ℕ))) ^ 2 / 2) ∧
    (∀ k ∈ Finset.Ico (q + 1) N, |mobiusPrefix k + 2| ≤ rho N (q + 1) * k) ∧
    |discrepancy N q a b| ≤ |reciprocalPrefix N N| * weight a / 8 +
      (cellMass a b / 2) * rho N (q + 1) *
        (Real.log ((N : ℝ) / (q + 1 : ℕ)) + (Real.log ((N : ℝ) / (q + 1 : ℕ))) ^ 2 / 2) ∧
    (phaseCentre N a b + (cellMass a b / 2) * alpha N (q + 1) * weightedTail N (q + 1) -
        |reciprocalPrefix N N| * (weight a - weight b) / 16 ≤ discrepancy N q a b ∧
      discrepancy N q a b ≤ phaseCentre N a b +
        (cellMass a b / 2) * beta N (q + 1) * weightedTail N (q + 1) +
          |reciprocalPrefix N N| * (weight a - weight b) / 16) := by
  have hh : 0 < q + 1 := by omega
  have hhN : q + 1 < N := by omega
  have ha1 : 1 < a := lt_trans (by exact_mod_cast (by omega : 1 < N)) ha
  have hc := cell_centering ha1 hab.le
  have hp := weighted_bernoulli_phase ha1 hab.le
  have hm : 0 ≤ cellMass a b := intervalIntegral.integral_nonneg hab.le
    (fun x hx => MellinWeightedVariation.weight_nonneg (ha1.trans_le hx.1))
  have hrho : 0 ≤ rho N (q + 1) := by
    have he := (extremum_bounds hh hhN (Finset.mem_Ico.mpr ⟨le_rfl, hhN⟩)).1
    have h0 : (0 : ℝ) < (q + 1 : ℕ) := by positivity
    nlinarith [abs_nonneg (mobiusPrefix (q + 1) + 2)]
  have hid := abel_identity hN hq
  have hw := weight_bounds hh hhN
  have ht := tail_bounds hh hhN
  have hd : discrepancy N q a b =
      reciprocalPrefix N N * (cellMoment a b - cellMass a b / 2) +
        (cellMass a b / 2) * abelTail N (q + 1) := by
    rw [← hid]; unfold discrepancy; ring
  refine ⟨hid, by simpa only [Nat.add_assoc] using weighted_identity hh hhN,
    hw, fun k hk => (extremum_bounds hh hhN hk).1, ?_, ?_⟩
  · rw [hd]
    calc
      _ ≤ |reciprocalPrefix N N * (cellMoment a b - cellMass a b / 2)| +
          |(cellMass a b / 2) * abelTail N (q + 1)| := abs_add_le _ _
      _ = |reciprocalPrefix N N| * |∫ x in a..b, weight x * betaOne x| +
          (cellMass a b / 2) * |abelTail N (q + 1)| := by
        rw [hc, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ cellMass a b / 2)]
      _ ≤ |reciprocalPrefix N N| * (weight a / 8) +
          (cellMass a b / 2) * (rho N (q + 1) *
            (Real.log ((N : ℝ) / (q + 1 : ℕ)) +
              (Real.log ((N : ℝ) / (q + 1 : ℕ))) ^ 2 / 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2.2 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (ht.1.trans
            (mul_le_mul_of_nonneg_left hw.2 hrho)) (by positivity))
      _ = _ := by ring
  · have he : |reciprocalPrefix N N * (cellMoment a b - cellMass a b / 2) -
        phaseCentre N a b| ≤ |reciprocalPrefix N N| * (weight a - weight b) / 16 := by
      unfold phaseCentre
      rw [← mul_sub, abs_mul, hc]
      exact (mul_le_mul_of_nonneg_left hp.2.1 (abs_nonneg _)).trans_eq (by ring)
    have hl := mul_le_mul_of_nonneg_left ht.2.1 (show 0 ≤ cellMass a b / 2 by positivity)
    have hu := mul_le_mul_of_nonneg_left ht.2.2 (show 0 ≤ cellMass a b / 2 by positivity)
    have he' := abs_le.mp he
    rw [hd]
    constructor <;> nlinarith

#print axioms cell_slope_payment

end D5.S3.Arith.Robin.OriginalResidualCellSlope
