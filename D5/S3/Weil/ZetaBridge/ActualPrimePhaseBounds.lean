/- GID: D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualPrimePhaseBounds
   mirror-E: none(waiver:general-analytic-estimate)
   anchors: []
   utility: none
   digest: Explicit amplitude, chord and moment bounds for the actual finite prime-power symbol. -/

import D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Explicit bounds for the actual finite arithmetic symbol

The amplitude retains all labels in Ico 2 c and their von Mangoldt weights.
Actual logarithmic phase gaps control the first moment and both ordered
second-moment channels, with resonant pairs retained in the existing mean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexConjugate
namespace D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.ActualFullSymbolTail

private lemma weight_nonneg (q : ℕ) : 0 ≤ primeWeight q :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

private lemma reciprocal_sqrt_step {q : ℕ} (hq : 2 ≤ q) :
    1 / Real.sqrt (q : ℝ) ≤
      2 * (Real.sqrt (q : ℝ) - Real.sqrt ((q-1 : ℕ) : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : ((q-1 : ℕ) : ℝ) = (q : ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hs := Real.sqrt_pos.2 hq0
  have ht := Real.sqrt_nonneg ((q-1 : ℕ) : ℝ)
  have hm : Real.sqrt ((q-1 : ℕ) : ℝ) ≤ Real.sqrt (q : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le q 1))
  have he1 := Real.sq_sqrt hq0.le
  have he2 : Real.sqrt ((q-1 : ℕ) : ℝ)^2 = (q : ℝ)-1 :=
    (Real.sq_sqrt (Nat.cast_nonneg (q-1))).trans hq1
  apply (div_le_iff₀ hs).2
  have hh := mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hm)
  nlinarith only [he1,he2,hh]

/-- Amplitude over exactly Ico 2 c, with every von Mangoldt prime power. -/
theorem amplitude_le {c : ℕ} (hc : 3 ≤ c) :
    (∑ q ∈ primeIndices c, primeWeight q) ≤
      2 * Real.sqrt (c : ℝ) * logLength c := by
  have hc2 : 2 ≤ c := by omega
  have hL := logLength_pos hc2
  have hpoint (q : ℕ) (hq : q ∈ primeIndices c) :
      primeWeight q ≤ logLength c * (1 / Real.sqrt (q : ℝ)) := by
    have hq2 := (Finset.mem_Ico.mp hq).1
    have hqc := (Finset.mem_Ico.mp hq).2
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hlog : Real.log (q : ℝ) ≤ logLength c :=
      Real.log_le_log hq0 (by exact_mod_cast hqc.le)
    calc
      primeWeight q ≤ Real.log (q : ℝ) / Real.sqrt (q : ℝ) :=
        div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
          (Real.sqrt_nonneg _)
      _ ≤ logLength c / Real.sqrt (q : ℝ) :=
        div_le_div_of_nonneg_right hlog (Real.sqrt_nonneg _)
      _ = _ := by ring
  have htel : (∑ q ∈ Finset.Ico 2 c,
      (Real.sqrt (q : ℝ)-Real.sqrt ((q-1 : ℕ) : ℝ))) =
      Real.sqrt ((c-1 : ℕ) : ℝ)-1 := by
    have h := Finset.sum_Ico_sub (fun q : ℕ => Real.sqrt ((q-1 : ℕ) : ℝ)) hc2
    simpa only [Nat.add_sub_cancel, Nat.reduceSubDiff, Nat.cast_one, Real.sqrt_one] using h
  have hsum : (∑ q ∈ primeIndices c, 1 / Real.sqrt (q : ℝ)) ≤
      2 * (Real.sqrt ((c-1 : ℕ) : ℝ)-1) := by
    calc
      _ ≤ ∑ q ∈ Finset.Ico 2 c,
          2*(Real.sqrt (q : ℝ)-Real.sqrt ((q-1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun q hq => reciprocal_sqrt_step (Finset.mem_Ico.mp hq).1)
      _ = _ := by rw [← Finset.mul_sum,htel]
  have hs : Real.sqrt ((c-1 : ℕ) : ℝ) ≤ Real.sqrt (c : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le c 1))
  calc
    _ ≤ ∑ q ∈ primeIndices c, logLength c * (1 / Real.sqrt (q : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = logLength c * ∑ q ∈ primeIndices c, 1 / Real.sqrt (q : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ logLength c * (2*(Real.sqrt ((c-1 : ℕ) : ℝ)-1)) :=
      mul_le_mul_of_nonneg_left hsum hL.le
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hs hL.le,hL.le]

private lemma log_ratio_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y-x)/y ≤ Real.log y-Real.log x := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne', inv_div] at h
  convert h using 1
  field_simp [hy.ne']

private lemma log_two_lower : (1 : ℝ)/2 ≤ Real.log (2 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h ⊢
  exact h

private lemma label_log_gaps {c q : ℕ} (hc : 3 ≤ c) (hq : q ∈ primeIndices c) :
    1/(c : ℝ) ≤ Real.log (q : ℝ) ∧
      1/(c : ℝ) ≤ logLength c-Real.log (q : ℝ) := by
  obtain ⟨hq2,hqc⟩ := Finset.mem_Ico.mp hq
  have hcR : (3:ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0:ℝ)<c := by linarith
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hq0 : (0:ℝ)<q := by linarith
  have hstep : (q:ℝ)+1 ≤ c := by exact_mod_cast (show q+1≤c by omega)
  have hi : 1/(c:ℝ) ≤ 1/2 := (div_le_div_iff₀ hc0 (by norm_num)).2 (by linarith)
  constructor
  · exact hi.trans (log_two_lower.trans (Real.log_le_log (by norm_num) hqR))
  · have h := log_ratio_lower hq0 hc0
    have hh : 1/(c:ℝ) ≤ ((c:ℝ)-q)/c :=
      div_le_div_of_nonneg_right (by linarith) hc0.le
    exact hh.trans h

private lemma chord_formula (L t : ℝ) :
    ‖1-circleMap (0:ℂ) 1 (2*Real.pi*t/L)‖ =
      2*|Real.sin (Real.pi*t/L)| := by
  rw [norm_sub_rev]
  simp only [circleMap, Complex.ofReal_one, zero_add, one_mul]
  rw [mul_comm (_ : ℂ) Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show (2*Real.pi*t/L)/2 = Real.pi*t/L by ring]

/-- A private chord calculation pays BOTH endpoints of a full period. -/
private lemma chord_lower {L t e : ℝ} (hL : 0 < L)
    (ht : 0 ≤ t) (htL : t ≤ L) (he : e ≤ t) (heL : e ≤ L-t) :
    4*e/L ≤ ‖1-circleMap (0:ℂ) 1 (2*Real.pi*t/L)‖ := by
  rw [chord_formula]
  by_cases hh : t ≤ L/2
  · have hx : 0 ≤ Real.pi*t/L := by positivity
    have hx' : Real.pi*t/L ≤ Real.pi/2 := by
      apply (div_le_iff₀ hL).2
      have hp := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
      nlinarith only [hp]
    have hs := Real.mul_le_sin hx hx'
    have he' : 2*e/L ≤ (2/Real.pi)*(Real.pi*t/L) := by
      calc
        _ ≤ 2*t/L := div_le_div_of_nonneg_right (by linarith) hL.le
        _ = _ := by field_simp [Real.pi_pos.ne',hL.ne']
    calc
      4*e/L = 2*(2*e/L) := by ring
      _ ≤ 2*((2/Real.pi)*(Real.pi*t/L)) := mul_le_mul_of_nonneg_left he' (by norm_num)
      _ ≤ 2*Real.sin (Real.pi*t/L) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
  · have hx : 0 ≤ Real.pi*(L-t)/L :=
      div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr htL)) hL.le
    have hx' : Real.pi*(L-t)/L ≤ Real.pi/2 := by
      apply (div_le_iff₀ hL).2
      have hp := mul_le_mul_of_nonneg_left (show L-t ≤ L/2 by linarith) Real.pi_pos.le
      nlinarith only [hp]
    have hs := Real.mul_le_sin hx hx'
    have he' : 2*e/L ≤ (2/Real.pi)*(Real.pi*(L-t)/L) := by
      calc
        _ ≤ 2*(L-t)/L := div_le_div_of_nonneg_right (by linarith) hL.le
        _ = _ := by field_simp [Real.pi_pos.ne',hL.ne']
    have hid : Real.pi*(L-t)/L = Real.pi-Real.pi*t/L := by
      field_simp [hL.ne']
    have hsin : Real.sin (Real.pi*(L-t)/L) = Real.sin (Real.pi*t/L) := by
      rw [hid,Real.sin_pi_sub]
    rw [hsin] at hs
    calc
      4*e/L = 2*(2*e/L) := by ring
      _ ≤ 2*((2/Real.pi)*(Real.pi*(L-t)/L)) := mul_le_mul_of_nonneg_left he' (by norm_num)
      _ ≤ 2*Real.sin (Real.pi*t/L) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)

private lemma chord_neg (L t : ℝ) :
    ‖1-circleMap (0:ℂ) 1 (2*Real.pi*(-t)/L)‖ =
      ‖1-circleMap (0:ℂ) 1 (2*Real.pi*t/L)‖ := by
  rw [chord_formula,chord_formula,show Real.pi*(-t)/L = -(Real.pi*t/L) by ring,
    Real.sin_neg,abs_neg]

private lemma chord_period (L t : ℝ) (hL : L ≠ 0) :
    ‖1-circleMap (0:ℂ) 1 (2*Real.pi*t/L)‖ =
      ‖1-circleMap (0:ℂ) 1 (2*Real.pi*(t-L)/L)‖ := by
  rw [chord_formula,chord_formula,
    show Real.pi*(t-L)/L = Real.pi*t/L-Real.pi by field_simp [hL],
    Real.sin_sub_pi,abs_neg]

private lemma first_phase_formula (c q : ℕ) :
    primePhase c q = circleMap 0 1 (2*Real.pi*Real.log (q:ℝ)/logLength c) := by
  unfold primePhase theta
  congr 1
  ring

private lemma difference_phase_formula (c p q : ℕ) :
    primePhase c p * conj (primePhase c q) =
      circleMap 0 1 (2*Real.pi*(Real.log (p:ℝ)-Real.log (q:ℝ))/logLength c) := by
  rw [primePhase,primePhase,conj_circleMap_zero,circleMap_zero_mul]
  norm_num only [one_mul]
  congr 1
  unfold theta
  ring

private lemma sum_phase_formula (c p q : ℕ) :
    primePhase c p * primePhase c q =
      circleMap 0 1 (2*Real.pi*(Real.log (p:ℝ)+Real.log (q:ℝ))/logLength c) := by
  rw [primePhase,primePhase,circleMap_zero_mul]
  norm_num only [one_mul]
  congr 1
  unfold theta
  ring

/-- Actual first-phase denominators, including the upper endpoint gap. -/
private theorem first_chord_lower {c q : ℕ} (hc : 3 ≤ c) (hq : q ∈ primeIndices c) :
    4/((c:ℝ)*logLength c) ≤ ‖1-primePhase c q‖ := by
  have hL := logLength_pos (show 2≤c by omega)
  have hc0 : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  obtain ⟨ha,hb⟩ := label_log_gaps hc hq
  rw [first_phase_formula]
  convert chord_lower hL ((by positivity : (0:ℝ) ≤ 1/c).trans ha)
    (by linarith [show (0:ℝ) ≤ 1/c by positivity]) ha hb using 1
  field_simp [hc0.ne',hL.ne']

private lemma ordered_log_chord {c p q : ℕ} (hc : 3 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) (hpq : p < q) :
    4/((c:ℝ)*logLength c) ≤
      ‖1-circleMap (0:ℂ) 1
        (2*Real.pi*(Real.log (q:ℝ)-Real.log (p:ℝ))/logLength c)‖ := by
  have hL := logLength_pos (show 2≤c by omega)
  have hp2 := (Finset.mem_Ico.mp hp).1
  have hqc := (Finset.mem_Ico.mp hq).2
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hc0 : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hqcR : (q:ℝ) ≤ c := by exact_mod_cast hqc.le
  have hpqR : (p:ℝ)+1 ≤ q := by exact_mod_cast (show p+1≤q by omega)
  have hlog := log_ratio_lower hp0 hq0
  have hlo : 1/(c:ℝ) ≤ Real.log (q:ℝ)-Real.log (p:ℝ) := by
    calc
      _ ≤ 1/(q:ℝ) := div_le_div_of_nonneg_left (by norm_num) hq0 hqcR
      _ ≤ ((q:ℝ)-p)/q := div_le_div_of_nonneg_right (by linarith) hq0.le
      _ ≤ _ := hlog
  have hlogp : Real.log (2:ℝ) ≤ Real.log (p:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  have hqgap := (label_log_gaps hc hq).2
  have hwrap : 1/(c:ℝ) ≤ logLength c-(Real.log (q:ℝ)-Real.log (p:ℝ)) := by
    have hpnon : 0 ≤ Real.log (p:ℝ) := (by norm_num : (0:ℝ) ≤ 1/2).trans
      (log_two_lower.trans hlogp)
    linarith
  convert chord_lower hL ((by positivity : (0:ℝ) ≤ 1/c).trans hlo)
    (by linarith [show (0:ℝ) ≤ 1/c by positivity]) hlo hwrap using 1
  field_simp [hc0.ne',hL.ne']

/-- Distinct actual differences, with both orientations and wraparound. -/
private theorem difference_chord_lower {c p q : ℕ} (hc : 3 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) (hpq : p ≠ q) :
    4/((c:ℝ)*logLength c) ≤ ‖1-primePhase c p*conj (primePhase c q)‖ := by
  rw [difference_phase_formula]
  rcases lt_or_gt_of_ne hpq with h | h
  · have he : Real.log (p:ℝ)-Real.log (q:ℝ) =
        -(Real.log (q:ℝ)-Real.log (p:ℝ)) := by ring
    rw [he,chord_neg]
    exact ordered_log_chord hc hp hq h
  · exact ordered_log_chord hc hq hp h

/-- Nonresonant actual sums; pq=c, including self-pairs, is excluded precisely
as in sumCross. The distance to 0, L and 2L is paid explicitly. -/
private theorem sum_chord_lower {c p q : ℕ} (hc : 3 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) (hpq : p * q ≠ c) :
    4/(((c:ℝ)+1)*logLength c) ≤ ‖1-primePhase c p*primePhase c q‖ := by
  have hL := logLength_pos (show 2≤c by omega)
  obtain ⟨hp2,hpc⟩ := Finset.mem_Ico.mp hp
  obtain ⟨hq2,hqc⟩ := Finset.mem_Ico.mp hq
  have hcR : (3:ℝ)≤c := by exact_mod_cast hc
  have hc0 : (0:ℝ)<c := by linarith
  have hc1 : (0:ℝ)<(c:ℝ)+1 := by positivity
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp2
  have hqR : (2:ℝ)≤q := by exact_mod_cast hq2
  have hp0 : (0:ℝ)<p := by linarith
  have hq0 : (0:ℝ)<q := by linarith
  let t : ℝ := Real.log (p:ℝ)+Real.log (q:ℝ)
  let e : ℝ := 1/((c:ℝ)+1)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hec : e ≤ 1/(c:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hc0 (by linarith)
  have hpfirst := (label_log_gaps hc hp).1
  have hqfirst := (label_log_gaps hc hq).1
  have hpgap := (label_log_gaps hc hp).2
  have hqgap := (label_log_gaps hc hq).2
  have ht0 : e ≤ t := by dsimp [t]; linarith
  have ht2 : e ≤ 2*logLength c-t := by dsimp [t]; linarith
  have hprod : Real.log ((p*q : ℕ):ℝ) = t := by
    rw [Nat.cast_mul,Real.log_mul hp0.ne' hq0.ne']
  have hu0 : (0:ℝ)<(p*q:ℕ) := by
    rw [Nat.cast_mul]
    positivity
  rw [sum_phase_formula]
  change 4/(((c:ℝ)+1)*logLength c) ≤ ‖1-circleMap (0:ℂ) 1 (2*Real.pi*t/logLength c)‖
  rcases lt_or_gt_of_ne hpq with hu | hu
  · have huR : ((p*q:ℕ):ℝ)+1≤c := by exact_mod_cast (show p*q+1≤c by omega)
    have hh := log_ratio_lower hu0 hc0
    rw [hprod] at hh
    have hmid : e ≤ logLength c-t := by
      have hstep : 1/(c:ℝ) ≤ ((c:ℝ)-(p*q:ℕ))/c :=
        div_le_div_of_nonneg_right (by linarith) hc0.le
      exact hec.trans (hstep.trans hh)
    convert chord_lower hL (he.trans ht0) (by linarith) ht0 hmid using 1
    dsimp [e]
    field_simp [hc1.ne',hL.ne']
  · have huR : (c:ℝ)+1 ≤ ((p*q:ℕ):ℝ) := by exact_mod_cast (show c+1≤p*q by omega)
    have hh := log_ratio_lower hc0 hc1
    have hlog : Real.log ((c:ℝ)+1) ≤ t := by
      rw [← hprod]
      exact Real.log_le_log hc1 huR
    have hmid : e ≤ t-logLength c := by
      have hratio : (((c:ℝ)+1)-(c:ℝ))/((c:ℝ)+1) = e := by dsimp [e]; ring
      rw [hratio] at hh
      change e ≤ Real.log ((c:ℝ)+1)-logLength c at hh
      linarith
    rw [chord_period _ _ hL.ne']
    convert chord_lower hL (he.trans hmid) (by linarith) hmid
      (show e ≤ logLength c-(t-logLength c) by linarith) using 1
    dsimp [e]
    field_simp [hc1.ne',hL.ne']

private lemma denominator_bound {a d H : ℝ} (ha : 0 ≤ a) (hH : 0 < H)
    (hd : 4 / H ≤ d) : 2*a/d ≤ (H/2)*a := by
  have hd0 : 0 < d := (div_pos (by norm_num) hH).trans_le hd
  apply (div_le_iff₀ hd0).2
  have hh : 4 ≤ d*H := (div_le_iff₀ hH).1 hd
  nlinarith only [mul_le_mul_of_nonneg_right hh ha]

/-- The exact first moment, including the factor two per label. -/
theorem firstMoment_le {c : ℕ} (hc : 3 ≤ c) :
    primeFirstMoment c ≤ (c:ℝ)*Real.sqrt (c:ℝ)*logLength c^2 := by
  have hL := logLength_pos (show 2≤c by omega)
  have hc0 : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  calc
    primeFirstMoment c ≤ ∑ q ∈ primeIndices c,
        ((c:ℝ)*logLength c/2)*primeWeight q := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_of_nonneg (weight_nonneg q)]
      exact denominator_bound (weight_nonneg q) (by positivity) (first_chord_lower hc hq)
    _ = ((c:ℝ)*logLength c/2)*(∑ q ∈ primeIndices c,primeWeight q) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((c:ℝ)*logLength c/2)*(2*Real.sqrt (c:ℝ)*logLength c) :=
      mul_le_mul_of_nonneg_left (amplitude_le hc) (by positivity)
    _ = _ := by ring

private lemma double_mass (c : ℕ) :
    (∑ p ∈ primeIndices c,∑ q ∈ primeIndices c,primeWeight p*primeWeight q) =
      (∑ q ∈ primeIndices c,primeWeight q)^2 := by
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum]

private lemma cross_le {c : ℕ} (hc : 3 ≤ c) :
    primeCross c ≤ ((c:ℝ)*logLength c/2)*(∑ q ∈ primeIndices c,primeWeight q)^2 ∧
    sumCross c ≤ (((c:ℝ)+1)*logLength c/2)*(∑ q ∈ primeIndices c,primeWeight q)^2 := by
  have hL := logLength_pos (show 2≤c by omega)
  have hc0 : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  constructor
  · unfold primeCross orderedCross
    calc
      _ ≤ ∑ p ∈ primeIndices c,∑ q ∈ primeIndices c,
          ((c:ℝ)*logLength c/2)*(primeWeight p*primeWeight q) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        split_ifs with heq
        · exact mul_nonneg (by positivity)
            (mul_nonneg (weight_nonneg p) (weight_nonneg q))
        · rw [abs_of_nonneg (mul_nonneg (weight_nonneg p) (weight_nonneg q))]
          exact denominator_bound (mul_nonneg (weight_nonneg p) (weight_nonneg q))
            (by positivity) (difference_chord_lower hc hp hq heq)
      _ = _ := by
        rw [← double_mass c]
        simp only [Finset.mul_sum]
  · unfold sumCross
    calc
      _ ≤ ∑ p ∈ primeIndices c,∑ q ∈ primeIndices c,
          (((c:ℝ)+1)*logLength c/2)*(primeWeight p*primeWeight q) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        split_ifs with heq
        · exact mul_nonneg (by positivity)
            (mul_nonneg (weight_nonneg p) (weight_nonneg q))
        · rw [abs_of_nonneg (mul_nonneg (weight_nonneg p) (weight_nonneg q))]
          exact denominator_bound (mul_nonneg (weight_nonneg p) (weight_nonneg q))
            (by positivity) (sum_chord_lower hc hp hq heq)
      _ = _ := by
        rw [← double_mass c]
        simp only [Finset.mul_sum]

/-- Actual centered second-moment offset. Ordered resonances remain in mean. -/
theorem offset_le {c : ℕ} (hc : 3 ≤ c) :
    offset c ≤ (c:ℝ)*(2*(c:ℝ)+1)*logLength c^3 := by
  have hL := logLength_pos (show 2≤c by omega)
  have hc0 : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hA0 : 0 ≤ ∑ q ∈ primeIndices c,primeWeight q :=
    Finset.sum_nonneg (fun q _ => weight_nonneg q)
  have hA2 := pow_le_pow_left₀ hA0 (amplitude_le hc) 2
  have hsq := Real.sq_sqrt hc0.le
  have hA : (∑ q ∈ primeIndices c,primeWeight q)^2 ≤ 4*(c:ℝ)*logLength c^2 := by
    simp only [mul_pow,hsq] at hA2
    nlinarith only [hA2]
  obtain ⟨hd,hs⟩ := cross_le hc
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hA
    (show 0 ≤ (c:ℝ)*logLength c/2 by positivity))
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hA
    (show 0 ≤ ((c:ℝ)+1)*logLength c/2 by positivity))
  unfold offset
  nlinarith only [hd',hs']

end D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
