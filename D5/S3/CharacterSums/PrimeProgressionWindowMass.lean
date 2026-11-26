/- GID: D5/S3/CharacterSums/PrimeProgressionWindowMass
   generality: I
   mirror-B: D5/B/S3/CharacterSums/PrimeProgressionWindowMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every fixed reduced progression contributes a positive fraction of logarithmic prime mass in each sufficiently large real power window. -/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S3.CharacterSums.PrimeProgressionWindowMass

section
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries

private def primeTerm {q : ℕ} (a : ZMod q) (j : ℕ) (h : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod q) = a then Real.log n / n * (n : ℝ) ^ (-(j * h)) else 0

private theorem all_eq {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  apply ofReal_injective
  simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
    ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hx, eqOn_LFunctionResidueClassAux ha
    (show 1 < (x : ℂ).re from hx), sub_add_cancel, LSeries, term]
  apply tsum_congr
  intro n
  split_ifs with h
  · simp [h]
  · rfl

private def nonPrime {q : ℕ} (a : ZMod q) (x : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then 0 else residueClass a n) / (n : ℝ)^x

private theorem nonprime_le {q : ℕ} (a : ZMod q) {x : ℝ} (hx : 1 < x) (n : ℕ) :
    0 ≤ nonPrime a x n ∧ nonPrime a x n ≤ (if n.Prime then 0 else residueClass a n) / n := by
  have h : 0 ≤ (if n.Prime then 0 else residueClass a n) := by split <;> simp [residueClass_nonneg]
  refine ⟨div_nonneg h (Real.rpow_nonneg n.cast_nonneg _), ?_⟩
  obtain rfl|hn := n.eq_zero_or_pos
  · simp [nonPrime]
  · apply div_le_div_of_nonneg_left h (by exact_mod_cast hn)
    calc
      (n : ℝ) = (n : ℝ)^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx.le

private theorem split_term {q : ℕ} (a : ZMod q) (j : ℕ) (h : ℝ) (n : ℕ) :
    residueClass a n / (n : ℝ) ^ (1 + j*h) = primeTerm a j h n + nonPrime a (1 + j*h) n := by
  by_cases hp : n.Prime
  · have hpow := Real.rpow_add (by exact_mod_cast hp.pos : 0 < (n : ℝ)) 1 (j*h)
    simp [primeTerm, nonPrime, hp, residueClass, Set.indicator, vonMangoldt_apply_prime hp,
      Real.rpow_neg n.cast_nonneg, div_eq_mul_inv, mul_comm]
    split <;> simp_all [mul_comm, mul_assoc, mul_left_comm]
  · simp [primeTerm, nonPrime, hp]

private theorem primeTerm_summable {q : ℕ} (a : ZMod q) (j : ℕ) (hj : 0 < j) {h : ℝ} (hh : 0 < h) :
    Summable (primeTerm a j h) := by
  have hx : 1 < 1 + (j : ℝ)*h := by linarith [mul_pos (by exact_mod_cast hj : 0 < (j : ℝ)) hh]
  have hs : Summable (fun n : ℕ => residueClass a n / (n : ℝ)^(1+(j:ℝ)*h)) :=
    summable_real_of_abscissaOfAbsConv_lt ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx))
  have hn := Summable.of_nonneg_of_le (fun n => (nonprime_le a hx n).1)
    (fun n => (nonprime_le a hx n).2) (summable_residueClass_non_primes_div a)
  exact (hs.sub hn).congr (fun n => by simpa using sub_eq_of_eq_add (split_term a j h n))

private theorem prime_progression_mellin {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (j : ℕ) (hj : 0 < j) :
    Tendsto (fun h : ℝ => h * ∑' n, primeTerm a j h n) (𝓝[>] 0)
      (𝓝 ((q.totient : ℝ)⁻¹ / j)) := by
  have hjr : 0 < (j : ℝ) := by exact_mod_cast hj
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  let X (h : ℝ) : ℝ := 1 + j*h
  have ht : Tendsto X (𝓝[>] 0) (𝓝 1) := by
    simpa [X] using (tendsto_const_nhds (x := (1 : ℝ))).add (hid.const_mul (j : ℝ))
  have hw : Tendsto (fun h : ℝ => (X h : ℂ)) (𝓝[>] 0) (𝓝[{s : ℂ | 1 ≤ s.re}] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa [Function.comp_def] using continuous_ofReal.continuousAt.tendsto.comp ht
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with h hh
      change 1 ≤ 1 + (j : ℝ)*h
      linarith [mul_nonneg hjr.le (le_of_lt hh)]
  have hreg := (continuous_re.continuousAt.tendsto.comp
    (((continuousOn_LFunctionResidueClassAux a) 1 (show (1:ℂ) ∈ {s : ℂ | 1 ≤ s.re} by simp)).tendsto.comp hw))
  have hall : Tendsto (fun h : ℝ => h * ∑' n, residueClass a n / (n : ℝ) ^ (X h))
      (𝓝[>] 0) (𝓝 ((q.totient : ℝ)⁻¹ / j)) := by
    have hh := (hid.mul hreg).add (tendsto_const_nhds (x := (q.totient : ℝ)⁻¹ / j))
    simp only [zero_mul, zero_add] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with h hh
    have hpos : 0 < (j:ℝ)*h := mul_pos hjr hh
    rw [all_eq ha (show 1 < X h by dsimp [X]; linarith), mul_add]
    congr 1
    dsimp [X]
    rw [add_sub_cancel_left]
    field_simp [hjr.ne', (show 0 < h from hh).ne']
  let C := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n
  have hnon : Tendsto (fun h : ℝ => h * ∑' n, nonPrime a (X h) n) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun h : ℝ => h*C) _ (𝓝 0) by simpa using hid.mul_const C)
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with h hh
      have hx : 1 < X h := by dsimp [X]; linarith [mul_pos hjr hh]
      exact mul_nonneg (le_of_lt hh) (tsum_nonneg (fun n => (nonprime_le a hx n).1))
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with h hh
      have hx : 1 < X h := by dsimp [X]; linarith [mul_pos hjr hh]
      have hs := (summable_residueClass_non_primes_div a)
      exact mul_le_mul_of_nonneg_left ((Summable.of_nonneg_of_le (fun n => (nonprime_le a hx n).1)
        (fun n => (nonprime_le a hx n).2) hs).tsum_le_tsum (fun n => (nonprime_le a hx n).2) hs) (le_of_lt hh)
  apply (by simpa using hall.sub hnon : Tendsto _ _ (𝓝 ((q.totient : ℝ)⁻¹ / j))).congr'
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with h hh
  have hx : 1 < X h := by dsimp [X]; linarith [mul_pos hjr hh]
  have hs : Summable (fun n : ℕ => residueClass a n / (n : ℝ)^(X h)) :=
    summable_real_of_abscissaOfAbsConv_lt ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx))
  have hn := Summable.of_nonneg_of_le (fun n => (nonprime_le a hx n).1)
    (fun n => (nonprime_le a hx n).2) (summable_residueClass_non_primes_div a)
  rw [← mul_sub, ← hs.tsum_sub hn]
  congr 1
  apply tsum_congr
  intro n
  linarith [split_term a j h n]

end

open Real Finset Filter Topology

private def minorant (t : ℝ) : ℝ := t^12 * (1-t)^12 * (t-3/8) * (3/5-t)

/-- The numerator coefficients of 40 P(t), ordered from degree 12. -/
private def numerator (j : ℕ) : ℝ :=
  ([-9,147,-1102,5034,-15675,35233,-59004,74844,-72303,52965,-28974,11482,-3117,519,-40] : List ℝ)[j]?.getD 0

private lemma expand_minorant (t : ℝ) :
    minorant t = ∑ j ∈ range 15, numerator j / 40 * t^(j+12) := by
  norm_num [minorant,Finset.sum_range_succ,numerator]
  ring

private lemma minorant_moment :
    (∑ j ∈ range 15, numerator j / 40 / ((j:ℝ)+12)) = 1/10816624000 := by
  norm_num [Finset.sum_range_succ,numerator]

private lemma minorant_le_window {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) :
    minorant (exp (-log n / T)) ≤
      if exp (T/2) < (n:ℝ) ∧ (n:ℝ) ≤ exp T then 1 else 0 := by
  let t := exp (-log n / T)
  have ht := exp_pos (-log n / T)
  have hl : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn)
  have h1 : t ≤ 1 := exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) hT.le)
  have h0 : 0 ≤ t := ht.le
  have hfac : 0 ≤ t^12*(1-t)^12 := by positivity
  have hinside (hp : 0 < minorant t) : exp (T/2) < (n:ℝ) ∧ (n:ℝ) ≤ exp T := by
    have hh : 0 < (t-3/8)*(3/5-t) := by
      apply pos_of_mul_pos_right (a:=t^12*(1-t)^12) _ hfac
      simpa only [minorant,mul_assoc] using hp
    obtain ⟨hleft,hright⟩ : 3/8 < t ∧ t < 3/5 := by
      rcases mul_pos_iff.mp hh with h|h <;> constructor <;> linarith [h.1,h.2]
    have hlow : exp (-1) < 3/8 := by linarith [exp_neg_one_lt_d9]
    have hhigh : 3/5 < exp (-(1:ℝ)/2) := by
      rw [exp_half]
      apply (lt_sqrt (by norm_num)).2
      linarith [exp_neg_one_gt_d9]
    have hl' := exp_lt_exp.mp (hlow.trans hleft)
    have hr' := exp_lt_exp.mp (hright.trans hhigh)
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    rw [← exp_log hn']
    constructor
    · apply exp_lt_exp.mpr
      linarith [(div_lt_iff₀ hT).mp hr']
    · apply exp_le_exp.mpr
      linarith [(lt_div_iff₀ hT).mp hl']
  by_cases hp : 0 < minorant t
  · rw [ite_eq_left (hinside hp)]
    have hbase : t^12*(1-t)^12 ≤ 1 := (mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by linarith) (by linarith))).trans (pow_le_one₀ h0 h1)
    change t^12*(1-t)^12*(t-3/8)*(3/5-t) ≤ 1
    have : (t-3/8)*(3/5-t) ≤ 1 := by nlinarith [sq_nonneg (t - 39/80)]
    rw [mul_assoc (t^12*(1-t)^12)]
    exact (mul_le_mul_of_nonneg_left this hfac).trans (by simpa using hbase)
  · split <;> change minorant t ≤ _ <;> linarith


/-- Primes in the given residue class between exp(T/2) (excluded) and exp(T) (included). -/
def primeBand {m : ℕ} (a : ZMod m) (T : ℝ) : Finset ℕ :=
  (range (⌊exp T⌋₊+1)).filter (fun n : ℕ => exp (T/2) < (n:ℝ) ∧ (n:ZMod m) = a ∧ n.Prime)

private lemma band_dominates {m : ℕ} [NeZero m] (a : ZMod m) {T : ℝ} (hT : 0 < T) :
    (∑ j ∈ range 15, numerator j / 40 * ∑' n, primeTerm a (j+12) T⁻¹ n) ≤
    ∑ n ∈ primeBand a T, log n / n := by
  let f (j n : ℕ) := numerator j / 40 * primeTerm a (j+12) T⁻¹ n
  let g (n : ℕ) : ℝ := if n ∈ primeBand a T then log n / n else 0
  have hf (j : ℕ) : Summable (f j) :=
    (primeTerm_summable a _ (by omega) (inv_pos.2 hT)).mul_left _
  have hg : HasSum g (∑ n ∈ primeBand a T, log n / n) := by
    have h : HasSum g (∑ n ∈ primeBand a T, g n) := hasSum_sum_of_ne_finset_zero (f:=g) (s:=primeBand a T) (by intro n hn; simp [g,hn])
    simpa [g] using h
  have hb (n : ℕ) : (∑ j ∈ range 15, f j n) ≤ g n := by
    by_cases hp : n.Prime ∧ (n:ZMod m) = a
    · have hn : 0 < (n:ℝ) := by exact_mod_cast hp.1.pos
      have hw : 0 ≤ log (n:ℝ)/n := div_nonneg
        (log_nonneg (by exact_mod_cast hp.1.one_le)) hn.le
      have he (j : ℕ) : (n:ℝ)^(-((j+12:ℕ):ℝ)*T⁻¹) =
          exp (-log n / T)^(j+12) := by
        rw [rpow_def_of_pos hn, ← exp_nat_mul]; congr 1; ring
      have hrow : (∑ j ∈ range 15, f j n) = log n/n * minorant (exp (-log n/T)) := by
        rw [expand_minorant,mul_sum]; apply sum_congr rfl; intro j _
        simp only [f,primeTerm,ite_eq_left hp,← he,neg_mul]
        ring
      have hm : n ∈ primeBand a T ↔ exp (T/2) < (n:ℝ) ∧ (n:ℝ) ≤ exp T := by
        simp only [primeBand,mem_filter,mem_range,Nat.lt_succ_iff,
          Nat.le_floor_iff (exp_pos T).le,hp.1,hp.2,and_true]; exact and_comm
      rw [hrow]
      apply (mul_le_mul_of_nonneg_left (minorant_le_window hT hp.1.pos) hw).trans_eq
      by_cases hb : n ∈ primeBand a T
      · simp [g,hb,hm.mp hb]
      · simp [g,hb,mt hm.mpr hb]
    · have hnp : n ∉ primeBand a T := by
        intro h; have h' := (mem_filter.1 h).2; exact hp ⟨h'.2.2,h'.2.1⟩
      simp [f,g,primeTerm,hp,hnp]
  calc
    _ = ∑ j ∈ range 15, ∑' n, f j n := by simp [f,tsum_mul_left]
    _ = ∑' n, ∑ j ∈ range 15, f j n := (Summable.tsum_finsetSum (fun j _ => hf j)).symm
    _ ≤ ∑' n, g n := (summable_sum (s:=range 15) (fun j _ => hf j)).tsum_le_tsum hb hg.summable
    _ = _ := hg.tsum_eq

/-- Uniform positive logarithmic weight on every sufficiently large multiplicative half-window. -/
theorem prime_progression_window_mass {m : ℕ} [NeZero m] (a : ZMod m) (ha : IsUnit a) :
    ∀ᶠ T : ℝ in atTop, T / ((21633248000:ℝ) * (m.totient:ℝ)) ≤
      ∑ n ∈ primeBand a T, log n / n := by
  let M := (m.totient:ℝ)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Nat.totient_pos.2 (NeZero.pos m)
  have hlim (j : ℕ) : Tendsto (fun T : ℝ =>
      numerator j / 40 * (T⁻¹ * ∑' n, primeTerm a (j+12) T⁻¹ n)) atTop
      (𝓝 (numerator j / 40 * (M⁻¹ / (j+12:ℕ)))) :=
    ((prime_progression_mellin a ha (j+12) (by omega)).comp tendsto_inv_atTop_nhdsGT_zero).const_mul _
  have total := tendsto_finsetSum (range 15) (fun j _ => hlim j)
  have hv : (∑ j ∈ range 15, numerator j / 40 * (M⁻¹ / (j+12:ℕ))) =
      1 / (10816624000 * M) := by
    calc
      _ = (∑ j ∈ range 15, numerator j / 40 / ((j:ℝ)+12)) * M⁻¹ := by
        rw [sum_mul]; apply sum_congr rfl; intro j _; push_cast; ring
      _ = _ := by rw [minorant_moment]; ring
  rw [hv] at total
  have hlt : 1/(21633248000 * M) < 1/(10816624000 * M) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  filter_upwards [eventually_gt_atTop (0:ℝ),total.eventually_const_lt hlt] with T hT ht
  apply le_trans _ (band_dominates a hT)
  have he : (∑ j ∈ range 15, numerator j / 40 * (T⁻¹ * ∑' n, primeTerm a (j+12) T⁻¹ n)) =
      (∑ j ∈ range 15, numerator j / 40 * ∑' n, primeTerm a (j+12) T⁻¹ n) / T := by
    rw [sum_div]; apply sum_congr rfl; intro j _; ring
  rw [he] at ht
  simpa only [M,div_eq_mul_inv,one_mul,mul_comm] using (lt_div_iff₀ hT).mp ht |>.le

end D5.S3.CharacterSums.PrimeProgressionWindowMass
