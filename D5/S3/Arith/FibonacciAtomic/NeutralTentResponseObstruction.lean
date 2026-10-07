/- GID: D5/S3/Arith/FibonacciAtomic/NeutralTentResponseObstruction
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NeutralTentResponseObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Neutral finite tents obstruct a uniform square-root response bound. -/

import D5.S3.Arith.FibonacciAtomic.BinetPositiveResponse
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
open Filter
open D5.S3.Arith.FibonacciAtomic.BinetPositiveResponse

namespace D5.S3.Arith.FibonacciAtomic.NeutralTentResponseObstruction

set_option maxHeartbeats 2000000 in
-- One proof elaborates the full tent family, moment sums, and floor-sampling inequalities.
/-- At the actual Fibonacci response kernel, simultaneous exact zero moments,
a unit square-root norm, and unit adjacent increments still permit an unbounded
family of normalized responses at the original cubic cutoffs. The final
negation ranges over the entire moment-neutral input class. -/
theorem neutral_tent_response_obstruction :
    let q : ℝ := (Real.goldenRatio ^ 2)⁻¹
    ∃ hq : 0 < q,
    let k : ℕ → ℝ := response q hq
    let K : ℕ → ℝ := fun J => ∑ d ∈ Finset.Icc 1 J, k d
    let u : ℕ → ℝ := fun m => 1 / ((m : ℝ) * ((m : ℝ) + 1))
    let v : ℕ → ℝ := fun m => Real.log m / m - Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1)
    let ratios : (ℕ → ℝ) → Set ℝ := fun f => {x | ∃ m : ℕ, 1 ≤ m ∧ x = |f m| / Real.sqrt m}
    let input : (ℕ → ℝ) → Prop := fun f =>
      f 0 = 0 ∧
      Summable (fun m : ℕ => f (m + 1) * u (m + 1)) ∧
      Summable (fun m : ℕ => f (m + 1) * v (m + 1)) ∧
      (∑' m : ℕ, f (m + 1) * u (m + 1)) = 0 ∧
      (∑' m : ℕ, f (m + 1) * v (m + 1)) = 0 ∧
      (ratios f).Nonempty ∧ BddAbove (ratios f) ∧ sSup (ratios f) ≤ 1 ∧
      (∀ m : ℕ, |f m| ≤ Real.sqrt m) ∧
      (∀ m : ℕ, 1 ≤ m → |f m - f (m - 1)| ≤ 1)
    let original : (ℕ → ℝ) → Prop := fun f =>
      f 0 = 0 ∧
      (∑' m : ℕ, f (m + 1) * u (m + 1)) = 0 ∧
      (∑' m : ℕ, f (m + 1) * v (m + 1)) = 0 ∧
      (ratios f).Nonempty ∧ BddAbove (ratios f) ∧ sSup (ratios f) ≤ 1 ∧
      (∀ m : ℕ, 1 ≤ m → |f m - f (m - 1)| ≤ 1)
    let T : (ℕ → ℝ) → ℕ → ℝ := fun f N => ∑ d ∈ Finset.Icc 1 N, k d * f (N / d)
    (∃ f : ℕ → ℕ → ℝ, ∀ J : ℕ, 2 ≤ J →
      (Function.support (f J)).Finite ∧ input (f J) ∧
      K J / (16 * Real.sqrt J) ≤ T (f J) (64 * J ^ 3) / Real.sqrt ((64 * J ^ 3 : ℕ) : ℝ)) ∧
    Tendsto (fun J : ℕ => K J / (16 * Real.sqrt J)) atTop atTop ∧
    ¬ ∃ C : ℝ, ∀ f : ℕ → ℝ, original f → ∀ N : ℕ, 1 ≤ N →
      |T f N| / Real.sqrt N ≤ C := by
  dsimp only
  let q : ℝ := (Real.goldenRatio ^ 2)⁻¹
  have hphi : (3 / 2 : ℝ) < Real.goldenRatio := by
    have hp := Real.goldenRatio_pos
    have hs := Real.goldenRatio_sq
    nlinarith
  have hq : 0 < q := inv_pos.mpr (sq_pos_of_pos Real.goldenRatio_pos)
  have hqmax : q ≤ 2 / 5 := by
    dsimp [q]
    apply (inv_le_iff_one_le_mul₀ (sq_pos_of_pos Real.goldenRatio_pos)).mpr
    have hs := Real.goldenRatio_sq
    nlinarith
  refine ⟨hq, ?_⟩
  let k : ℕ → ℝ := response q hq
  let K : ℕ → ℝ := fun J => ∑ d ∈ Finset.Icc 1 J, k d
  let u : ℕ → ℝ := fun m => 1 / ((m : ℝ) * ((m : ℝ) + 1))
  let v : ℕ → ℝ := fun m => Real.log m / m - Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1)
  let r : ℕ → ℝ := fun m => ((m : ℝ) + 1) * Real.log m - (m : ℝ) * Real.log ((m : ℝ) + 1)
  have uv (m : ℕ) (hm : 1 ≤ m) : v m = u m * r m := by
    dsimp [u, v, r]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have upos (m : ℕ) (hm : 1 ≤ m) : 0 < u m := by
    dsimp [u]
    have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  have umono (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) : u n ≤ u m := by
    dsimp only [u]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    apply one_div_le_one_div_of_le (by positivity)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have rmono : StrictMono (fun n : ℕ => r (n + 1)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hn2 : (0 : ℝ) < n + 2 := by positivity
    have hn3 : (0 : ℝ) < n + 3 := by positivity
    have hlog : Real.log (((n : ℝ) + 1) * ((n : ℝ) + 3)) <
        Real.log (((n : ℝ) + 2) ^ 2) := by
      apply Real.log_lt_log (mul_pos hn hn3)
      nlinarith
    rw [Real.log_mul hn.ne' hn3.ne', Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    norm_num [r, Nat.cast_add, add_assoc]
    nlinarith [mul_pos hn2 (sub_pos.mpr hlog)]
  have rlt (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) : r m < r n := by
    have h := rmono (show m - 1 < n - 1 by omega)
    simpa [Nat.sub_add_cancel hm, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  obtain ⟨hsE, hsP, hgap, hbudget, hk1, hbounds, hstrict⟩ := binet_response_contract q hq hqmax
  have hkone : k 1 = 0 := hk1
  have hE : 0 ≤ negativeTail q := by simpa using (hbudget 1).1
  have hP : 0 ≤ positiveTail q := by simpa using (hbudget 1).2
  have hb : 0 < beta q 1 := by
    have hpositive : 0 < 94 * q / 2205 := by positivity
    linarith
  have hD : 0 < beta q 1 - negativeTail q := by
    have hpositive : 0 < 94 * q / 2205 := by positivity
    linarith
  let c : ℝ := (beta q 1 - negativeTail q - positiveTail q) /
    (beta q 1 * (beta q 1 - negativeTail q))
  have hc : 0 < c := div_pos (by
    have hpositive : 0 < 94 * q / 2205 := by positivity
    linarith) (mul_pos hb hD)
  have klower (n : ℕ) (hn : 1 ≤ n) : c * Real.log n ≤ k n := (hbounds n (by omega)).1
  have knonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ k n :=
    (mul_nonneg hc.le (Real.log_nonneg (by exact_mod_cast hn))).trans (klower n hn)
  have geometry (J j : ℕ) (hJ : 2 ≤ J) (hj : 2 ≤ j) (hjJ : j ≤ J) :
      let N := 64 * J ^ 3
      let m := N / j
      let R := ⌊Real.sqrt (m : ℝ) / 8⌋₊
      64 * J ^ 2 ≤ m ∧ J ≤ R ∧ 64 * R ^ 2 ≤ m ∧
      64 * J * R ≤ m ∧ 3 * R ≤ m ∧ m + 3 * R ≤ N ∧
      N / (m - 3 * R + 1) = j ∧ N / (m + 3 * R) = j - 1 := by
    let N := 64 * J ^ 3
    let m := N / j
    let R := ⌊Real.sqrt (m : ℝ) / 8⌋₊
    change 64 * J ^ 2 ≤ m ∧ J ≤ R ∧ 64 * R ^ 2 ≤ m ∧
      64 * J * R ≤ m ∧ 3 * R ≤ m ∧ m + 3 * R ≤ N ∧
      N / (m - 3 * R + 1) = j ∧ N / (m + 3 * R) = j - 1
    have hj0 : 0 < j := by omega
    have hmJ : 64 * J ^ 2 ≤ m := by
      apply (Nat.le_div_iff_mul_le hj0).mpr
      dsimp [N]
      nlinarith [Nat.mul_le_mul_left (64 * J ^ 2) hjJ]
    have hJr : (J : ℝ) ≤ Real.sqrt m / 8 := by
      have hsq := Real.sq_sqrt (Nat.cast_nonneg m)
      have hsqJ : (64 : ℝ) * J ^ 2 ≤ m := by exact_mod_cast hmJ
      have hnonneg := Real.sqrt_nonneg (m : ℝ)
      nlinarith [show (0 : ℝ) ≤ J from Nat.cast_nonneg J]
    have hRJ : J ≤ R := (Nat.le_floor_iff (by positivity)).mpr hJr
    have hRr : (R : ℝ) ≤ Real.sqrt m / 8 := Nat.floor_le (by positivity)
    have hRsq : 64 * R ^ 2 ≤ m := by
      have hsq := Real.sq_sqrt (Nat.cast_nonneg m)
      have hnonneg := Real.sqrt_nonneg (m : ℝ)
      have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
      have he : (64 : ℝ) * R ^ 2 ≤ m := by nlinarith
      exact_mod_cast he
    have hJR : 64 * J * R ≤ m := by
      have hsq := Real.sq_sqrt (Nat.cast_nonneg m)
      have hnonneg := Real.sqrt_nonneg (m : ℝ)
      have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
      have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
      have hprod := mul_nonneg (sub_nonneg.mpr hJr) hnonneg
      have hprod2 := mul_nonneg hJ0 (sub_nonneg.mpr hRr)
      have he : (64 : ℝ) * J * R ≤ m := by nlinarith
      exact_mod_cast he
    have hR0 : 0 < R := by omega
    have hmR : 3 * R ≤ m := by nlinarith
    have hdivlo : m * j ≤ N := Nat.div_mul_le_self N j
    have hdivhi : N < (m + 1) * j := (Nat.div_lt_iff_lt_mul hj0).mp (Nat.lt_succ_self m)
    have hmN : m + 3 * R ≤ N := by nlinarith
    have ha0 : 0 < m - 3 * R + 1 := by omega
    have ha : m - 3 * R + 1 + 3 * R = m + 1 := by omega
    have hqa : N / (m - 3 * R + 1) = j := by
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul ha0).mpr
        nlinarith
      · apply (Nat.le_div_iff_mul_le ha0).mpr
        nlinarith
    have hb0 : 0 < m + 3 * R := by omega
    have hqb : N / (m + 3 * R) = j - 1 := by
      apply Nat.le_antisymm
      · have hx : N / (m + 3 * R) < j := by
          apply (Nat.div_lt_iff_lt_mul hb0).mpr
          nlinarith
        omega
      · apply (Nat.le_div_iff_mul_le hb0).mpr
        have hjsub : j - 1 + 1 = j := by omega
        nlinarith
    exact ⟨hmJ, hRJ, hRsq, hJR, hmR, hmN, hqa, hqb⟩
  have divergence : Tendsto (fun J : ℕ => K J / (16 * Real.sqrt J)) atTop atTop := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK (J : ℕ) (hJ : 2 ≤ J) : ((J : ℝ) - 1) * (c * Real.log 2) ≤ K J := by
      have hsplit : Finset.Icc 1 J = insert 1 (Finset.Icc 2 J) := by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hk : k 1 = 0 := hk1
      dsimp only [K]
      rw [hsplit, Finset.sum_insert (by simp), hk, zero_add]
      calc
        _ = ∑ d ∈ Finset.Icc 2 J, c * Real.log 2 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          have hcast : ((J + 1 - 2 : ℕ) : ℝ) = (J : ℝ) - 1 := by
            rw [show J + 1 - 2 = J - 1 by omega, Nat.cast_sub (by omega : 1 ≤ J)]
            norm_num
          rw [hcast]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d hd
          have hd2 := (Finset.mem_Icc.mp hd).1
          exact (mul_le_mul_of_nonneg_left
            (Real.log_le_log (by norm_num) (by exact_mod_cast hd2)) hc.le).trans
            (klower d (by omega))
    have hscale : Tendsto (fun J : ℕ => (c * Real.log 2 / 32) * Real.sqrt J) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
    apply tendsto_atTop_mono' atTop _ hscale
    filter_upwards [eventually_ge_atTop 2] with J hJ
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
    have hs : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr hJ0
    apply (le_div_iff₀ (by positivity : 0 < 16 * Real.sqrt J)).mpr
    have hj : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    have hs2 := Real.sq_sqrt hJ0.le
    have hc2 : 0 < c * Real.log 2 := mul_pos hc hlog2
    have hk := hK J hJ
    have he : (c * Real.log 2 / 32) * Real.sqrt J * (16 * Real.sqrt J) =
        (J : ℝ) / 2 * (c * Real.log 2) := by
      calc
        _ = (Real.sqrt (J : ℝ)) ^ 2 * (c * Real.log 2) / 2 := by ring
        _ = _ := by rw [hs2]; ring
    rw [he]
    nlinarith only [hk, mul_nonneg (by linarith : (0 : ℝ) ≤ J / 2 - 1) hc2.le]
  let tent : ℕ → ℕ → ℕ → ℝ := fun R a n =>
    max ((R : ℝ) - |(n : ℝ) - ((a : ℝ) + R)|) 0
  let height : ℕ → ℕ → ℝ := fun R i => max ((R : ℝ) - |(i : ℝ) - R|) 0
  have tent_nonneg (R a n : ℕ) : 0 ≤ tent R a n := le_max_right _ _
  have tent_le (R a n : ℕ) : tent R a n ≤ R := by
    apply max_le
    · exact sub_le_self _ (abs_nonneg _)
    · exact Nat.cast_nonneg R
  have height_pos (R i : ℕ) (hR : 1 ≤ R) (hi : i ∈ Finset.Icc 1 (2 * R - 1)) :
      0 < height R i := by
    obtain ⟨hi0, hiR⟩ := Finset.mem_Icc.mp hi
    have hile : i < 2 * R := by omega
    have hil : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hiu : (i : ℝ) < 2 * R := by exact_mod_cast hile
    apply lt_max_of_lt_left
    have hh : |(i : ℝ) - R| < R := abs_lt.mpr (by constructor <;> linarith)
    linarith
  have tent_offset (R a i : ℕ) : tent R a (a + i) = height R i := by
    dsimp only [tent, height]
    rw [Nat.cast_add]
    congr 2
    congr 1
    ring
  have tent_support (R a n : ℕ) (hn : tent R a n ≠ 0) : a < n ∧ n < a + 2 * R := by
    have hp : 0 < tent R a n := lt_of_le_of_ne (tent_nonneg R a n) (Ne.symm hn)
    have hh : (R : ℝ) - |(n : ℝ) - ((a : ℝ) + R)| > 0 := by
      exact (lt_max_iff.mp hp).resolve_right (lt_irrefl _)
    have hr : |(n : ℝ) - ((a : ℝ) + R)| < R := by linarith
    have hh := abs_lt.mp hr
    constructor
    · exact_mod_cast (show (a : ℝ) < n by linarith)
    · have : (n : ℝ) < (a + 2 * R : ℕ) := by push_cast; linarith
      exact_mod_cast this
  have tent_lip (R a n : ℕ) (hn : 1 ≤ n) : |tent R a n - tent R a (n - 1)| ≤ 1 := by
    calc
      _ ≤ |((R : ℝ) - |(n : ℝ) - ((a : ℝ) + R)|) -
          ((R : ℝ) - |((n - 1 : ℕ) : ℝ) - ((a : ℝ) + R)|)| :=
        abs_max_sub_max_le_abs _ _ _
      _ = |(|(n : ℝ) - ((a : ℝ) + R)| - |((n - 1 : ℕ) : ℝ) - ((a : ℝ) + R)|)| := by
        rw [show ((R : ℝ) - |(n : ℝ) - ((a : ℝ) + R)|) -
          ((R : ℝ) - |((n - 1 : ℕ) : ℝ) - ((a : ℝ) + R)|) =
          -(|(n : ℝ) - ((a : ℝ) + R)| - |((n - 1 : ℕ) : ℝ) - ((a : ℝ) + R)|) by ring,
          abs_neg]
      _ ≤ |((n : ℝ) - ((a : ℝ) + R)) - (((n - 1 : ℕ) : ℝ) - ((a : ℝ) + R))| :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = 1 := by rw [Nat.cast_sub hn]; norm_num
  have tent_expand (R a n : ℕ) (hR : 1 ≤ R) :
      tent R a n = ∑ i ∈ Finset.Icc 1 (2 * R - 1),
        if n = a + i then height R i else 0 := by
    by_cases hn : tent R a n = 0
    · rw [hn]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      split_ifs with he
      · have heq := tent_offset R a i
        have hpos := height_pos R i hR hi
        rw [← he] at heq
        rw [hn] at heq
        linarith
      · rfl
    · obtain ⟨han, hnR⟩ := tent_support R a n hn
      have hi : n - a ∈ Finset.Icc 1 (2 * R - 1) := by
        apply Finset.mem_Icc.mpr
        constructor <;> omega
      have he : n = a + (n - a) := by omega
      rw [Finset.sum_eq_single (n - a)]
      · rw [if_pos he]
        calc
          tent R a n = tent R a (a + (n - a)) := by congr 1
          _ = height R (n - a) := tent_offset R a (n - a)
      · intro i hi hine
        rw [if_neg]
        intro h
        omega
      · exact fun h => False.elim (h hi)
  have tent_moment (R a : ℕ) (hR : 1 ≤ R) (w : ℕ → ℝ) :
      Summable (fun n : ℕ => tent R a (n + 1) * w (n + 1)) ∧
      (∑' n : ℕ, tent R a (n + 1) * w (n + 1)) =
        ∑ i ∈ Finset.Icc 1 (2 * R - 1), height R i * w (a + i) := by
    let I := Finset.Icc 1 (2 * R - 1)
    have hdelta (i : ℕ) (hi : i ∈ I) :
        (fun n : ℕ => if n + 1 = a + i then height R i * w (a + i) else 0) =
        (fun n : ℕ => if n = a + i - 1 then height R i * w (a + i) else 0) := by
      funext n
      have hi0 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hh : n + 1 = a + i ↔ n = a + i - 1 := by omega
      simp only [hh]
    have hsum : (fun n : ℕ => tent R a (n + 1) * w (n + 1)) =
        (fun n : ℕ => ∑ i ∈ I, if n + 1 = a + i then height R i * w (a + i) else 0) := by
      funext n
      rw [tent_expand R a (n + 1) hR, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with he
      · rw [he]
      · simp
    have hs (i : ℕ) (hi : i ∈ I) : Summable
        (fun n : ℕ => if n + 1 = a + i then height R i * w (a + i) else 0) := by
      rw [hdelta i hi]
      apply summable_of_ne_finset_zero (s := {a + i - 1})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      exact if_neg hn
    constructor
    · rw [hsum]
      exact summable_sum hs
    · rw [hsum, Summable.tsum_finsetSum hs]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdelta i hi, tsum_ite_eq]
  let U : ℕ → ℕ → ℝ := fun R a => ∑ i ∈ Finset.Icc 1 (2 * R - 1), height R i * u (a + i)
  let V : ℕ → ℕ → ℝ := fun R a => ∑ i ∈ Finset.Icc 1 (2 * R - 1), height R i * v (a + i)
  have Upos (R a : ℕ) (hR : 1 ≤ R) : 0 < U R a := by
    apply Finset.sum_pos
    · intro i hi
      exact mul_pos (height_pos R i hR hi)
        (upos (a + i) (by have := (Finset.mem_Icc.mp hi).1; omega))
    · exact ⟨R, Finset.mem_Icc.mpr (by constructor <;> omega)⟩
  have Umono (R a b : ℕ) (hab : a ≤ b) : U R b ≤ U R a := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (umono (a + i) (b + i) (by have := (Finset.mem_Icc.mp hi).1; omega) (by omega))
      (le_max_right _ _)
  have average_order (R a b : ℕ) (hR : 1 ≤ R) (hab : a + 2 * R ≤ b) :
      V R a / U R a < V R b / U R b := by
    have hI : (Finset.Icc 1 (2 * R - 1)).Nonempty :=
      ⟨R, Finset.mem_Icc.mpr (by constructor <;> omega)⟩
    have hleft : V R a < r (a + 2 * R) * U R a := by
      dsimp only [V, U]
      rw [Finset.mul_sum]
      apply Finset.sum_lt_sum_of_nonempty hI
      intro i hi
      have hi0 := (Finset.mem_Icc.mp hi).1
      have hiR := (Finset.mem_Icc.mp hi).2
      have hpos := mul_pos (height_pos R i hR hi) (upos (a + i) (by omega))
      have hlt := rlt (a + i) (a + 2 * R) (by omega) (by omega)
      rw [uv (a + i) (by omega)]
      nlinarith [mul_pos hpos (sub_pos.mpr hlt)]
    have hright : r (a + 2 * R) * U R b < V R b := by
      dsimp only [V, U]
      rw [Finset.mul_sum]
      apply Finset.sum_lt_sum_of_nonempty hI
      intro i hi
      have hi0 := (Finset.mem_Icc.mp hi).1
      have hpos := mul_pos (height_pos R i hR hi) (upos (b + i) (by omega))
      have hlt := rlt (a + 2 * R) (b + i) (by omega) (by omega)
      rw [uv (b + i) (by omega)]
      nlinarith [mul_pos hpos (sub_pos.mpr hlt)]
    exact ((div_lt_iff₀ (Upos R a hR)).mpr hleft).trans
      ((lt_div_iff₀ (Upos R b hR)).mpr hright)
  have Uratio (R a : ℕ) (hR : 1 ≤ R) (ha : 8 * R ≤ a + 1) :
      U R a < 2 * U R (a + 2 * R) := by
    dsimp only [U]
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty ⟨R, Finset.mem_Icc.mpr (by constructor <;> omega)⟩
    intro i hi
    have hi0 := (Finset.mem_Icc.mp hi).1
    have hx : (8 : ℝ) * R ≤ (a + i : ℕ) := by exact_mod_cast (by omega : 8 * R ≤ a + i)
    have hx0 : (0 : ℝ) < (a + i : ℕ) := by exact_mod_cast (by omega : 0 < a + i)
    have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
    have he : ((a + 2 * R + i : ℕ) : ℝ) = (a + i : ℕ) + 2 * R := by push_cast; ring
    have hden : ((a + 2 * R + i : ℕ) : ℝ) * ((a + 2 * R + i : ℕ) + 1) <
        2 * ((a + i : ℕ) : ℝ) * ((a + i : ℕ) + 1) := by
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) hx0.le,
        mul_nonneg (sub_nonneg.mpr hx) hR0.le]
    have hu : u (a + i) < 2 * u (a + 2 * R + i) := by
      dsimp only [u]
      have hd0 : (0 : ℝ) < ((a + i : ℕ) : ℝ) * ((a + i : ℕ) + 1) := by positivity
      have hd1 : (0 : ℝ) < ((a + 2 * R + i : ℕ) : ℝ) *
          ((a + 2 * R + i : ℕ) + 1) := by rw [he]; positivity
      have h : (1 : ℝ) / (((a + i : ℕ) : ℝ) * ((a + i : ℕ) + 1)) <
          2 / (((a + 2 * R + i : ℕ) : ℝ) * ((a + 2 * R + i : ℕ) + 1)) :=
        (div_lt_div_iff₀ hd0 hd1).mpr (by simpa [mul_assoc] using hden)
      simpa only [div_eq_mul_inv, one_mul] using h
    have hp := height_pos R i hR hi
    nlinarith [mul_pos hp (sub_pos.mpr hu)]
  have coefficients (R A : ℕ) (hR : 1 ≤ R) (hA : 8 * R ≤ A + 2 * R + 1) :
      ∃ α η : ℝ, 0 < α ∧ α < 1 ∧ 0 < η ∧ η < 2 ∧
        U R (A + 2 * R) - α * U R A - η * U R (A + 4 * R) = 0 ∧
        V R (A + 2 * R) - α * V R A - η * V R (A + 4 * R) = 0 := by
    let rm := V R A / U R A
    let r0 := V R (A + 2 * R) / U R (A + 2 * R)
    let rp := V R (A + 4 * R) / U R (A + 4 * R)
    have hm0 : rm < r0 := average_order R A (A + 2 * R) hR le_rfl
    have h0p : r0 < rp := average_order R (A + 2 * R) (A + 4 * R) hR (by omega)
    let t := (rp - r0) / (rp - rm)
    have hden : 0 < rp - rm := by linarith
    have ht : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    let α := U R (A + 2 * R) * t / U R A
    let η := U R (A + 2 * R) * (1 - t) / U R (A + 4 * R)
    have hUm := Upos R A hR
    have hU0 := Upos R (A + 2 * R) hR
    have hUp := Upos R (A + 4 * R) hR
    have hα : 0 < α := div_pos (mul_pos hU0 ht) hUm
    have hη : 0 < η := div_pos (mul_pos hU0 (by linarith)) hUp
    have hα1 : α < 1 := by
      apply (div_lt_one hUm).mpr
      have hle := Umono R A (A + 2 * R) (by omega)
      nlinarith only [hle, mul_pos hU0 (sub_pos.mpr ht1)]
    have hη2 : η < 2 := by
      apply (div_lt_iff₀ hUp).mpr
      have hle := Uratio R (A + 2 * R) hR hA
      have he : A + 2 * R + 2 * R = A + 4 * R := by omega
      rw [he] at hle
      nlinarith only [hle, mul_pos hU0 ht]
    have hαU : α * U R A = U R (A + 2 * R) * t := div_mul_cancel₀ _ hUm.ne'
    have hηU : η * U R (A + 4 * R) = U R (A + 2 * R) * (1 - t) := div_mul_cancel₀ _ hUp.ne'
    have hV : V R (A + 2 * R) - α * V R A - η * V R (A + 4 * R) = 0 := by
      have hm : V R A = U R A * rm := by dsimp [rm]; field_simp
      have h0 : V R (A + 2 * R) = U R (A + 2 * R) * r0 := by dsimp [r0]; field_simp
      have hp : V R (A + 4 * R) = U R (A + 4 * R) * rp := by dsimp [rp]; field_simp
      rw [hm, h0, hp]
      have hbalance : t * rm + (1 - t) * rp = r0 := by
        dsimp [t]
        field_simp
        ring
      calc
        _ = U R (A + 2 * R) * (r0 - (t * rm + (1 - t) * rp)) := by
          rw [← mul_assoc α, ← mul_assoc η, hαU, hηU]
          ring
        _ = 0 := by rw [hbalance]; ring
    exact ⟨α, η, hα, hα1, hη, hη2, by rw [hαU, hηU]; ring, hV⟩
  have pulse (R A : ℕ) (hR : 1 ≤ R) (hA : 8 * R ≤ A + 2 * R + 1)
      (hsq : R ^ 2 ≤ A + 1) :
      ∃ h : ℕ → ℝ,
        (∀ n, h n ≠ 0 → A < n ∧ n < A + 6 * R) ∧
        (∀ n, |h n| ≤ Real.sqrt n) ∧
        (∀ n, 1 ≤ n → |h n - h (n - 1)| ≤ 1) ∧
        Summable (fun n : ℕ => h (n + 1) * u (n + 1)) ∧
        Summable (fun n : ℕ => h (n + 1) * v (n + 1)) ∧
        (∑' n : ℕ, h (n + 1) * u (n + 1)) = 0 ∧
        (∑' n : ℕ, h (n + 1) * v (n + 1)) = 0 ∧
        h (A + 3 * R) = R / 2 := by
    obtain ⟨α, η, hα, hα1, hη, hη2, hU, hV⟩ := coefficients R A hR hA
    let h : ℕ → ℝ := fun n =>
      (tent R (A + 2 * R) n - α * tent R A n - η * tent R (A + 4 * R) n) / 2
    have hsupport (n : ℕ) (hn : h n ≠ 0) : A < n ∧ n < A + 6 * R := by
      by_contra hbad
      have hzero (a : ℕ) (ha : A ≤ a) (haR : a + 2 * R ≤ A + 6 * R) : tent R a n = 0 := by
        by_contra hn0
        have hs := tent_support R a n hn0
        omega
      have hz0 := hzero A le_rfl (by omega)
      have hz1 := hzero (A + 2 * R) (by omega) (by omega)
      have hz2 := hzero (A + 4 * R) (by omega) (by omega)
      apply hn
      simp [h, hz0, hz1, hz2]
    have active (n a : ℕ) (hn : 1 ≤ n)
        (ha : tent R a n ≠ 0 ∨ tent R a (n - 1) ≠ 0) : a < n ∧ n ≤ a + 2 * R := by
      rcases ha with ha | ha
      · have hs := tent_support R a n ha
        omega
      · have hs := tent_support R a (n - 1) ha
        omega
    have zero_pair (n a b : ℕ) (hn : 1 ≤ n)
        (ha : tent R a n ≠ 0 ∨ tent R a (n - 1) ≠ 0)
        (hab : a + 2 * R ≤ b ∨ b + 2 * R ≤ a) :
        tent R b n = 0 ∧ tent R b (n - 1) = 0 := by
      have hs := active n a hn ha
      constructor <;> by_contra hnonzero
      · have ht := active n b hn (Or.inl hnonzero)
        omega
      · have ht := active n b hn (Or.inr hnonzero)
        omega
    have hlip (n : ℕ) (hn : 1 ≤ n) : |h n - h (n - 1)| ≤ 1 := by
      by_cases ha : tent R A n ≠ 0 ∨ tent R A (n - 1) ≠ 0
      · obtain ⟨hm, hm'⟩ := zero_pair n A (A + 2 * R) hn ha (Or.inl (by omega))
        obtain ⟨hp, hp'⟩ := zero_pair n A (A + 4 * R) hn ha (Or.inl (by omega))
        have ht := tent_lip R A n hn
        have he : h n - h (n - 1) = -(α / 2) *
            (tent R A n - tent R A (n - 1)) := by simp [h, hm, hm', hp, hp']; ring
        rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < α / 2)]
        nlinarith only [ht, hα1, hα, abs_nonneg (tent R A n - tent R A (n - 1))]
      · have ha0 : tent R A n = 0 ∧ tent R A (n - 1) = 0 := by simpa only [not_or, not_not] using ha
        by_cases hm : tent R (A + 2 * R) n ≠ 0 ∨ tent R (A + 2 * R) (n - 1) ≠ 0
        · obtain ⟨hp, hp'⟩ := zero_pair n (A + 2 * R) (A + 4 * R) hn hm (Or.inl (by omega))
          have ht := tent_lip R (A + 2 * R) n hn
          have he : h n - h (n - 1) =
              (tent R (A + 2 * R) n - tent R (A + 2 * R) (n - 1)) / 2 := by
            simp [h, ha0.1, ha0.2, hp, hp']; ring
          rw [he, abs_div]
          norm_num
          linarith
        · have hm0 : tent R (A + 2 * R) n = 0 ∧ tent R (A + 2 * R) (n - 1) = 0 := by
            simpa only [not_or, not_not] using hm
          have ht := tent_lip R (A + 4 * R) n hn
          have he : h n - h (n - 1) = -(η / 2) *
              (tent R (A + 4 * R) n - tent R (A + 4 * R) (n - 1)) := by
            simp [h, ha0.1, ha0.2, hm0.1, hm0.2]; ring
          rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < η / 2)]
          nlinarith only [ht, hη2, hη,
            abs_nonneg (tent R (A + 4 * R) n - tent R (A + 4 * R) (n - 1))]
    have hmag (n : ℕ) : |h n| ≤ R := by
      by_cases hn : n = 0
      · subst n
        have hz : h 0 = 0 := by by_contra hz; have hs := hsupport 0 hz; omega
        simp [hz]
      have hn1 : 1 ≤ n := by omega
      by_cases ha : tent R A n ≠ 0
      · obtain ⟨hm, hm'⟩ := zero_pair n A (A + 2 * R) hn1 (Or.inl ha) (Or.inl (by omega))
        obtain ⟨hp, hp'⟩ := zero_pair n A (A + 4 * R) hn1 (Or.inl ha) (Or.inl (by omega))
        have he : h n = -(α / 2) * tent R A n := by simp [h, hm, hp]; ring
        rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < α / 2),
          abs_of_nonneg (tent_nonneg R A n)]
        calc
          _ ≤ 1 * (R : ℝ) := mul_le_mul (by linarith : α / 2 ≤ 1)
            (tent_le R A n) (tent_nonneg R A n) (by norm_num)
          _ = _ := one_mul _
      · have ha0 : tent R A n = 0 := not_ne_iff.mp ha
        by_cases hm : tent R (A + 2 * R) n ≠ 0
        · obtain ⟨hp, hp'⟩ := zero_pair n (A + 2 * R) (A + 4 * R) hn1
            (Or.inl hm) (Or.inl (by omega))
          have he : h n = tent R (A + 2 * R) n / 2 := by simp [h, ha0, hp]
          rw [he, abs_div, abs_of_nonneg (tent_nonneg R (A + 2 * R) n)]
          norm_num
          have ht := tent_le R (A + 2 * R) n
          have hrr : (0 : ℝ) ≤ R := Nat.cast_nonneg R
          linarith
        · have hm0 : tent R (A + 2 * R) n = 0 := not_ne_iff.mp hm
          have he : h n = -(η / 2) * tent R (A + 4 * R) n := by simp [h, ha0, hm0]; ring
          rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < η / 2),
            abs_of_nonneg (tent_nonneg R (A + 4 * R) n)]
          calc
            _ ≤ 1 * (R : ℝ) := mul_le_mul (by linarith : η / 2 ≤ 1)
              (tent_le R (A + 4 * R) n) (tent_nonneg R (A + 4 * R) n) (by norm_num)
            _ = _ := one_mul _
    have henvelope (n : ℕ) : |h n| ≤ Real.sqrt n := by
      by_cases hn : h n = 0
      · simp [hn]
      · have hs := hsupport n hn
        have hsqn : R ^ 2 ≤ n := by omega
        have hsqr : (R : ℝ) ^ 2 ≤ n := by exact_mod_cast hsqn
        exact (hmag n).trans (Real.le_sqrt_of_sq_le hsqr)
    have moments (w : ℕ → ℝ) :
        Summable (fun n : ℕ => h (n + 1) * w (n + 1)) ∧
        (∑' n : ℕ, h (n + 1) * w (n + 1)) =
          ((∑ i ∈ Finset.Icc 1 (2 * R - 1), height R i * w (A + 2 * R + i)) -
           α * (∑ i ∈ Finset.Icc 1 (2 * R - 1), height R i * w (A + i)) -
           η * (∑ i ∈ Finset.Icc 1 (2 * R - 1), height R i * w (A + 4 * R + i))) / 2 := by
      obtain ⟨hsm, hem⟩ := tent_moment R A hR w
      obtain ⟨hs0, he0⟩ := tent_moment R (A + 2 * R) hR w
      obtain ⟨hsp, hep⟩ := tent_moment R (A + 4 * R) hR w
      have he : (fun n : ℕ => h (n + 1) * w (n + 1)) =
          (fun n : ℕ => (tent R (A + 2 * R) (n + 1) * w (n + 1) -
            α * (tent R A (n + 1) * w (n + 1)) -
            η * (tent R (A + 4 * R) (n + 1) * w (n + 1))) / 2) := by
        funext n
        dsimp [h]
        ring
      constructor
      · rw [he]
        exact ((hs0.sub (hsm.mul_left α)).sub (hsp.mul_left η)).div_const 2
      · rw [he, tsum_div_const,
          (hs0.sub (hsm.mul_left α)).tsum_sub (hsp.mul_left η),
          hs0.tsum_sub (hsm.mul_left α), tsum_mul_left, tsum_mul_left, hem, he0, hep]
    have hmom0 : (∑' n : ℕ, h (n + 1) * u (n + 1)) = 0 := by
      rw [(moments u).2]
      change (U R (A + 2 * R) - α * U R A - η * U R (A + 4 * R)) / 2 = 0
      rw [hU, zero_div]
    have hmom1 : (∑' n : ℕ, h (n + 1) * v (n + 1)) = 0 := by
      rw [(moments v).2]
      change (V R (A + 2 * R) - α * V R A - η * V R (A + 4 * R)) / 2 = 0
      rw [hV, zero_div]
    have hcenter : h (A + 3 * R) = R / 2 := by
      have hl : tent R A (A + 3 * R) = 0 := by
        by_contra hn
        have hs := tent_support R A (A + 3 * R) hn
        omega
      have hp : tent R (A + 4 * R) (A + 3 * R) = 0 := by
        by_contra hn
        have hs := tent_support R (A + 4 * R) (A + 3 * R) hn
        omega
      have hm : tent R (A + 2 * R) (A + 3 * R) = R := by
        have he : A + 3 * R = (A + 2 * R) + R := by omega
        rw [he, tent_offset]
        simp [height]
      simp [h, hl, hp, hm]
    exact ⟨h, hsupport, henvelope, hlip, (moments u).1, (moments v).1, hmom0, hmom1, hcenter⟩
  let ratios : (ℕ → ℝ) → Set ℝ := fun f => {x | ∃ m : ℕ, 1 ≤ m ∧ x = |f m| / Real.sqrt m}
  let input : (ℕ → ℝ) → Prop := fun f =>
    f 0 = 0 ∧ Summable (fun m : ℕ => f (m + 1) * u (m + 1)) ∧
    Summable (fun m : ℕ => f (m + 1) * v (m + 1)) ∧
    (∑' m : ℕ, f (m + 1) * u (m + 1)) = 0 ∧
    (∑' m : ℕ, f (m + 1) * v (m + 1)) = 0 ∧
    (ratios f).Nonempty ∧ BddAbove (ratios f) ∧ sSup (ratios f) ≤ 1 ∧
    (∀ m : ℕ, |f m| ≤ Real.sqrt m) ∧
    (∀ m : ℕ, 1 ≤ m → |f m - f (m - 1)| ≤ 1)
  let original : (ℕ → ℝ) → Prop := fun f =>
    f 0 = 0 ∧
    (∑' m : ℕ, f (m + 1) * u (m + 1)) = 0 ∧
    (∑' m : ℕ, f (m + 1) * v (m + 1)) = 0 ∧
    (ratios f).Nonempty ∧ BddAbove (ratios f) ∧ sSup (ratios f) ≤ 1 ∧
    (∀ m : ℕ, 1 ≤ m → |f m - f (m - 1)| ≤ 1)
  let T : (ℕ → ℝ) → ℕ → ℝ := fun f N => ∑ d ∈ Finset.Icc 1 N, k d * f (N / d)
  change (∃ f : ℕ → ℕ → ℝ, ∀ J : ℕ, 2 ≤ J →
    (Function.support (f J)).Finite ∧ input (f J) ∧
    K J / (16 * Real.sqrt J) ≤ T (f J) (64 * J ^ 3) / Real.sqrt ((64 * J ^ 3 : ℕ) : ℝ)) ∧
    Tendsto (fun J : ℕ => K J / (16 * Real.sqrt J)) atTop atTop ∧
    ¬ ∃ C : ℝ, ∀ f : ℕ → ℝ, original f → ∀ N : ℕ, 1 ≤ N → |T f N| / Real.sqrt N ≤ C
  have construct (J : ℕ) (hJ : 2 ≤ J) : ∃ f : ℕ → ℝ,
      (Function.support f).Finite ∧ input f ∧
      K J / (16 * Real.sqrt J) ≤ T f (64 * J ^ 3) / Real.sqrt ((64 * J ^ 3 : ℕ) : ℝ) := by
    classical
    let N := 64 * J ^ 3
    let m : ℕ → ℕ := fun j => N / j
    let R : ℕ → ℕ := fun j => ⌊Real.sqrt (m j : ℝ) / 8⌋₊
    let A : ℕ → ℕ := fun j => m j - 3 * R j
    let S := Finset.Icc 2 J
    have geo (j : ℕ) (hj : j ∈ S) :=
      geometry J j hJ (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    have hbase (j : ℕ) (hj : j ∈ S) : A j + 3 * R j = m j := Nat.sub_add_cancel (geo j hj).2.2.2.2.1
    have hp (j : ℕ) (hj : j ∈ S) : ∃ h : ℕ → ℝ,
        (∀ n, h n ≠ 0 → A j < n ∧ n < A j + 6 * R j) ∧
        (∀ n, |h n| ≤ Real.sqrt n) ∧
        (∀ n, 1 ≤ n → |h n - h (n - 1)| ≤ 1) ∧
        Summable (fun n : ℕ => h (n + 1) * u (n + 1)) ∧
        Summable (fun n : ℕ => h (n + 1) * v (n + 1)) ∧
        (∑' n : ℕ, h (n + 1) * u (n + 1)) = 0 ∧
        (∑' n : ℕ, h (n + 1) * v (n + 1)) = 0 ∧ h (m j) = R j / 2 := by
      have g := geo j hj
      have ha := hbase j hj
      have hR : 1 ≤ R j := by
        have hRJ : J ≤ R j := g.2.1
        omega
      have hA : 8 * R j ≤ A j + 2 * R j + 1 := by
        have hJR : 64 * J * R j ≤ m j := g.2.2.2.1
        have hx := Nat.mul_le_mul_right (R j) hJ
        nlinarith only [ha, hJR, hx]
      have hsq : R j ^ 2 ≤ A j + 1 := by
        have hRsq : 64 * R j ^ 2 ≤ m j := g.2.2.1
        nlinarith only [ha, hRsq, hR]
      simpa only [ha] using pulse (R j) (A j) hR hA hsq
    choose! h hsupport henvelope hlip hsu hsv hmu hmv hcenter using hp
    let f : ℕ → ℝ := fun n => ∑ j ∈ S, h j n
    have separation (j k : ℕ) (hj : j ∈ S) (hk : k ∈ S) (hjk : j < k) :
        A k + 6 * R k ≤ A j := by
      have hj0 : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
      have hm : m k ≤ m j := Nat.div_le_div_left (by omega) hj0
      have hR : R k ≤ R j := Nat.floor_mono (div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by exact_mod_cast hm)) (by norm_num))
      have hlo : (j + 1) * m k ≤ N := by
        have hmul : (j + 1) * m k ≤ k * m k := Nat.mul_le_mul_right (m k) (by omega)
        exact hmul.trans (by simpa [m, mul_comm] using Nat.div_mul_le_self N k)
      have hhi : N < j * (m j + 1) := by
        simpa [m, mul_comm] using (Nat.div_lt_iff_lt_mul hj0).mp (Nat.lt_succ_self (m j))
      have gj := geo j hj
      have hjJ := (Finset.mem_Icc.mp hj).2
      have hRJ : J ≤ R j := gj.2.1
      have hJR : 64 * J * R j ≤ m j := gj.2.2.2.1
      have hx : j * R j ≤ J * R j := Nat.mul_le_mul_right (R j) hjJ
      have hy : j ≤ j * R j := by nlinarith
      have hz : R j ≤ J * R j := by nlinarith
      have hbudget : 7 * (j + 1) * R j + j ≤ m j := by nlinarith only [hJR, hx, hy, hz]
      have hgap : m k + 7 * R j < m j := by
        by_contra hh
        have hmul := Nat.mul_le_mul_left (j + 1) (show m j ≤ m k + 7 * R j by omega)
        nlinarith only [hmul, hlo, hhi, hbudget]
      have haj := hbase j hj
      have hak := hbase k hk
      omega
    have active (j n : ℕ) (hj : j ∈ S) (hn : 1 ≤ n)
        (ha : h j n ≠ 0 ∨ h j (n - 1) ≠ 0) : A j < n ∧ n ≤ A j + 6 * R j := by
      rcases ha with ha | ha
      · have hs := hsupport j hj n ha
        omega
      · have hs := hsupport j hj (n - 1) ha
        omega
    have unique (j k n : ℕ) (hj : j ∈ S) (hk : k ∈ S) (hn : 1 ≤ n)
        (ha : h j n ≠ 0 ∨ h j (n - 1) ≠ 0) (hb : h k n ≠ 0 ∨ h k (n - 1) ≠ 0) : j = k := by
      have haj := active j n hj hn ha
      have hak := active k n hk hn hb
      rcases lt_trichotomy j k with hlt | heq | hgt
      · have hs := separation j k hj hk hlt
        omega
      · exact heq
      · have hs := separation k j hk hj hgt
        omega
    have single (j n : ℕ) (hj : j ∈ S) (hn : 1 ≤ n)
        (ha : h j n ≠ 0 ∨ h j (n - 1) ≠ 0) : f n = h j n ∧ f (n - 1) = h j (n - 1) := by
      constructor <;> apply Finset.sum_eq_single j
      · intro k hk hkj
        by_contra hh
        exact hkj (unique k j n hk hj hn (Or.inl hh) ha)
      · exact fun h => False.elim (h hj)
      · intro k hk hkj
        by_contra hh
        exact hkj (unique k j n hk hj hn (Or.inr hh) ha)
      · exact fun h => False.elim (h hj)
    have hf0 : f 0 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_contra hh
      have hs := hsupport j hj 0 hh
      omega
    have henv (n : ℕ) : |f n| ≤ Real.sqrt n := by
      by_cases hn : n = 0
      · subst n
        simp [hf0]
      have hn1 : 1 ≤ n := by omega
      by_cases ha : ∃ j ∈ S, h j n ≠ 0
      · obtain ⟨j, hj, ha⟩ := ha
        rw [(single j n hj hn1 (Or.inl ha)).1]
        exact henvelope j hj n
      · have hz : f n = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          by_contra hh
          exact ha ⟨j, hj, hh⟩
        simp [hz]
    have hinc (n : ℕ) (hn : 1 ≤ n) : |f n - f (n - 1)| ≤ 1 := by
      by_cases ha : ∃ j ∈ S, h j n ≠ 0 ∨ h j (n - 1) ≠ 0
      · obtain ⟨j, hj, ha⟩ := ha
        obtain ⟨hn0, hn1⟩ := single j n hj hn ha
        rw [hn0, hn1]
        exact hlip j hj n hn
      · have hz : f n = 0 ∧ f (n - 1) = 0 := by
          constructor <;> apply Finset.sum_eq_zero
          · intro j hj
            by_contra hh
            exact ha ⟨j, hj, Or.inl hh⟩
          · intro j hj
            by_contra hh
            exact ha ⟨j, hj, Or.inr hh⟩
        simp [hz.1, hz.2]
    have hfsupport (n : ℕ) (hn : f n ≠ 0) : 1 ≤ n ∧ n ≤ N := by
      have hex : ∃ j ∈ S, h j n ≠ 0 := by
        by_contra hh
        apply hn
        apply Finset.sum_eq_zero
        intro j hj
        by_contra hnonzero
        exact hh ⟨j, hj, hnonzero⟩
      obtain ⟨j, hj, hnonzero⟩ := hex
      have hs := hsupport j hj n hnonzero
      have ha := hbase j hj
      have hb : m j + 3 * R j ≤ N := (geo j hj).2.2.2.2.2.1
      omega
    have hfinite : (Function.support f).Finite :=
      (Finset.Icc 1 N).finite_toSet.subset (fun n hn => Finset.mem_Icc.mpr (hfsupport n hn))
    have hfun (w : ℕ → ℝ) : (fun n : ℕ => f (n + 1) * w (n + 1)) =
        (fun n : ℕ => ∑ j ∈ S, h j (n + 1) * w (n + 1)) := by
      funext n
      exact Finset.sum_mul S (fun j => h j (n + 1)) (w (n + 1))
    have hfmu : (∑' n : ℕ, f (n + 1) * u (n + 1)) = 0 := by
      rw [hfun u, Summable.tsum_finsetSum (fun j hj => hsu j hj)]
      exact Finset.sum_eq_zero (fun j hj => hmu j hj)
    have hfmv : (∑' n : ℕ, f (n + 1) * v (n + 1)) = 0 := by
      rw [hfun v, Summable.tsum_finsetSum (fun j hj => hsv j hj)]
      exact Finset.sum_eq_zero (fun j hj => hmv j hj)
    have hrnonempty : (ratios f).Nonempty := ⟨|f 1| / Real.sqrt 1, 1, le_rfl, by simp⟩
    have hratio (x : ℝ) (hx : x ∈ ratios f) : x ≤ 1 := by
      obtain ⟨n, hn, rfl⟩ := hx
      have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      exact (div_le_one hs).mpr (henv n)
    have hinput : input f := by
      refine ⟨hf0, ?_, ?_, hfmu, hfmv, hrnonempty, ⟨1, hratio⟩,
        csSup_le hrnonempty hratio, henv, hinc⟩
      · rw [hfun u]; exact summable_sum (fun j hj => hsu j hj)
      · rw [hfun v]; exact summable_sum (fun j hj => hsv j hj)
    have hJN : J ≤ N := by
      have hp : J ≤ J ^ 3 := le_self_pow (by omega) (by decide)
      dsimp only [N]
      omega
    have sample (j d : ℕ) (hj : j ∈ S) (hd : 1 ≤ d) :
        (A j + 1 ≤ N / d ∧ N / d ≤ A j + 6 * R j - 1) ↔ d = j := by
      have ha := hbase j hj
      have g := geo j hj
      have hqa : N / (A j + 1) = j := g.2.2.2.2.2.2.1
      have hqb : N / (A j + 6 * R j) = j - 1 := by
        have he : A j + 6 * R j = m j + 3 * R j := by omega
        rw [he]
        exact g.2.2.2.2.2.2.2
      constructor
      · intro hs
        have hd0 : 0 < d := by omega
        have hlo : d * (A j + 1) ≤ N := by
          have hh := (Nat.le_div_iff_mul_le hd0).mp hs.1
          simpa [mul_comm] using hh
        have hhi : N < d * (A j + 6 * R j) := by
          simpa [mul_comm] using
            (Nat.div_lt_iff_lt_mul hd0).mp (show N / d < A j + 6 * R j by omega)
        have hqa' : N < (j + 1) * (A j + 1) :=
          (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
        have hqb' : (j - 1) * (A j + 6 * R j) ≤ N := by
          have hh := Nat.div_mul_le_self N (A j + 6 * R j)
          rwa [hqb] at hh
        have hdj : d ≤ j := by
          by_contra hh
          have hmul := Nat.mul_le_mul_right (A j + 1) (show j + 1 ≤ d by omega)
          omega
        have hjd : j ≤ d := by
          by_contra hh
          have hmul := Nat.mul_le_mul_right (A j + 6 * R j) (show d ≤ j - 1 by omega)
          omega
        omega
      · intro hdj
        subst d
        have hRJ : J ≤ R j := g.2.1
        have hR : 1 ≤ R j := by omega
        change A j + 1 ≤ m j ∧ m j ≤ A j + 6 * R j - 1
        constructor <;> omega
    have hresponse : T f N = ∑ j ∈ S, k j * (R j / 2) := by
      dsimp only [T, f]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_eq_single j]
      · rw [hcenter j hj]
      · intro d hd hdj
        have hd0 := (Finset.mem_Icc.mp hd).1
        have hz : h j (N / d) = 0 := by
          by_contra hh
          have hs := hsupport j hj (N / d) hh
          exact hdj ((sample j d hj hd0).mp (by constructor <;> omega))
        rw [hz, mul_zero]
      · intro hjn
        have hj0 := (Finset.mem_Icc.mp hj).1
        have hjJ := (Finset.mem_Icc.mp hj).2
        exact False.elim (hjn (Finset.mem_Icc.mpr (by constructor <;> omega)))
    have hsumK : (∑ j ∈ S, k j) = K J := by
      have he : Finset.Icc 1 J = insert 1 S := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert, S]
        omega
      dsimp only [K]
      rw [he, Finset.sum_insert (by simp [S]), hkone, zero_add]
    have hresponse_lower : (J : ℝ) / 2 * K J ≤ T f N := by
      rw [hresponse, ← hsumK]
      calc
        _ = ∑ j ∈ S, k j * ((J : ℝ) / 2) := by rw [← Finset.sum_mul]; ring
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          have hR : (J : ℝ) ≤ R j := by exact_mod_cast (geo j hj).2.1
          have hk := knonneg j (by have := (Finset.mem_Icc.mp hj).1; omega)
          exact mul_le_mul_of_nonneg_left (by linarith) hk
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
    have hroot : Real.sqrt (N : ℝ) = 8 * (J : ℝ) * Real.sqrt J := by
      apply (Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg N) (by positivity)).mpr
      dsimp only [N]
      push_cast
      have hs := Real.sq_sqrt hJ0.le
      calc
        _ = 64 * (J : ℝ) ^ 2 * (J : ℝ) := by ring
        _ = 64 * (J : ℝ) ^ 2 * (Real.sqrt (J : ℝ)) ^ 2 := by rw [hs]
        _ = _ := by ring
    refine ⟨f, hfinite, hinput, ?_⟩
    change K J / (16 * Real.sqrt J) ≤ T f N / Real.sqrt (N : ℝ)
    calc
      _ = ((J : ℝ) / 2 * K J) / Real.sqrt (N : ℝ) := by
        rw [hroot]
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hresponse_lower (Real.sqrt_nonneg _)
  classical
  have family (J : ℕ) : ∃ f : ℕ → ℝ, 2 ≤ J →
      (Function.support f).Finite ∧ input f ∧
      K J / (16 * Real.sqrt J) ≤ T f (64 * J ^ 3) / Real.sqrt ((64 * J ^ 3 : ℕ) : ℝ) := by
    by_cases hJ : 2 ≤ J
    · obtain ⟨f, hf⟩ := construct J hJ
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 0, fun h => False.elim (hJ h)⟩
  choose f hf using family
  refine ⟨⟨f, hf⟩, divergence, ?_⟩
  rintro ⟨C, hC⟩
  obtain ⟨J, hJ, hgt⟩ := ((eventually_ge_atTop 2).and (divergence.eventually_gt_atTop C)).exists
  obtain ⟨g, hfinite, hinput, hresponse⟩ := construct J hJ
  have hN : 1 ≤ 64 * J ^ 3 := by
    have hj : 0 < J := by omega
    have hp : 0 < 64 * J ^ 3 := by positivity
    omega
  obtain ⟨hg0, hsu, hsv, hmu, hmv, hne, hbounded, hsup, henvelope, hincrement⟩ := hinput
  have hsource : original g := ⟨hg0, hmu, hmv, hne, hbounded, hsup, hincrement⟩
  have hb := hC g hsource (64 * J ^ 3) hN
  have habs := div_le_div_of_nonneg_right (le_abs_self (T g (64 * J ^ 3)))
    (Real.sqrt_nonneg ((64 * J ^ 3 : ℕ) : ℝ))
  linarith only [hb, habs, hresponse, hgt]

end D5.S3.Arith.FibonacciAtomic.NeutralTentResponseObstruction
