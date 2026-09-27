/- GID: D5/S1/Words/Patterns/A398542Polynomial
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/A398542Polynomial
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Guarded generating functions of actual fixed-bottom permutations. -/

import D5.S1.Words.Patterns.A398542MinimumRecurrence
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators

namespace D5.S1.Words.Patterns.A398542Polynomial

open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open D5.S1.Words.Patterns.A398542FixedBottom
open D5.S1.Words.Patterns.A398542MinimumRecurrence
open Finset PowerSeries

noncomputable section

/-- Coefficients are cardinalities of actual source permutations. -/
def intervalSeries {m : ℕ} (b : Equiv.Perm (Fin m)) (l h : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun k => (intervalCount b l h k : ℚ))

/-- The pinned Catalan series, with rational coefficients. -/
def catalanQ : PowerSeries ℚ := catalanSeries.map (Nat.castRingHom ℚ)

/-- The inverse of the constant-one series `1-2XC`. -/
def centralSeries : PowerSeries ℚ :=
  invOfUnit (1 - 2 * X * catalanQ) (Units.mk0 (1 : ℚ) one_ne_zero)

/-- The actual minimum split gives the interval equation. Singleton intervals
have the Catalan series, by uniqueness of its coefficient recurrence. -/
theorem actual_series {m : ℕ} (b : Equiv.Perm (Fin m))
    (hb : ¬Contains pattern132 b) :
    (∀ l h, l ≤ h → h ≤ m →
      intervalSeries b l h = 1 + X * ∑ g ∈ Icc l h,
        intervalSeries b l g * intervalSeries b g (min h (dead b g - 1))) ∧
    (∀ g ≤ m, intervalSeries b g g = catalanQ) := by
  classical
  have dp (g : ℕ) (hg : g ≤ m) : g < dead b g := by
    unfold dead
    apply (Finset.lt_min'_iff _ _).mpr
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · omega
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have := (Finset.mem_filter.mp hi).2.1
    omega
  have eqn (l h : ℕ) (hlh : l ≤ h) (hhm : h ≤ m) :
      intervalSeries b l h = 1 + X * ∑ g ∈ Icc l h,
        intervalSeries b l g * intervalSeries b g (min h (dead b g - 1)) := by
    have hc := actual_cardinal_recurrence b hb hlh hhm
    ext k
    cases k with
    | zero => simp [intervalSeries, hc.1]
    | succ k =>
      simp only [map_add, coeff_one, Nat.add_one_ne_zero, ↓reduceIte, zero_add,
        coeff_succ_X_mul]
      simp only [map_sum, coeff_mul, intervalSeries, coeff_mk]
      rw [(hc.2.1 k).2]
      push_cast
      apply Finset.sum_bij (fun g _ => g.val.val)
      · intro g hg
        exact Finset.mem_Icc.mpr g.property
      · intro g hg j hj he
        apply Subtype.ext
        exact Fin.ext he
      · intro g hg
        have gh := Finset.mem_Icc.mp hg
        exact ⟨⟨⟨g, by omega⟩, gh⟩, Finset.mem_univ _, rfl⟩
      · intro g hg
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        exact Fin.sum_univ_eq_sum_range (fun a =>
          (intervalCount b l g.val.val a : ℚ) *
            (intervalCount b g.val.val (min h (dead b g.val.val - 1)) (k - a) : ℚ)) (k + 1)
  refine ⟨eqn, ?_⟩
  intro g hg
  have eg := eqn g g le_rfl hg
  have hmin : min g (dead b g - 1) = g := min_eq_left (by have := dp g hg; omega)
  simp only [Finset.Icc_self, Finset.sum_singleton, hmin] at eg
  have ec : catalanQ = 1 + X * (catalanQ * catalanQ) := by
    have hh := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa [catalanQ, pow_two, add_comm, mul_comm] using hh.symm
  ext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simpa [intervalSeries, catalanQ] using
        congrArg (fun n : ℕ => (n : ℚ)) (actual_cardinal_recurrence b hb le_rfl hg).1
    | succ k =>
      rw [eg, ec]
      simp only [map_add, coeff_one, Nat.add_one_ne_zero, ↓reduceIte, zero_add,
        coeff_succ_X_mul]
      simp only [coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hij' := Finset.mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega), ih ij.2 (by omega)]

/-- Strictly guarded nonsingleton intervals have a finite polynomial in the
central-binomial series, with the sharp width bound. Singleton right children
use the Catalan identity separately; no monotonicity of `dead` is needed. -/
theorem guarded_polynomial {m : ℕ} (b : Equiv.Perm (Fin m))
    (hb : ¬Contains pattern132 b) {l h : ℕ}
    (hlh : l < h) (hhm : h ≤ m) (guard : h < dead b l) :
    ∃ A : Polynomial ℚ, A.natDegree ≤ 2 * (h - l) - 2 ∧
      intervalSeries b l h = centralSeries * A.eval₂ PowerSeries.C centralSeries := by
  classical
  let T := centralSeries
  let C := catalanQ
  let s : PowerSeries ℚ := 1 - 2 * X * C
  have ec : C ^ 2 * X + 1 = C := by
    simpa [C, catalanQ] using congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
  have ss : s * s = 1 - 4 * X := by
    have h1 : X * C ^ 2 = C - 1 := by
      rw [mul_comm]
      exact eq_sub_of_add_eq ec
    have h2 : X ^ 2 * C ^ 2 = X * C - X := by
      calc
        X ^ 2 * C ^ 2 = X * (X * C ^ 2) := by ring
        _ = X * (C - 1) := by rw [h1]
        _ = X * C - X := by ring
    calc
      s * s = 1 - 4 * (X * C) + 4 * (X ^ 2 * C ^ 2) := by dsimp [s]; ring
      _ = 1 - 4 * X := by rw [h2]; ring
  have st : s * T = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp [s]
  have ts : T * s = 1 := by rw [mul_comm, st]
  have t2 : 4 * X * T ^ 2 = T ^ 2 - 1 := by
    calc
      4 * X * T ^ 2 = T ^ 2 - T ^ 2 * (s * s) := by rw [ss]; ring
      _ = T ^ 2 - (T * s) ^ 2 := by ring
      _ = T ^ 2 - 1 := by rw [ts]; ring
  have tc : 2 * X * C * T = T - 1 := by
    calc
      2 * X * C * T = T - s * T := by dsimp [s]; ring
      _ = T - 1 := by rw [st]
  have scalar (a : ℚ) (ha : a ≠ 0) :
      (PowerSeries.C a⁻¹ : PowerSeries ℚ) * PowerSeries.C a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have xt2 : X * T ^ 2 = PowerSeries.C (1 / 4 : ℚ) * (T ^ 2 - 1) := by
    rw [← t2]
    have hc : (PowerSeries.C (1 / 4 : ℚ) : PowerSeries ℚ) * 4 = 1 := by
      simpa only [one_div, map_ofNat] using scalar 4 (by norm_num)
    calc
      X * T ^ 2 = (PowerSeries.C (1 / 4 : ℚ) * 4) * (X * T ^ 2) := by rw [hc, one_mul]
      _ = _ := by ring
  have xct : X * C * T = PowerSeries.C (1 / 2 : ℚ) * (T - 1) := by
    rw [← tc]
    have hc : (PowerSeries.C (1 / 2 : ℚ) : PowerSeries ℚ) * 2 = 1 := by
      simpa only [one_div, map_ofNat] using scalar 2 (by norm_num)
    calc
      X * C * T = (PowerSeries.C (1 / 2 : ℚ) * 2) * (X * C * T) := by rw [hc, one_mul]
      _ = _ := by ring
  obtain ⟨equation, singleton⟩ := actual_series b hb
  have dp (g : ℕ) (hg : g ≤ m) : g < dead b g := by
    unfold dead
    apply (Finset.lt_min'_iff _ _).mpr
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · omega
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have := (Finset.mem_filter.mp hi).2.1
    omega
  have induction_step (w : ℕ) : ∀ l h, h - l = w → l < h → h ≤ m → h < dead b l →
      ∃ A : Polynomial ℚ, A.natDegree ≤ 2 * w - 2 ∧
        intervalSeries b l h = T * A.eval₂ PowerSeries.C T := by
    induction w using Nat.strong_induction_on with
    | h w ih =>
      intro l h hw hlh hhm guard
      have terms (g : ℕ) (hg : g ∈ Ioo l h) :
          ∃ P : Polynomial ℚ, P.natDegree ≤ 2 * w - 2 ∧
            T * P.eval₂ PowerSeries.C T = X * T *
              intervalSeries b l g * intervalSeries b g (min h (dead b g - 1)) := by
        obtain ⟨hlg, hgh⟩ := Finset.mem_Ioo.mp hg
        obtain ⟨A, hA, eA⟩ := ih (g - l) (by omega) l g rfl hlg (by omega) (by omega)
        let r := min h (dead b g - 1)
        have gr : g ≤ r := le_min (by omega) (by have := dp g (by omega); omega)
        have rh : r ≤ h := min_le_left _ _
        by_cases he : r = g
        · have er : intervalSeries b g r = C := by rw [he]; exact singleton g (by omega)
          refine ⟨Polynomial.C (1 / 2 : ℚ) * (Polynomial.X - 1) * A, ?_, ?_⟩
          · have hd : (Polynomial.C (1 / 2 : ℚ) * (Polynomial.X - 1) * A).natDegree ≤
                1 + A.natDegree := by
              apply le_trans Polynomial.natDegree_mul_le
              apply Nat.add_le_add_right
              apply le_trans Polynomial.natDegree_mul_le
              simp only [Polynomial.natDegree_C, zero_add]
              apply le_trans (Polynomial.natDegree_sub_le _ _)
              simp
            omega
          · change T * _ = X * T * intervalSeries b l g * intervalSeries b g r
            rw [eA, er]
            simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_sub,
              Polynomial.eval₂_X, Polynomial.eval₂_one]
            calc
              T * (PowerSeries.C (1 / 2 : ℚ) * (T - 1) * A.eval₂ PowerSeries.C T) =
                  T * (X * C * T) * A.eval₂ PowerSeries.C T := by rw [xct]; ring
              _ = _ := by ring
        · have gr' : g < r := by omega
          obtain ⟨B, hB, eB⟩ := ih (r - g) (by omega) g r rfl gr' (by omega)
            (by have := min_le_right h (dead b g - 1); have := dp g (by omega); dsimp [r]; omega)
          refine ⟨Polynomial.C (1 / 4 : ℚ) * (Polynomial.X ^ 2 - 1) * A * B, ?_, ?_⟩
          · have hd : (Polynomial.C (1 / 4 : ℚ) * (Polynomial.X ^ 2 - 1) * A * B).natDegree ≤
                2 + A.natDegree + B.natDegree := by
              apply le_trans Polynomial.natDegree_mul_le
              apply Nat.add_le_add_right
              apply le_trans Polynomial.natDegree_mul_le
              apply Nat.add_le_add_right
              apply le_trans Polynomial.natDegree_mul_le
              simp only [Polynomial.natDegree_C, zero_add]
              apply le_trans (Polynomial.natDegree_sub_le _ _)
              simp
            omega
          · change T * _ = X * T * intervalSeries b l g * intervalSeries b g r
            rw [eA, eB]
            simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_sub,
              Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
            calc
              T * (PowerSeries.C (1 / 4 : ℚ) * (T ^ 2 - 1) *
                  A.eval₂ PowerSeries.C T * B.eval₂ PowerSeries.C T) =
                  T * (X * T ^ 2) * A.eval₂ PowerSeries.C T * B.eval₂ PowerSeries.C T := by
                    rw [xt2]; ring
              _ = _ := by ring
      let P (g : ℕ) : Polynomial ℚ := if hg : g ∈ Ioo l h then (terms g hg).choose else 0
      have hp (g : ℕ) (hg : g ∈ Ioo l h) :
          (P g).natDegree ≤ 2 * w - 2 ∧
            T * (P g).eval₂ PowerSeries.C T = X * T *
              intervalSeries b l g * intervalSeries b g (min h (dead b g - 1)) := by
        simpa only [P, dif_pos hg] using (terms g hg).choose_spec
      refine ⟨1 + ∑ g ∈ Ioo l h, P g, ?_, ?_⟩
      · apply Polynomial.natDegree_add_le_of_degree_le (by simp)
        exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun g hg => (hp g hg).1)
      · have e := equation l h (by omega) hhm
        have decomp : Icc l h = insert l (insert h (Ioo l h)) := by
          ext j
          simp only [mem_Icc, mem_insert, mem_Ioo]
          omega
        rw [decomp, sum_insert (by simp; omega), sum_insert (by simp)] at e
        have ml : min h (dead b l - 1) = h := min_eq_left (by omega)
        have mh : min h (dead b h - 1) = h := min_eq_left (by have := dp h hhm; omega)
        rw [ml, mh, singleton l (by omega), singleton h hhm] at e
        have isolated : s * intervalSeries b l h = 1 + X * ∑ g ∈ Ioo l h,
            intervalSeries b l g * intervalSeries b g (min h (dead b g - 1)) := by
          dsimp [s, C]
          linear_combination e
        have solve : intervalSeries b l h = T + ∑ g ∈ Ioo l h,
            X * T * intervalSeries b l g * intervalSeries b g (min h (dead b g - 1)) := by
          calc
            intervalSeries b l h = T * (s * intervalSeries b l h) := by
              rw [← mul_assoc, ts, one_mul]
            _ = T * (1 + X * ∑ g ∈ Ioo l h,
                intervalSeries b l g * intervalSeries b g (min h (dead b g - 1))) := by
              rw [isolated]
            _ = _ := by
              simp only [mul_add, mul_one, Finset.mul_sum]
              congr 1
              apply sum_congr rfl
              intros
              ring
        rw [solve]
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_finsetSum,
          mul_add, mul_one, Finset.mul_sum]
        congr 1
        exact sum_congr rfl (fun g hg => (hp g hg).2.symm)
  exact induction_step (h - l) l h rfl hlh hhm guard

/-- The fixed-bottom conjecture for the literal cardinality of actual
permutations. The rational polynomials are chosen before the upper size `k`;
the empty upper cell is included, and the one-letter bottom has `q = 0`. -/
theorem result {m : ℕ} (hm : 1 ≤ m) (b : Equiv.Perm (Fin m))
    (hb : ¬Contains pattern132 b) :
    ∃ p q : Polynomial ℚ,
      p.natDegree ≤ m - 1 ∧ q.natDegree ≤ m - 2 ∧ (m = 1 → q = 0) ∧
      ∀ k : ℕ, (count b k : ℚ) =
        p.eval (k : ℚ) * (Nat.centralBinom k : ℚ) + q.eval (k : ℚ) * (4 : ℚ) ^ k := by
  classical
  let T := centralSeries
  let s : PowerSeries ℚ := 1 - 2 * X * catalanQ
  have ec : catalanQ ^ 2 * X + 1 = catalanQ := by
    simpa [catalanQ] using congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
  have ss : s * s = 1 - 4 * X := by
    have h1 : X * catalanQ ^ 2 = catalanQ - 1 := by
      rw [mul_comm]
      exact eq_sub_of_add_eq ec
    have h2 : X ^ 2 * catalanQ ^ 2 = X * catalanQ - X := by
      calc
        X ^ 2 * catalanQ ^ 2 = X * (X * catalanQ ^ 2) := by ring
        _ = X * (catalanQ - 1) := by rw [h1]
        _ = X * catalanQ - X := by ring
    calc
      s * s = 1 - 4 * (X * catalanQ) + 4 * (X ^ 2 * catalanQ ^ 2) := by dsimp [s]; ring
      _ = 1 - 4 * X := by rw [h2]; ring
  have sc : constantCoeff s = 1 := by simp [s]
  have st : s * T = 1 := PowerSeries.mul_invOfUnit _ _ sc
  let B : PowerSeries ℚ := rescale (-4 : ℚ) (binomialSeries ℚ (1 / 2 : ℚ))
  have bc : constantCoeff B = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [B]
  have bs : B * B = 1 - 4 * X := by
    have hadd := PowerSeries.binomialSeries_add (A := ℚ) (1 / 2 : ℚ) (1 / 2 : ℚ)
    have hone := PowerSeries.binomialSeries_nat (R := ℚ) (A := ℚ) 1
    have hbin : PowerSeries.binomialSeries ℚ (1 : ℚ) = 1 + X := by simpa using hone
    have hsum : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + X := by
      rw [show (1 / 2 + 1 / 2 : ℚ) = 1 by norm_num, hbin] at hadd
      exact (pow_two _).trans hadd.symm
    change rescale (-4 : ℚ) _ * rescale (-4 : ℚ) _ = _
    rw [← map_mul, ← pow_two, hsum, map_add, PowerSeries.rescale_X]
    simp only [map_one, map_neg, map_ofNat]
    ring
  have be : B = s := by
    have hu : IsUnit (s + B) := PowerSeries.isUnit_iff_constantCoeff.mpr (by
      rw [map_add, sc, bc]; norm_num)
    have he : (s + B) * s = (s + B) * B := by
      calc
        (s + B) * s = s * s + B * s := by ring
        _ = B * B + B * s := by rw [ss, bs]
        _ = (s + B) * B := by ring
    exact (hu.mul_left_cancel he).symm
  have te : T = rescale (-4 : ℚ) (binomialSeries ℚ (-(1 / 2 : ℚ))) := by
    have hh : s * rescale (-4 : ℚ) (binomialSeries ℚ (-(1 / 2 : ℚ))) = 1 := by
      rw [← be]
      change rescale (-4 : ℚ) _ * rescale (-4 : ℚ) _ = _
      rw [← map_mul, ← binomialSeries_add, add_neg_cancel, binomialSeries_zero, map_one]
    have hu : IsUnit s := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [sc]; exact isUnit_one)
    exact hu.mul_left_cancel (st.trans hh.symm)
  have tp (j : ℕ) : T ^ j = rescale (-4 : ℚ) (binomialSeries ℚ (-(j : ℚ) / 2)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, te, ← map_mul, ← binomialSeries_add]
      congr 2
      push_cast
      ring
  have choose_neg (a : ℚ) (n : ℕ) : Ring.choose (-a) n =
      ((-1 : ℚ) ^ n) * (ascPochhammer ℚ n).eval a / (n.factorial : ℚ) := by
    rw [Ring.choose_neg']
    have hh := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at hh
    have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [← hh]
    simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
    field_simp
  have tcoeff (j k : ℕ) : coeff k (T ^ j) =
      (4 : ℚ) ^ k * (ascPochhammer ℚ k).eval ((j : ℚ) / 2) / (k.factorial : ℚ) := by
    rw [tp, coeff_rescale, binomialSeries_coeff]
    simp only [smul_eq_mul, mul_one]
    rw [neg_div, choose_neg, mul_div_assoc, ← mul_assoc, ← mul_pow]
    ring
  have half (k : ℕ) : (4 : ℚ) ^ k * (ascPochhammer ℚ k).eval (1 / 2) =
      (Nat.centralBinom k : ℚ) * (k.factorial : ℚ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_eval, pow_succ, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      have hc : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
          2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ k
      calc
        (4 : ℚ) ^ k * 4 * ((ascPochhammer ℚ k).eval (1 / 2) * (1 / 2 + k)) =
            ((4 : ℚ) ^ k * (ascPochhammer ℚ k).eval (1 / 2)) * (2 * (2 * k + 1)) := by ring
        _ = ((Nat.centralBinom k : ℚ) * k.factorial) * (2 * (2 * k + 1)) := by rw [ih]
        _ = ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) * k.factorial := by rw [hc]; ring
        _ = _ := by ring
  have ratio (a : ℚ) (ha : 0 < a) (k r : ℕ) :
      (ascPochhammer ℚ k).eval (a + r) = (ascPochhammer ℚ k).eval a *
        ∏ i ∈ Finset.range r, ((a + k + i) / (a + i)) := by
    have shift (a : ℚ) (k : ℕ) : a * (ascPochhammer ℚ k).eval (a + 1) =
        (ascPochhammer ℚ k).eval a * (a + k) := by
      have h1 := congrArg (Polynomial.eval a) (ascPochhammer_mul ℚ 1 k)
      have h2 := congrArg (Polynomial.eval a) (ascPochhammer_mul ℚ k 1)
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, ascPochhammer_one,
        Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_natCast] at h1 h2
      rw [Nat.add_comm 1 k] at h1
      exact h1.trans h2.symm
    induction r with
    | zero => simp
    | succ r ih =>
      have hn : a + (r : ℚ) ≠ 0 := ne_of_gt (by positivity)
      have hs := shift (a + r) k
      rw [ih] at hs
      rw [Finset.prod_range_succ]
      push_cast
      rw [show a + ((r : ℚ) + 1) = a + r + 1 by ring]
      apply mul_left_cancel₀ hn
      calc
        (a + r) * (ascPochhammer ℚ k).eval (a + r + 1) =
            ((ascPochhammer ℚ k).eval a * ∏ i ∈ Finset.range r, ((a + k + i) / (a + i))) *
              (a + r + k) := hs
        _ = _ := by field_simp; ring
  have oddcoeff (r k : ℕ) : coeff k (T ^ (2 * r + 1)) = (Nat.centralBinom k : ℚ) *
      ∏ i ∈ Finset.range r, ((2 * (k : ℚ) + 2 * i + 1) / (2 * i + 1)) := by
    rw [tcoeff]
    have he : ((2 * r + 1 : ℕ) : ℚ) / 2 = 1 / 2 + r := by push_cast; ring
    rw [he, ratio (1 / 2) (by norm_num), ← mul_assoc, half]
    have hn : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hp : (∏ i ∈ Finset.range r, ((1 / 2 + (k : ℚ) + i) / (1 / 2 + i))) =
        ∏ i ∈ Finset.range r, ((2 * (k : ℚ) + 2 * i + 1) / (2 * i + 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have h1 : (1 / 2 + (i : ℚ)) ≠ 0 := by positivity
      have h2 : (2 * (i : ℚ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hp]
    field_simp
  have evencoeff (r k : ℕ) : coeff k (T ^ (2 * r + 2)) = (4 : ℚ) ^ k *
      ∏ i ∈ Finset.range r, (((k : ℚ) + i + 1) / (i + 1)) := by
    rw [tcoeff]
    have he : ((2 * r + 2 : ℕ) : ℚ) / 2 = 1 + r := by push_cast; ring
    rw [he, ratio 1 (by norm_num), ascPochhammer_eval_one]
    have hn : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hp : (∏ i ∈ Finset.range r, ((1 + (k : ℚ) + i) / (1 + i))) =
        ∏ i ∈ Finset.range r, (((k : ℚ) + i + 1) / (i + 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1 <;> ring
    rw [hp]
    field_simp
  let oddP (r : ℕ) : Polynomial ℚ := ∏ i ∈ Finset.range r,
    Polynomial.C (1 / (2 * (i : ℚ) + 1)) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * (i : ℚ) + 1))
  let evenP (r : ℕ) : Polynomial ℚ := ∏ i ∈ Finset.range r,
    Polynomial.C (1 / ((i : ℚ) + 1)) * (Polynomial.X + Polynomial.C ((i : ℚ) + 1))
  have deg_odd (r : ℕ) : (oddP r).natDegree ≤ r := by
    apply le_trans (Polynomial.natDegree_prod_le _ _)
    calc
      _ ≤ ∑ _i ∈ Finset.range r, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        apply le_trans Polynomial.natDegree_mul_le
        simp only [Polynomial.natDegree_C, zero_add]
        apply Polynomial.natDegree_add_le_of_degree_le
        · apply le_trans Polynomial.natDegree_mul_le
          simp
        · rw [Polynomial.natDegree_C]
          omega
      _ = r := by simp
  have deg_even (r : ℕ) : (evenP r).natDegree ≤ r := by
    apply le_trans (Polynomial.natDegree_prod_le _ _)
    calc
      _ ≤ ∑ _i ∈ Finset.range r, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        apply le_trans Polynomial.natDegree_mul_le
        simp only [Polynomial.natDegree_C, zero_add]
        apply Polynomial.natDegree_add_le_of_degree_le
        · simp only [Polynomial.natDegree_X, le_refl]
        · rw [Polynomial.natDegree_C]
          omega
      _ = r := by simp
  have odd_eval (r k : ℕ) : (oddP r).eval (k : ℚ) =
      ∏ i ∈ Finset.range r, ((2 * (k : ℚ) + 2 * i + 1) / (2 * i + 1)) := by
    simp only [oddP, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  have even_eval (r k : ℕ) : (evenP r).eval (k : ℚ) =
      ∏ i ∈ Finset.range r, (((k : ℚ) + i + 1) / (i + 1)) := by
    simp only [evenP, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  have powers (i : ℕ) (hi : i ≤ 2 * m - 2) :
      ∃ p q : Polynomial ℚ, p.natDegree ≤ m - 1 ∧ q.natDegree ≤ m - 2 ∧
        (m = 1 → q = 0) ∧ ∀ k : ℕ, coeff k (T ^ (i + 1)) =
          p.eval (k : ℚ) * (Nat.centralBinom k : ℚ) + q.eval (k : ℚ) * (4 : ℚ) ^ k := by
    obtain ⟨r, he | he⟩ := Nat.even_or_odd' i
    · refine ⟨oddP r, 0, le_trans (deg_odd r) (by omega), by simp, by simp, ?_⟩
      intro k
      rw [he, oddcoeff, odd_eval]
      simp [mul_comm]
    · refine ⟨0, evenP r, by simp, le_trans (deg_even r) (by omega), ?_, ?_⟩
      · intro hm1
        omega
      · intro k
        rw [he, show 2 * r + 1 + 1 = 2 * r + 2 by omega, evencoeff, even_eval]
        simp [mul_comm]
  have dead0 : dead b 0 = m + 2 := by
    have pm : prefixMin b 0 = m := by simp [prefixMin]
    have empty : (Finset.univ.filter
        (fun j : Fin m => 0 ≤ j.val ∧ prefixMin b 0 < (b j).val)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj hh
      rw [pm] at hh
      have := (b j).isLt
      omega
    unfold dead
    simp only [empty, Finset.image_empty]
    simp
  obtain ⟨A, hA, eA⟩ := guarded_polynomial b hb (l := 0) (h := m) (by omega) le_rfl
    (by rw [dead0]; omega)
  simp only [Nat.sub_zero] at hA
  let p (i : ℕ) : Polynomial ℚ := if hi : i ≤ 2 * m - 2 then (powers i hi).choose else 0
  let q (i : ℕ) : Polynomial ℚ := if hi : i ≤ 2 * m - 2 then (powers i hi).choose_spec.choose else 0
  have pq (i : ℕ) (hi : i ≤ 2 * m - 2) :
      (p i).natDegree ≤ m - 1 ∧ (q i).natDegree ≤ m - 2 ∧ (m = 1 → q i = 0) ∧
        ∀ k : ℕ, coeff k (T ^ (i + 1)) =
          (p i).eval (k : ℚ) * (Nat.centralBinom k : ℚ) + (q i).eval (k : ℚ) * (4 : ℚ) ^ k := by
    simpa only [p, q, dif_pos hi] using (powers i hi).choose_spec.choose_spec
  refine ⟨∑ i ∈ Finset.range (A.natDegree + 1), Polynomial.C (A.coeff i) * p i,
    ∑ i ∈ Finset.range (A.natDegree + 1), Polynomial.C (A.coeff i) * q i, ?_, ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hh := pq i (by have := Finset.mem_range.mp hi; omega)
    exact Polynomial.natDegree_mul_le.trans (by simpa using hh.1)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hh := pq i (by have := Finset.mem_range.mp hi; omega)
    exact Polynomial.natDegree_mul_le.trans (by simpa using hh.2.1)
  · intro hm1
    apply Finset.sum_eq_zero
    intro i hi
    rw [(pq i (by have := Finset.mem_range.mp hi; omega)).2.2.1 hm1, mul_zero]
  · intro k
    have ef : (count b k : ℚ) = coeff k (T * A.eval₂ PowerSeries.C T) := by
      rw [← eA]
      simp only [intervalSeries, coeff_mk]
      exact (congrArg (fun n : ℕ => (n : ℚ))
        ((actual_cardinal_recurrence b hb (Nat.zero_le m) le_rfl).2.2 k)).symm
    rw [ef, Polynomial.eval₂_eq_sum_range]
    simp only [Finset.mul_sum, map_sum]
    have hc (i : ℕ) : coeff k (T * (PowerSeries.C (A.coeff i) * T ^ i)) =
        A.coeff i * coeff k (T ^ (i + 1)) := by
      rw [show T * (PowerSeries.C (A.coeff i) * T ^ i) =
        PowerSeries.C (A.coeff i) * T ^ (i + 1) by rw [pow_succ]; ring, coeff_C_mul]
    simp only [hc, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(pq i (by have := Finset.mem_range.mp hi; omega)).2.2.2 k]
    ring

end

end D5.S1.Words.Patterns.A398542Polynomial
