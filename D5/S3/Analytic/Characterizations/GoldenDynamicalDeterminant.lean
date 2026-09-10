/- GID: D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant
   generality: I
   mirror-B: D5/B/S3/Analytic/Characterizations/GoldenDynamicalDeterminant
   mirror-E: none(waiver:analytically-proved)
   anchors: []
   utility: none
   digest: The golden trace series has a local principal logarithm, a rational continuation, and reciprocal Perron poles. -/

import D5.S3.Analytic.Characterizations.GoldenTraceLog
import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
The source uses the positive exponential convention, commonly called the dynamical zeta.
Its defining sum and exponential live only on the open convergence disk. Pole statements
refer to the separate rational continuation and its punctured germ.

The finite matrix and word-count facts are reused prerequisites. The new assertions concern
the infinite trace series, its branch, continuation, and the asymptotics of actual words.
The source's naming and negative-energy qualifications are interpretive prose, not extra
physical predicates. Part1738 and Part1740 are not covered by this module.
-/

open scoped Matrix
open Filter
open D5.S3.Analytic.Characterizations.GoldenTraceLog

noncomputable section

namespace D5.S3.Analytic.Characterizations.GoldenDynamicalDeterminant

def wordCount : ℕ → ℕ := fun n =>
  Fintype.card {w : Fin n → Bool // D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm n w}

/-- Poles belong to the continuation. The convergence radius is the greatest centered
open disk of absolute summability; the positive boundary point has a harmonic obstruction. -/
def continuationContract : Prop :=
  MeromorphicOn continuation Set.univ ∧
  (∀ z : ℂ, z ≠ ((Real.goldenRatio⁻¹ : ℝ) : ℂ) →
    z ≠ -(Real.goldenRatio : ℂ) → AnalyticAt ℂ continuation z) ∧
  meromorphicOrderAt continuation ((Real.goldenRatio⁻¹ : ℝ) : ℂ) = (-1 : ℤ) ∧
  meromorphicOrderAt continuation (-(Real.goldenRatio : ℂ)) = (-1 : ℤ) ∧
  (∀ z : ℂ, meromorphicOrderAt continuation z < 0 ↔
    z = ((Real.goldenRatio⁻¹ : ℝ) : ℂ) ∨ z = -(Real.goldenRatio : ℂ)) ∧
  0 < Real.goldenRatio⁻¹ ∧ Real.goldenRatio⁻¹ < Real.goldenRatio ∧
  (∀ z : ℂ, meromorphicOrderAt continuation z < 0 →
    Real.goldenRatio⁻¹ ≤ ‖z‖ ∧
    (‖z‖ = Real.goldenRatio⁻¹ ↔ z = ((Real.goldenRatio⁻¹ : ℝ) : ℂ))) ∧
  (∀ n : ℕ, traceTerm ((Real.goldenRatio⁻¹ : ℝ) : ℂ) n =
    (1 + (-((Real.goldenRatio⁻¹ : ℝ) : ℂ) ^ 2) ^ (n + 1)) / (n + 1 : ℂ)) ∧
  Summable (fun n : ℕ =>
    ‖(-((Real.goldenRatio⁻¹ : ℝ) : ℂ) ^ 2) ^ (n + 1) / (n + 1 : ℂ)‖) ∧
  ¬ Summable (traceTerm ((Real.goldenRatio⁻¹ : ℝ) : ℂ)) ∧
  IsGreatest {R : ℝ | 0 ≤ R ∧ ∀ z : ℂ, ‖z‖ < R →
    Summable (fun n : ℕ => ‖traceTerm z n‖)} Real.goldenRatio⁻¹ ∧
  spectrum ℂ adjacency = {(Real.goldenRatio : ℂ), (Real.goldenConj : ℂ)} ∧
  spectralRadius ℂ adjacency = ENNReal.ofReal Real.goldenRatio ∧
  (∀ i : Fin 2, 0 < D5.S1.Scale.expandingEigenvector i) ∧
  D5.S1.Scale.fibonacciSubstitution *ᵥ D5.S1.Scale.expandingEigenvector =
    Real.goldenRatio • D5.S1.Scale.expandingEigenvector

/-- Recursive forbidden-11 words, integer counts, their actual root growth, and the
different trace and word correction indices. No energy or naming classifier is introduced. -/
def wordContract : Prop :=
  (∀ n : ℕ, ∀ w : Fin n → Bool,
    (D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm n w ↔
      ∀ i : Fin n, ∀ hi : i.val + 1 < n,
        ¬ (w i = true ∧ w ⟨i.val + 1, hi⟩ = true)) ∧
    (D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm n w ↔
      ∀ i : Fin n, ∀ hi : i.val + 1 < n,
        adjacency (if w i then 1 else 0) (if w ⟨i.val + 1, hi⟩ then 1 else 0) = 1)) ∧
  (∀ n : ℕ, wordCount n = Nat.fib (n + 2)) ∧
  Filter.Tendsto (fun n : ℕ => (wordCount n : ℝ) ^ (1 / (n : ℝ)))
    Filter.atTop (nhds Real.goldenRatio) ∧
  Irrational Real.goldenRatio ∧
  Real.goldenRatio = (1 + Real.sqrt 5) / 2 ∧
  Real.goldenConj = (1 - Real.sqrt 5) / 2 ∧
  Real.goldenConj = -Real.goldenRatio⁻¹ ∧
  (∀ n : ℕ, Real.goldenConj ^ n = (-1 : ℝ) ^ n * (Real.goldenRatio⁻¹) ^ n) ∧
  (∀ n : ℕ, (wordCount n : ℝ) =
    (Real.goldenRatio ^ (n + 2) - Real.goldenConj ^ (n + 2)) / Real.sqrt 5) ∧
  (∀ n : ℕ,
    (Even n → 0 < Real.goldenConj ^ n) ∧
    (Odd n → Real.goldenConj ^ n < 0) ∧
    (Even n → -(Real.goldenConj ^ (n + 2)) / Real.sqrt 5 < 0) ∧
    (Odd n → 0 < -(Real.goldenConj ^ (n + 2)) / Real.sqrt 5))

private theorem admissible_iff_no_adjacent (n : ℕ) (w : Fin n → Bool) :
    D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm n w ↔
      ∀ i : Fin n, ∀ hi : i.val + 1 < n,
        ¬ (w i = true ∧ w ⟨i.val + 1, hi⟩ = true) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        trivial
  | one =>
      constructor
      · intro _ i hi
        have hi0 : i.val = 0 := by omega
        omega
      · intro _
        trivial
  | more n ih0 ih1 =>
      change (¬ (w 0 = true ∧ w 1 = true) ∧
        D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm (n + 1) (Fin.tail w)) ↔ _
      constructor
      · rintro ⟨hh, ht⟩ ⟨i, hi⟩ hij
        change i + 1 < n + 2 at hij
        cases i with
        | zero => simpa using hh
        | succ i =>
            have hj : i < n + 1 := by omega
            have hj' : i + 1 < n + 1 := by omega
            exact (ih1 (Fin.tail w)).mp ht ⟨i, hj⟩ hj'
      · intro h
        refine ⟨?_, (ih1 (Fin.tail w)).mpr ?_⟩
        · have h0 : (0 : Fin (n + 2)).val + 1 < n + 2 := by simp
          simpa using h 0 h0
        intro i hi
        have hi' : i.val + 1 + 1 < n + 2 := by omega
        exact h ⟨i.val + 1, by omega⟩ hi'

private theorem word_normalized_limit : Filter.Tendsto
    (fun n : ℕ => (wordCount n : ℝ) / Real.goldenRatio ^ n)
    Filter.atTop (nhds (Real.goldenRatio ^ 2 / Real.sqrt 5)) := by
  have hp := Real.goldenRatio_pos
  have hq : |Real.goldenConj / Real.goldenRatio| < 1 := by
    rw [abs_div, abs_of_neg Real.goldenConj_neg, abs_of_pos hp, div_lt_one hp]
    linarith [Real.neg_one_lt_goldenConj, Real.one_lt_goldenRatio]
  have hgeom := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have identity (n : ℕ) : (wordCount n : ℝ) / Real.goldenRatio ^ n =
      Real.goldenRatio ^ 2 / Real.sqrt 5 - Real.goldenConj ^ 2 / Real.sqrt 5 *
        (Real.goldenConj / Real.goldenRatio) ^ n := by
    rw [wordCount,
      D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib, Real.coe_fib_eq]
    simp only [pow_add, div_pow]
    field_simp
  simp_rw [identity]
  convert tendsto_const_nhds.sub
    (tendsto_const_nhds.mul hgeom) using 1
  simp

/-- The source grammar is independently recursive. Its root growth and parity are unbounded
statements, with the Binet correction at length plus two rather than at the trace index. -/
theorem golden_words : wordContract := by
  have hp := Real.goldenRatio_pos
  have hsq : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hcount (n : ℕ) : wordCount n = Nat.fib (n + 2) :=
    D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib n
  have hbinet (n : ℕ) : (wordCount n : ℝ) =
      (Real.goldenRatio ^ (n + 2) - Real.goldenConj ^ (n + 2)) / Real.sqrt 5 := by
    rw [hcount, Real.coe_fib_eq]
  have hc : 0 < Real.goldenRatio ^ 2 / Real.sqrt 5 := div_pos (pow_pos hp _) hsq
  have hroot := word_normalized_limit.rpow
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) (Or.inl hc.ne')
  have hgrowth : Tendsto (fun n : ℕ => (wordCount n : ℝ) ^ (1 / (n : ℝ)))
      atTop (nhds Real.goldenRatio) := by
    have h := hroot.mul_const Real.goldenRatio
    simp only [Real.rpow_zero, one_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hpn : (Real.goldenRatio ^ n) ^ (1 / (n : ℝ)) = Real.goldenRatio := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      rw [show (n : ℝ) * (1 / (n : ℝ)) = 1 by field_simp, Real.rpow_one]
    rw [Real.div_rpow (Nat.cast_nonneg _) (pow_nonneg hp.le _), hpn]
    exact div_mul_cancel₀ _ hp.ne'
  refine ⟨?_, hcount, hgrowth, Real.goldenRatio_irrational, rfl, rfl, ?_, ?_, hbinet, ?_⟩
  · intro n w
    refine ⟨admissible_iff_no_adjacent n w, ?_⟩
    rw [admissible_iff_no_adjacent]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    cases w i <;> cases w ⟨i.val + 1, hi⟩ <;>
      simp [adjacency, D5.S1.Scale.fibonacciSubstitution]
  · rw [Real.inv_goldenRatio, neg_neg]
  · intro n
    rw [Real.inv_goldenRatio, ← mul_pow]
    simp
  · intro n
    refine ⟨fun hn => hn.pow_pos Real.goldenConj_ne_zero,
      fun hn => hn.pow_neg_iff.mpr Real.goldenConj_neg, ?_, ?_⟩
    · intro hn
      apply div_neg_of_neg_of_pos _ hsq
      exact neg_neg_of_pos ((hn.add (by decide : Even 2)).pow_pos Real.goldenConj_ne_zero)
    · intro hn
      apply div_pos _ hsq
      exact neg_pos.mpr ((hn.add_even (by decide : Even 2)).pow_neg_iff.mpr Real.goldenConj_neg)

/-- The continuation has two simple poles. Its positive nearest pole is the reciprocal
Perron rate and is also the exact centered convergence boundary of the trace series. -/
theorem golden_continuation : continuationContract := by
  let p : ℝ := Real.goldenRatio
  let r : ℝ := Real.goldenRatio⁻¹
  have hp : 0 < p := Real.goldenRatio_pos
  have hp1 : 1 < p := Real.one_lt_goldenRatio
  have hr : 0 < r := inv_pos.mpr hp
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    linarith [Real.neg_one_lt_goldenConj]
  have hrp : r < p := hr1.trans hp1
  have hmul : (r : ℂ) * (p : ℂ) = 1 := by
    exact_mod_cast (inv_mul_cancel₀ Real.goldenRatio_ne_zero)
  have hdiff : (p : ℂ) - (r : ℂ) = 1 := by
    have h : p - r = 1 := by
      dsimp [p, r]
      rw [Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    exact_mod_cast h
  have hfactor (z : ℂ) : 1 - z - z ^ 2 = -(z - (r : ℂ)) * (z + (p : ℂ)) := by
    linear_combination z * hdiff - hmul
  have hzero (z : ℂ) : 1 - z - z ^ 2 = 0 ↔ z = (r : ℂ) ∨ z = -(p : ℂ) := by
    rw [hfactor]
    simp only [mul_eq_zero, neg_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  have hmer : MeromorphicOn continuation Set.univ := by
    intro z _
    unfold continuation
    fun_prop
  have hoff (z : ℂ) (h1 : z ≠ (r : ℂ)) (h2 : z ≠ -(p : ℂ)) :
      AnalyticAt ℂ continuation z := by
    have hn : 1 - z - z ^ 2 ≠ 0 := fun h => (hzero z).1 h |>.elim h1 h2
    exact analyticAt_const.div (by fun_prop) hn
  have hplus : (r : ℂ) + (p : ℂ) ≠ 0 := by exact_mod_cast (add_pos hr hp).ne'
  have hminus : -(-(p : ℂ) - (r : ℂ)) ≠ 0 := by
    have h : -(p : ℂ) - (r : ℂ) ≠ 0 := by
      exact_mod_cast (show -p - r ≠ 0 by linarith)
    exact neg_ne_zero.mpr h
  have horderR : meromorphicOrderAt (fun z : ℂ => 1 - z - z ^ 2) (r : ℂ) = 1 := by
    rw [funext hfactor, fun_meromorphicOrderAt_mul
      (x := (r : ℂ))
      (f := fun z : ℂ => -(z - (r : ℂ))) (g := fun z : ℂ => z + (p : ℂ))
      (by fun_prop) (by fun_prop),
      ← meromorphicOrderAt_fun_neg, meromorphicOrderAt_id_sub_const]
    have ha : AnalyticAt ℂ (fun z : ℂ => z + (p : ℂ)) (r : ℂ) := by fun_prop
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hplus]
    simp
  have horderN : meromorphicOrderAt (fun z : ℂ => 1 - z - z ^ 2) (-(p : ℂ)) = 1 := by
    rw [funext hfactor, fun_meromorphicOrderAt_mul
      (x := -(p : ℂ))
      (f := fun z : ℂ => -(z - (r : ℂ))) (g := fun z : ℂ => z + (p : ℂ))
      (by fun_prop) (by fun_prop)]
    have ha : AnalyticAt ℂ (fun z : ℂ => -(z - (r : ℂ))) (-(p : ℂ)) := by fun_prop
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hminus]
    simpa [sub_neg_eq_add] using
      (meromorphicOrderAt_id_sub_const (x := -(p : ℂ)))
  have hpoleR : meromorphicOrderAt continuation (r : ℂ) = (-1 : ℤ) := by
    rw [show continuation = (fun z : ℂ => (1 - z - z ^ 2)⁻¹) by
      funext z; exact one_div _, fun_meromorphicOrderAt_inv, horderR]
    norm_num
  have hpoleN : meromorphicOrderAt continuation (-(p : ℂ)) = (-1 : ℤ) := by
    rw [show continuation = (fun z : ℂ => (1 - z - z ^ 2)⁻¹) by
      funext z; exact one_div _, fun_meromorphicOrderAt_inv, horderN]
    norm_num
  have hpoles (z : ℂ) : meromorphicOrderAt continuation z < 0 ↔
      z = (r : ℂ) ∨ z = -(p : ℂ) := by
    constructor
    · intro ho
      by_contra hn
      push Not at hn
      exact not_lt_of_ge (hoff z hn.1 hn.2).meromorphicOrderAt_nonneg ho
    · rintro (rfl | rfl)
      · rw [hpoleR]
        exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)
      · rw [hpoleN]
        exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)
  have hpsi : (Real.goldenConj : ℂ) = -(r : ℂ) := by
    have h : Real.goldenConj = -r := by dsimp [r]; rw [Real.inv_goldenRatio, neg_neg]
    exact_mod_cast h
  have hboundary (n : ℕ) : traceTerm (r : ℂ) n =
      (1 + (-(r : ℂ) ^ 2) ^ (n + 1)) / (n + 1 : ℂ) := by
    rw [traceTerm, golden_local.2.1]
    calc
      ((Real.goldenRatio : ℂ) ^ (n + 1) + (Real.goldenConj : ℂ) ^ (n + 1)) /
          (n + 1 : ℂ) * (r : ℂ) ^ (n + 1) =
          (((p : ℂ) * (r : ℂ)) ^ (n + 1) +
            ((Real.goldenConj : ℂ) * (r : ℂ)) ^ (n + 1)) / (n + 1 : ℂ) := by
        dsimp [p]
        simp only [mul_pow]
        ring
      _ = _ := by rw [mul_comm (p : ℂ), hmul, one_pow, hpsi, neg_mul, ← pow_two]
  have hcorr : Summable (fun n : ℕ => ‖(-(r : ℂ) ^ 2) ^ (n + 1) / (n + 1 : ℂ)‖) := by
    apply summable_norm_log_terms
    rw [norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]
    nlinarith
  have hdiv : ¬ Summable (traceTerm (r : ℂ)) := by
    intro hs
    have h := hs.sub hcorr.of_norm
    have hh : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ)) := h.congr fun n => by
      rw [hboundary]
      ring
    have hh' : Summable (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) := by
      apply Complex.summable_ofReal.mp
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
        Complex.ofReal_natCast] using hh
    apply Real.not_summable_one_div_natCast
    exact (summable_nat_add_iff 1).1 (by simpa only [Nat.cast_add, Nat.cast_one] using hh')
  have hradius : IsGreatest {R : ℝ | 0 ≤ R ∧ ∀ z : ℂ, ‖z‖ < R →
      Summable (fun n : ℕ => ‖traceTerm z n‖)} r := by
    refine ⟨⟨hr.le, fun z hz => (golden_local.2.2.1 ⟨z, hz⟩).2.2.1⟩, ?_⟩
    intro R hR
    by_contra h
    have hRr : ‖(r : ℂ)‖ < R := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
      exact lt_of_not_ge h
    exact hdiv (hR.2 (r : ℂ) hRr).of_norm
  have ht : Matrix.trace adjacency = 1 := by
    have h := congrArg Complex.ofReal
      D5.S1.Eigenstructure.FibonacciMatrixDiscriminant.fibonacci_substitution_trace_det_discriminant.1
    simpa [adjacency, Matrix.trace_fin_two] using h
  have hd : Matrix.det adjacency = -1 := by
    have h := congrArg Complex.ofReal
      D5.S1.Eigenstructure.FibonacciMatrixDiscriminant.fibonacci_substitution_trace_det_discriminant.2.1
    simpa [adjacency, Matrix.det_fin_two] using h
  have hspectrum : spectrum ℂ adjacency = {(Real.goldenRatio : ℂ), (Real.goldenConj : ℂ)} := by
    ext z
    have hs : (Real.goldenRatio : ℂ) + (Real.goldenConj : ℂ) = 1 := by
      exact_mod_cast Real.goldenRatio_add_goldenConj
    have hm : (Real.goldenRatio : ℂ) * (Real.goldenConj : ℂ) = -1 := by
      exact_mod_cast Real.goldenRatio_mul_goldenConj
    have he : (z - (Real.goldenRatio : ℂ)) * (z - (Real.goldenConj : ℂ)) =
        z ^ 2 - z + -1 := by linear_combination -z * hs + hm
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, Matrix.charpoly_fin_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, ht, hd, one_mul]
    rw [← he]
    simp only [mul_eq_zero, sub_eq_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hnp : (‖(p : ℂ)‖₊ : ENNReal) = ENNReal.ofReal p := by
    simpa only [coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hp.le] using
      (ENNReal.ofReal_coe_nnreal (p := ‖(p : ℂ)‖₊)).symm
  have hnr : (‖(Real.goldenConj : ℂ)‖₊ : ENNReal) = ENNReal.ofReal r := by
    rw [hpsi, nnnorm_neg]
    simpa only [coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hr.le] using
      (ENNReal.ofReal_coe_nnreal (p := ‖(r : ℂ)‖₊)).symm
  have hsrad : spectralRadius ℂ adjacency = ENNReal.ofReal p := by
    apply le_antisymm
    · refine iSup_le fun z => iSup_le fun hz => ?_
      have hz' : z = (p : ℂ) ∨ z = (Real.goldenConj : ℂ) := by simpa [hspectrum, p] using hz
      rcases hz' with rfl | rfl
      · exact hnp.le
      · rw [hnr]
        exact ENNReal.ofReal_le_ofReal hrp.le
    · rw [← hnp]
      exact le_iSup_of_le (p : ℂ) (le_iSup_of_le (by simp [hspectrum, p]) le_rfl)
  refine ⟨hmer, hoff, hpoleR, hpoleN, hpoles, hr, hrp, ?_, hboundary,
    hcorr, hdiv, hradius, hspectrum, hsrad, ?_,
    (D5.S1.Scale.fibonacci_substitution_spec 0).2.1⟩
  · intro z hz
    change r ≤ ‖z‖ ∧ (‖z‖ = r ↔ z = (r : ℂ))
    rcases (hpoles z).1 hz with rfl | rfl
    · simp only [Complex.norm_real, Real.norm_of_nonneg hr.le, le_refl, iff_self, and_self]
    · have hn : -(p : ℂ) ≠ (r : ℂ) := by exact_mod_cast (show -p ≠ r by linarith)
      simp only [norm_neg, Complex.norm_real, Real.norm_of_nonneg hp.le, hn, iff_false]
      exact ⟨hrp.le, ne_of_gt hrp⟩
  · intro i
    fin_cases i
    · change 0 < p
      exact hp
    · norm_num [D5.S1.Scale.expandingEigenvector]

/-- Complete mathematical specialization of Part1739, with the retained source interpretations. -/
theorem golden_dynamical_determinant : localContract ∧ continuationContract ∧ wordContract :=
  ⟨golden_local, golden_continuation, golden_words⟩

#print axioms admissible_iff_no_adjacent
#print axioms word_normalized_limit
#print axioms golden_words
#print axioms golden_continuation
#print axioms golden_dynamical_determinant

end D5.S3.Analytic.Characterizations.GoldenDynamicalDeterminant
