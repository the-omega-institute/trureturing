/- GID: D5/S3/Combinatorics/PatternMatchings/P13Series
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Series
   mirror-E: none(waiver:literal-completion-generating-series)
   anchors: []
   utility: none
   digest: Literal completion counts yield the catalytic functional equation. -/

import D5.S3.Combinatorics.PatternMatchings.P13Counts
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

open PowerSeries
open PowerSeries.WithPiTopology
open scoped PowerSeries.WithPiTopology

local instance : UniformSpace ℚ := ⊥
local instance : UniformSpace (Polynomial ℚ) := ⊥

/-- Closures mark literal completions from the old single block. -/
noncomputable def completionSeries (m : ℕ) : PowerSeries ℚ :=
  mk fun d => (c m d : ℚ)

/-- The original perfect-matching carrier supplies the ordinary counting series. -/
noncomputable def actualSeries : PowerSeries ℚ :=
  mk fun d => (actualCount d : ℚ)

/-- At closure degree d, only the old block sizes from zero through d occur. -/
noncomputable def countPolynomial (d : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.range (d + 1), Polynomial.monomial m (c m d : ℚ)

/-- The old block variable is polynomial at every closure degree. -/
noncomputable def completionBivariate : PowerSeries (Polynomial ℚ) :=
  mk countPolynomial

/-- A polynomial variable inside the coefficient ring. -/
noncomputable def blockMarker : PowerSeries (Polynomial ℚ) := C Polynomial.X

/-- The unit inverse of 1-zu, formed in the closure-adic series ring. -/
noncomputable def reciprocalMarker : PowerSeries (Polynomial ℚ) :=
  rescale Polynomial.X (invOneSubPow (Polynomial ℚ) 1).val

private noncomputable def coefficientEvaluation (v : PowerSeries (Polynomial ℚ)) :
    Polynomial ℚ →+* PowerSeries (Polynomial ℚ) :=
  Polynomial.eval₂RingHom (C.comp Polynomial.C) v

/-- Polynomial coefficient evaluation allows a nonzero constant term in v.
Only the outer series variable is evaluated at the topologically nilpotent X. -/
noncomputable def evaluateBlock (v : PowerSeries (Polynomial ℚ)) :
    PowerSeries (Polynomial ℚ) →+* PowerSeries (Polynomial ℚ) :=
  eval₂Hom (show Continuous (coefficientEvaluation v) from continuous_of_discreteTopology)
    (HasEval.X (R := Polynomial ℚ))

private theorem packed_coeff (d m : ℕ) :
    (coeff d completionBivariate).coeff m = (c m d : ℚ) := by
  classical
  simp only [completionBivariate, coeff_mk, countPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  by_cases h : m < d + 1
  · simp [h, Finset.mem_range]
  · have hz := c_support (m := m) (d := d) (by omega)
    simp [Finset.mem_range, h, hz]

private theorem actual_boundary :
    completionSeries 0 = actualSeries ∧ completionSeries 0 = 1 + completionSeries 1 := by
  have counts (d : ℕ) : c 0 d = actualCount d := by
    cases d with
    | zero => rw [c_zero_zero, actualCount_continuation.1]
    | succ d =>
      rw [c_empty_single (d + 1) (by omega)]
      have ht := c_triangular 1 (d + 1) (by omega) (by omega)
      have ha := actualCount_continuation.2 (d + 1) (by omega)
      have ht' : c 1 (d + 1) = c 2 (d + 1) + c 0 d +
          ∑ j ∈ Finset.Icc 1 d, c j d := by simpa using ht
      exact ht'.trans ha.symm
  constructor
  · ext d
    simp [completionSeries, actualSeries, counts]
  · ext d
    cases d with
    | zero => simp [completionSeries, c_zero_zero, c_support (m := 1) (d := 0) (by omega)]
    | succ d => simp [completionSeries, c_empty_single (d + 1) (by omega)]

private theorem reciprocal_unit :
    (1 - X * blockMarker) * reciprocalMarker = 1 := by
  have h := (invOneSubPow (Polynomial ℚ) 1).inv_val
  rw [invOneSubPow_inv_eq_one_sub_pow, pow_one] at h
  have hr := congrArg (rescale Polynomial.X) h
  simpa [reciprocalMarker, blockMarker, map_mul, map_sub, rescale_X, mul_comm] using hr

private theorem reciprocal_power_coeff (j a : ℕ) (hj : 0 < j) :
    coeff a (reciprocalMarker ^ j) =
      Polynomial.monomial a ((a + j - 1).choose a : ℚ) := by
  have hp : (invOneSubPow (Polynomial ℚ) 1).val ^ j =
      (invOneSubPow (Polynomial ℚ) j).val := by
    clear hj
    induction j with
    | zero => simp [invOneSubPow_zero]
    | succ j ih =>
      rw [pow_succ, ih, invOneSubPow_add, Units.val_mul]
  rw [reciprocalMarker, ← map_pow, hp,
    invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos (Polynomial ℚ) j hj,
    coeff_rescale, coeff_mk]
  have hn : j - 1 + a = a + j - 1 := by omega
  have hs : (j - 1 + a).choose (j - 1) = (a + j - 1).choose a := by
    rw [Nat.choose_symm_of_eq_add (show j - 1 + a = (j - 1) + a from rfl), hn]
  rw [hs, ← Polynomial.C_eq_natCast, mul_comm, Polynomial.C_mul_X_pow_eq_monomial]

private theorem evaluated_coeff (v : PowerSeries (Polynomial ℚ)) (N : ℕ) :
    coeff N (evaluateBlock v completionBivariate) =
      ∑ d ∈ Finset.range (N + 1),
        coeff (N - d) (coefficientEvaluation v (coeff d completionBivariate)) := by
  classical
  have hs := (hasSum_iff_hasSum_coeff (Polynomial ℚ)).mp
    (hasSum_eval₂
      (show Continuous (coefficientEvaluation v) from continuous_of_discreteTopology)
      (HasEval.X (R := Polynomial ℚ)) completionBivariate) N
  have hf := hasSum_sum_of_ne_finset_zero
    (L := SummationFilter.unconditional ℕ) (s := Finset.range (N + 1))
    (f := fun d => coeff N (coefficientEvaluation v (coeff d completionBivariate) * X ^ d))
    (by
      intro d hd
      rw [coeff_mul_X_pow', if_neg]
      simp only [Finset.mem_range] at hd
      omega)
  have he : coeff N (evaluateBlock v completionBivariate) =
      ∑ d ∈ Finset.range (N + 1),
        coeff N (coefficientEvaluation v (coeff d completionBivariate) * X ^ d) := by
    simpa only [evaluateBlock, coe_eval₂Hom] using hs.unique hf
  rw [he]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coeff_mul_X_pow', if_pos (by simp only [Finset.mem_range] at hd; omega)]

private theorem evaluated_row_coeff (v : PowerSeries (Polynomial ℚ)) (d n : ℕ) :
    coeff n (coefficientEvaluation v (coeff d completionBivariate)) =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C (c j d : ℚ) * coeff n (v ^ j) := by
  simp only [completionBivariate, coeff_mk, countPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [coefficientEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    RingHom.comp_apply, coeff_C_mul]

private theorem reciprocal_row_coeff (d n : ℕ) :
    coeff n (coefficientEvaluation reciprocalMarker (coeff d completionBivariate)) =
      (∑ j ∈ Finset.range d,
        Polynomial.monomial n ((c (j + 1) d : ℚ) * ((n + j).choose n : ℚ))) +
      if n = 0 then Polynomial.C (c 0 d : ℚ) else 0 := by
  classical
  rw [evaluated_row_coeff, Finset.sum_range_succ']
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [reciprocal_power_coeff (j + 1) n (by omega)]
    rw [show n + (j + 1) - 1 = n + j by omega, Polynomial.C_mul_monomial]
  · simp [coeff_one]

private theorem substituted_coeff (N a : ℕ) :
    (coeff N (evaluateBlock reciprocalMarker completionBivariate)).coeff a =
      (if a = 0 then (c 0 N : ℚ) else 0) +
      if a ≤ N then
        ∑ j ∈ Finset.range (N - a),
          (c (j + 1) (N - a) : ℚ) * ((a + j).choose a : ℚ)
      else 0 := by
  classical
  rw [evaluated_coeff]
  simp only [reciprocal_row_coeff, Polynomial.finsetSum_coeff, Polynomial.coeff_add,
    Polynomial.coeff_monomial]
  rw [Finset.sum_add_distrib]
  have constantPart :
      (∑ d ∈ Finset.range (N + 1),
        (if N - d = 0 then Polynomial.C (c 0 d : ℚ) else 0).coeff a) =
        if a = 0 then (c 0 N : ℚ) else 0 := by
    rw [Finset.sum_eq_single N]
    · simp
    · intro d hd hne
      have hn : N - d ≠ 0 := by simp only [Finset.mem_range] at hd; omega
      simp [hn]
    · simp
  rw [constantPart, add_comm]
  apply congrArg ((if a = 0 then (c 0 N : ℚ) else 0) + ·)
  by_cases ha : a ≤ N
  · rw [if_pos ha, Finset.sum_eq_single (N - a)]
    · have hn : N - (N - a) = a := by omega
      simp [hn]
    · intro d hd hne
      have hn : N - d ≠ a := by simp only [Finset.mem_range] at hd; omega
      simp [hn]
    · simp only [Finset.mem_range]
      omega
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro d hd
    have hn : N - d ≠ a := by omega
    simp [hn]

private theorem triangular_series_coeff (a N : ℕ) :
    (c (a + 1) (N + 1) : ℚ) - (c (a + 2) (N + 1) : ℚ) =
      (c a N : ℚ) + if a ≤ N then
        ∑ j ∈ Finset.range (N - a),
          (c (j + 1) (N - a) : ℚ) * ((a + j).choose a : ℚ)
      else 0 := by
  classical
  by_cases ha : a ≤ N
  · rw [if_pos ha]
    have ht := c_triangular (a + 1) (N + 1) (by omega) (by omega)
    have hs : N + 1 - (a + 1) = N - a := by omega
    simp only [Nat.add_sub_cancel, hs] at ht
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range] at ht
    simp only [Nat.add_sub_cancel, Nat.add_comm 1] at ht
    have hi (j : ℕ) : a + 1 + (j + 1) - 2 = a + j := by omega
    simp_rw [hi] at ht
    have hq := congrArg (fun n : ℕ => (n : ℚ)) ht
    push_cast at hq
    have hc : (∑ j ∈ Finset.range (N - a),
        ((a + j).choose a : ℚ) * (c (j + 1) (N - a) : ℚ)) =
        ∑ j ∈ Finset.range (N - a),
          (c (j + 1) (N - a) : ℚ) * ((a + j).choose a : ℚ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _
    rw [hc] at hq
    linear_combination hq
  · have h0 := c_support (m := a) (d := N) (by omega)
    have h1 := c_support (m := a + 1) (d := N + 1) (by omega)
    have h2 := c_support (m := a + 2) (d := N + 1) (by omega)
    simp [ha, h0, h1, h2]

private theorem functional_equation :
    (blockMarker - 1 - X * blockMarker ^ 2) * completionBivariate =
      blockMarker - (1 + X * blockMarker ^ 2) * actualSeries.map Polynomial.C +
        X * blockMarker ^ 2 * evaluateBlock reciprocalMarker completionBivariate := by
  let A := actualSeries.map Polynomial.C
  let K := evaluateBlock reciprocalMarker completionBivariate
  have hA (d : ℕ) : coeff d A = Polynomial.C (c 0 d : ℚ) := by
    rw [show A = (completionSeries 0).map Polynomial.C from
      congrArg (PowerSeries.map Polynomial.C) actual_boundary.1.symm, coeff_map]
    simp only [completionSeries, coeff_mk]
  have hf0 : coeff 0 completionBivariate = 1 := by
    ext m
    rw [packed_coeff]
    cases m with
    | zero => simp [c_zero_zero]
    | succ m => simp [Polynomial.coeff_one,
        c_support (m := m + 1) (d := 0) (by omega)]
  have hf0' : constantCoeff completionBivariate = 1 := by
    simpa only [coeff_zero_eq_constantCoeff_apply] using hf0
  have hA0 : constantCoeff A = 1 := by
    simpa only [coeff_zero_eq_constantCoeff_apply, c_zero_zero,
      Nat.cast_one, Polynomial.C_1] using hA 0
  have he : (blockMarker - 1) * completionBivariate + A - blockMarker =
      X * blockMarker ^ 2 * (completionBivariate + K - A) := by
    apply PowerSeries.ext
    intro d
    cases d with
    | zero =>
      simp [blockMarker, sub_mul, mul_assoc, hf0', hA0]
    | succ N =>
      have hz (s : PowerSeries (Polynomial ℚ)) :
          coeff (N + 1) (X * blockMarker ^ 2 * s) =
            Polynomial.X ^ 2 * coeff N s := by
        rw [blockMarker, mul_assoc, ← map_pow, coeff_succ_X_mul, coeff_C_mul]
      rw [hz]
      simp only [map_sub, map_add]
      rw [sub_mul, map_sub, blockMarker, coeff_C_mul, one_mul, hA, coeff_C]
      simp only [Nat.succ_ne_zero, ↓reduceIte, sub_zero]
      apply Polynomial.ext
      intro k
      cases k with
      | zero =>
        simp [Polynomial.coeff_add, Polynomial.coeff_sub, packed_coeff]
      | succ k =>
        cases k with
        | zero =>
          simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
            Polynomial.coeff_X_pow_mul', packed_coeff, c_empty_single (N + 1) (by omega)]
        | succ a =>
          have hk : a + 1 + 1 = a + 2 := by omega
          rw [hk, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
            packed_coeff, packed_coeff, Polynomial.coeff_C, if_neg (by omega), add_zero,
            Polynomial.coeff_X_pow_mul', if_pos (by omega)]
          simp only [Nat.add_sub_cancel, Polynomial.coeff_sub, Polynomial.coeff_add,
            packed_coeff, hA, Polynomial.coeff_C]
          rw [show (coeff N K).coeff a = _ from substituted_coeff N a]
          rw [triangular_series_coeff]
          ring
  change (blockMarker - 1 - X * blockMarker ^ 2) * completionBivariate =
    blockMarker - (1 + X * blockMarker ^ 2) * A + X * blockMarker ^ 2 * K
  linear_combination he

/-- Concrete completion series, their exact low-degree boundary, and the actual
matching functional equation. No recurrence or functional equation is a premise. -/
theorem completion_functional_equation :
    (∀ m : ℕ, (m : ℕ∞) ≤ (completionSeries m).order ∧
      coeff m (completionSeries m) = 1) ∧
    (∀ d : ℕ, (coeff d completionBivariate).natDegree ≤ d) ∧
    completionSeries 0 = actualSeries ∧
    completionSeries 0 = 1 + completionSeries 1 ∧
    (1 - X * blockMarker) * reciprocalMarker = 1 ∧
    (blockMarker - 1 - X * blockMarker ^ 2) * completionBivariate =
      blockMarker - (1 + X * blockMarker ^ 2) * actualSeries.map Polynomial.C +
        X * blockMarker ^ 2 * evaluateBlock reciprocalMarker completionBivariate := by
  classical
  refine ⟨?_, ?_, actual_boundary.1, actual_boundary.2, reciprocal_unit,
    functional_equation⟩
  · intro m
    constructor
    · apply nat_le_order
      intro i hi
      simp [completionSeries, c_support hi]
    · simp [completionSeries, c_diagonal]
  · intro d
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [packed_coeff, c_support hm, Nat.cast_zero]

end D5.S3.Combinatorics.PatternMatchings.P13
