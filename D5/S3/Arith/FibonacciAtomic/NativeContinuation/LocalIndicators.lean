/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.L2Space, mathlib/module/Mathlib.Probability.ProbabilityMassFunction.Constructions]
   utility: none
   digest: Every native position has positive five-mode mass and a strict three-indicator L2 Gram. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.LocalIndicators

open scoped BigOperators
open LiteralWindowEnd (Window bits first last)
open NullReplyFiber (highBits)
open JointLaw (Source law mass embed bitWindow)
open D5.S3.Arith.ZeckendorfFutureKernel (legal)
open MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace Window := ⊤

private theorem isolated_legal (n : ℕ) (i : Fin n) (a : Window) :
    legal false (highBits (List.ofFn (fun k => if k = i then a else .zero))) := by
  have nulls (k : ℕ) (s : Bool) : legal s (highBits (List.replicate k .zero)) := by
    cases k with
    | zero => simp [highBits, legal]
    | succ k =>
      have h := (embed (k + 1) (fun _ => 0)).property
      simpa [embed, bitWindow, List.ofFn_const, List.replicate_succ, highBits,
        bits, legal] using h
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have tail : (fun k : Fin n => if k.succ = (0 : Fin (n + 1)) then a else .zero) =
          fun _ => .zero := by funext k; simp
      rw [List.ofFn_succ]
      simp only [ite_true, tail, List.ofFn_const]
      have h := nulls n (first a)
      cases a <;> simpa [highBits, bits, first, legal] using h
    · rw [List.ofFn_succ]
      simpa [highBits, bits, legal, Fin.succ_inj,
        (Fin.succ_ne_zero j).symm] using ih j

/-- Keep the original position and put the selected mode there, with every other mode null. -/
def isolated {n : ℕ} (i : Fin n) (a : Window) : Source n :=
  ⟨fun k => if k = i then a else .zero, isolated_legal n i a⟩

/-- The original source law's mass at one original window position. -/
def modeMass (n : ℕ) (mix : ℝ) (ε : ℤ) (i : Fin n) (a : Window) : ℝ :=
  mass (law n mix ε) (fun w => w.val i = a)

private theorem law_valid (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) :
    (∀ w : Source n, 0 < law n mix ε w) ∧ (∑ w, law n mix ε w) = 1 :=
  (JointLaw.native_probability_separation n hn mix hl hu).1 ε (by simpa using hε)

private theorem mode_positive (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1)
    (i : Fin n) (a : Window) : 0 < modeMass n mix ε i a := by
  have hp := (law_valid n hn mix hl hu ε hε).1
  apply Finset.sum_pos'
  · intro w _
    split
    · exact (hp w).le
    · exact le_rfl
  · refine ⟨isolated i a, Finset.mem_univ _, ?_⟩
    simpa [isolated] using hp (isolated i a)

private theorem marginal_sum (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) (i : Fin n) :
    (∑ a : Window, modeMass n mix ε i a) = 1 := by
  simp only [modeMass, mass]
  rw [Finset.sum_comm]
  simp_rw [eq_comm]
  simpa using (law_valid n hn mix hl hu ε hε).2.symm

/-- The actual marginal probability measure, on the same original five modes. -/
def marginalMeasure (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1)
    (i : Fin n) : Measure Window :=
  (PMF.ofFintype (fun a => ENNReal.ofReal (modeMass n mix ε i a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ =>
      (mode_positive n hn mix hl hu ε hε i a).le), marginal_sum n hn mix hl hu ε hε i]
    norm_num)).toMeasure

instance marginal_finite (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) (i : Fin n) :
    IsProbabilityMeasure (marginalMeasure n hn mix hl hu ε hε i) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Occupancy events in the original x, y, z order; the indicators are not centered. -/
def occupancy : Fin 3 → Set Window
  | 0 => {.low, .ends}
  | 1 => {.high, .ends}
  | 2 => {.middle}

/-- All three vectors live in the actual marginal's one L2 space. -/
def normalizedIndicator (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1)
    (i : Fin n) (r : Fin 3) : Lp ℝ 2 (marginalMeasure n hn mix hl hu ε hε i) :=
  (Real.sqrt ((marginalMeasure n hn mix hl hu ε hε i).real (occupancy r)))⁻¹ •
    indicatorConstLp (s := occupancy r) 2 MeasurableSet.of_discrete
      (by finiteness) (1 : ℝ)

/-- The three-index Gram of the actual noncentered normalized indicators. -/
def localGram (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1)
    (i : Fin n) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun r s => inner ℝ (normalizedIndicator n hn mix hl hu ε hε i r)
    (normalizedIndicator n hn mix hl hu ε hε i s)

/-- The three actual occupancy means, in the original x, y, z order. -/
def means (n : ℕ) (mix : ℝ) (ε : ℤ) (i : Fin n) : Fin 3 → ℝ
  | 0 => modeMass n mix ε i .low + modeMass n mix ε i .ends
  | 1 => modeMass n mix ε i .high + modeMass n mix ε i .ends
  | 2 => modeMass n mix ε i .middle

/-- The same-window endpoint mass divided by the geometric mean of X and Y. -/
def coupling (n : ℕ) (mix : ℝ) (ε : ℤ) (i : Fin n) : ℝ :=
  modeMass n mix ε i .ends / Real.sqrt (means n mix ε i 0 * means n mix ε i 1)

private theorem window_sum (f : Window → ℝ) :
    (∑ a, f a) = f .zero + f .low + f .middle + f .ends + f .high := by
  change (∑ a ∈ ({.zero, .low, .middle, .ends, .high} : Finset Window), f a) = _
  simp
  ring

section Actual
variable (n : ℕ) (hn : 3 ≤ n) (mix : ℝ) (hl : 0 < mix) (hu : mix < 1)
  (ε : ℤ) (hε : ε = -1 ∨ ε = 1) (i : Fin n)

private theorem measure_real (E : Set Window) :
    (marginalMeasure n hn mix hl hu ε hε i).real E =
      ∑ a, if a ∈ E then modeMass n mix ε i a else 0 := by
  have nonneg (a : Window) : 0 ≤ (if a ∈ E then modeMass n mix ε i a else 0) := by
    split
    · exact (mode_positive n hn mix hl hu ε hε i a).le
    · exact le_rfl
  have formula : marginalMeasure n hn mix hl hu ε hε i E =
      ENNReal.ofReal (∑ a, if a ∈ E then modeMass n mix ε i a else 0) := by
    simp only [marginalMeasure, PMF.toMeasure_apply_fintype, Set.indicator_apply,
      PMF.ofFintype_apply]
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => nonneg a)]
    apply Finset.sum_congr rfl
    intro a _
    split <;> simp_all
  rw [Measure.real, formula, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun a _ => nonneg a))]

private theorem measure_source (E : Set Window) :
    (marginalMeasure n hn mix hl hu ε hε i).real E =
      mass (law n mix ε) (fun w => w.val i ∈ E) := by
  classical
  letI : DecidableEq Window := fun a b => Classical.propDecidable (a = b)
  rw [measure_real]
  simp only [modeMass, mass]
  rw [window_sum]
  have pull (a : Window) :
      (if a ∈ E then ∑ w : Source n, if w.val i = a then law n mix ε w else 0 else 0) =
      ∑ w : Source n, if a ∈ E ∧ w.val i = a then law n mix ε w else 0 := by
    by_cases h : a ∈ E <;> simp [h]
  rw [pull .zero, pull .low, pull .middle, pull .ends, pull .high]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have identity (a : Window) :
      (if .zero ∈ E ∧ a = .zero then law n mix ε w else 0) +
      (if .low ∈ E ∧ a = .low then law n mix ε w else 0) +
      (if .middle ∈ E ∧ a = .middle then law n mix ε w else 0) +
      (if .ends ∈ E ∧ a = .ends then law n mix ε w else 0) +
      (if .high ∈ E ∧ a = .high then law n mix ε w else 0) =
      if a ∈ E then law n mix ε w else 0 := by
    cases a <;> simp
  exact identity (w.val i)

private theorem mean_measure (r : Fin 3) :
    (marginalMeasure n hn mix hl hu ε hε i).real (occupancy r) = means n mix ε i r := by
  rw [measure_real, window_sum]
  fin_cases r <;> simp [occupancy, means] <;> ring

private theorem inter_measure (r s : Fin 3) :
    (marginalMeasure n hn mix hl hu ε hε i).real (occupancy r ∩ occupancy s) =
      if r = s then means n mix ε i r
      else if (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) then modeMass n mix ε i .ends else 0 := by
  rw [measure_real, window_sum]
  fin_cases r <;> fin_cases s <;> simp [occupancy, means] <;> ring

include hn hl hu hε in
private theorem means_positive (r : Fin 3) : 0 < means n mix ε i r := by
  have hp := mode_positive n hn mix hl hu ε hε i
  fin_cases r
  · exact add_pos (hp .low) (hp .ends)
  · exact add_pos (hp .high) (hp .ends)
  · exact hp .middle

include hn hl hu hε in
private theorem coupling_bounds : 0 < coupling n mix ε i ∧ coupling n mix ε i < 1 := by
  have hlp := mode_positive n hn mix hl hu ε hε i .low
  have hhp := mode_positive n hn mix hl hu ε hε i .high
  have hep := mode_positive n hn mix hl hu ε hε i .ends
  have hX := means_positive n hn mix hl hu ε hε i 0
  have hY := means_positive n hn mix hl hu ε hε i 1
  have hXY : 0 < means n mix ε i 0 * means n mix ε i 1 := mul_pos hX hY
  have hs := Real.sqrt_pos.2 hXY
  have hs2 := Real.sq_sqrt hXY.le
  have hk : modeMass n mix ε i .ends <
      Real.sqrt (means n mix ε i 0 * means n mix ε i 1) := by
    have ht : modeMass n mix ε i .ends ^ 2 < means n mix ε i 0 * means n mix ε i 1 := by
      simp only [means]
      nlinarith [mul_pos hlp hhp, mul_pos hlp hep, mul_pos hhp hep]
    nlinarith
  exact ⟨div_pos hep hs, (div_lt_one hs).2 hk⟩

private theorem gram_entries (r s : Fin 3) :
    localGram n hn mix hl hu ε hε i r s =
      if r = s then 1
      else if (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) then coupling n mix ε i else 0 := by
  simp only [localGram, normalizedIndicator, real_inner_smul_left, inner_smul_right]
  rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  rw [mean_measure, mean_measure, inter_measure]
  have hp := means_positive n hn mix hl hu ε hε i
  by_cases hrs : r = s
  · subst s
    simp only [↓reduceIte]
    have hsq := Real.sq_sqrt (hp r).le
    have hne := (Real.sqrt_pos.2 (hp r)).ne'
    field_simp [hne]
    nlinarith
  · simp only [if_neg hrs]
    by_cases h : (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0)
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        simp [coupling, Real.sqrt_mul (hp 0).le]
        ring
    · simp [h]

/-- The complete original-source marginal has positive mass on all five modes.
Its three noncentered normalized indicators have precisely the strict local Gram. -/
theorem native_local_indicator_gram :
    (∀ E : Set Window, (marginalMeasure n hn mix hl hu ε hε i).real E =
      mass (law n mix ε) (fun w => w.val i ∈ E)) ∧
    (∀ a : Window, 0 < modeMass n mix ε i a) ∧
    (∀ r : Fin 3, 0 < means n mix ε i r) ∧
    (0 < coupling n mix ε i ∧ coupling n mix ε i < 1) ∧
    localGram n hn mix hl hu ε hε i =
      !![1, coupling n mix ε i, 0; coupling n mix ε i, 1, 0; 0, 0, 1] := by
  refine ⟨measure_source n hn mix hl hu ε hε i,
    mode_positive n hn mix hl hu ε hε i, means_positive n hn mix hl hu ε hε i,
    coupling_bounds n hn mix hl hu ε hε i, ?_⟩
  ext r s
  rw [gram_entries]
  fin_cases r <;> fin_cases s <;> simp

#print axioms native_local_indicator_gram
#print axioms isolated_legal

end Actual

end
end D5.S3.Arith.FibonacciAtomic.NativeContinuation.LocalIndicators
