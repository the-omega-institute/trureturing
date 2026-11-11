/- GID: D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/BarkerCyclicRepetitionCounting
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barker's generating function and radical formula count cyclic repetition words. -/

/-
admission_basis: open-problem-resolution (#22763; Proved)
Direct frozen dependencies: none (every declaration).
escape_witness: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25339
Utility is none: the conclusion enumerates all lengths by symbolic identities;
the finite letter calculations normalize internal transitions.
The literal adjacent-event predicate is counted by Nat.card, not by a recurrence.
The proof prepends letters; its state records the first event relative to the first letter.

Per-declaration classification (all dependencies are pinned Mathlib):
- eventLabels_cons: proof_shape: bind-only; escape_witness: none; consumers: phaseCount_cons.
- weight_partition: proof_shape: bind-only; escape_witness: none; consumers: count_partition.
- weight_transition: proof_shape: bind-only; escape_witness: none; consumers: phaseCount_step.
- count_partition: proof_shape: bind-only; escape_witness: none; consumers: count_initial, count_recurrence, sourceSeries_spec.
- phaseCount_cons: proof_shape: bind-only; escape_witness: none; consumers: phaseCount_step.
- phaseCount_initial: proof_shape: bind-only; escape_witness: none; consumers: count_initial, stateSeries_equations.
- phaseCount_step: proof_shape: bind-only; escape_witness: none; consumers: count_initial, count_recurrence, stateSeries_equations.
- count_initial: proof_shape: bind-only; escape_witness: none; consumers: radical_count.
- count_recurrence: proof_shape: bind-only; escape_witness: none; consumers: radical_count.
- power_recurrence: proof_shape: bind-only; escape_witness: none; consumers: closed_recurrence.
- closed_recurrence: proof_shape: bind-only; escape_witness: none; consumers: radical_count.
- closed_initial: proof_shape: bind-only; escape_witness: none; consumers: radical_count.
- radical_count: proof_shape: bind-only; escape_witness: none; consumers: result.
- stateSeries_equations: proof_shape: bind-only; escape_witness: none; consumers: sourceSeries_formula.
- sourceSeries_spec: proof_shape: bind-only; escape_witness: none; consumers: sourceSeries_unique, result.
- sourceSeries_unique: proof_shape: bind-only; escape_witness: none; consumers: result.
- sourceSeries_formula: proof_shape: bind-only; escape_witness: none; consumers: result.
- result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
- eventLabels: proof_shape: bind-only; escape_witness: none; consumers: result.
- Admissible: proof_shape: bind-only; escape_witness: none; consumers: result.
- count: proof_shape: bind-only; escape_witness: none; consumers: result.
- IsSourceSeries: proof_shape: bind-only; escape_witness: none; consumers: result.
- claim: proof_shape: bind-only; escape_witness: none; consumers: result.
- Rel: proof_shape: bind-only; escape_witness: none; consumers: result.
- weight: proof_shape: bind-only; escape_witness: none; consumers: result.
- prependEvents: proof_shape: bind-only; escape_witness: none; consumers: result.
- phaseCount: proof_shape: bind-only; escape_witness: none; consumers: result.
- closed: proof_shape: bind-only; escape_witness: none; consumers: result.
- stateSeries: proof_shape: bind-only; escape_witness: none; consumers: result.
- sourceSeries: proof_shape: bind-only; escape_witness: none; consumers: result.
- decidableRel: proof_shape: bind-only; escape_witness: none; consumers: result.
-/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S1.Words.Patterns.BarkerCyclicRepetitionCounting
open scoped BigOperators

/-- Labels at adjacent equal pairs, in their original order; overlapping pairs are retained. -/
def eventLabels (w : List (Fin 8)) : List (Fin 8) :=
  ((w.zip w.tail).filter (fun p => p.1 = p.2)).map Prod.snd

/-- Successive equality-event labels advance by one modulo eight. -/
def Admissible {n : ℕ} (w : Fin n → Fin 8) : Prop :=
  (eventLabels (List.ofFn w)).IsChain (fun a b => b.val = (a.val + 1) % 8)

/-- The literal finite-word count, including the empty word at index zero. -/
noncomputable def count (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → Fin 8 // Admissible w}

/-- The source generating function starts at index one and has constant coefficient zero. -/
def IsSourceSeries (F : PowerSeries ℚ) : Prop :=
  PowerSeries.coeff 0 F = 0 ∧
    ∀ (n : ℕ), 1 ≤ n → PowerSeries.coeff n F = (count n : ℚ)

/-- Both conjectured FORMULA lines of OEIS A268943, at every source index. -/
def claim : Prop :=
  (∃ (F : PowerSeries ℚ), IsSourceSeries F) ∧
  (∀ (F : PowerSeries ℚ), IsSourceSeries F →
    F = 8 * PowerSeries.X * (1 - 5 * PowerSeries.X - 7 * PowerSeries.X ^ 2) *
      ((1 - 7 * PowerSeries.X) *
        (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2))⁻¹) ∧
  (∀ (n : ℕ), 1 ≤ n →
    (count n : ℝ) =
      (-272 * (7 : ℝ) ^ n +
        (153 - 37 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n +
        (3 + Real.sqrt 17) ^ n * (153 + 37 * Real.sqrt 17)) / 34)

private def Rel (a b : Fin 8) : Prop := b.val = (a.val + 1) % 8

private instance decidableRel (a b : Fin 8) : Decidable (Rel a b) :=
  inferInstanceAs (Decidable (b.val = (a.val + 1) % 8))

private def weight (b : Fin 8) (es : List (Fin 8)) (i : Fin 3) : ℕ :=
  if es.IsChain Rel then
    match es with
    | [] => if i = 0 then 1 else 0
    | r :: _ => if i = (if Rel b r then 1 else 2) then 1 else 0
  else 0

private def prependEvents (a b : Fin 8) (es : List (Fin 8)) : List (Fin 8) :=
  if a = b then b :: es else es

private theorem eventLabels_cons (a b : Fin 8) (l : List (Fin 8)) :
    eventLabels (a :: b :: l) = prependEvents a b (eventLabels (b :: l)) := by
  simp [eventLabels, prependEvents, List.zip_cons_cons]; split_ifs <;> simp_all

private theorem weight_partition (b : Fin 8) (es : List (Fin 8)) :
    weight b es 0 + weight b es 1 + weight b es 2 =
      if es.IsChain Rel then 1 else 0 := by
  cases es <;> simp [weight] <;> split_ifs <;> simp_all

private theorem weight_transition (b : Fin 8) (es : List (Fin 8)) :
    (∑ a : Fin 8, weight a (prependEvents a b es) 0) = 7 * weight b es 0 ∧
    (∑ a : Fin 8, weight a (prependEvents a b es) 1) = weight b es 2 ∧
    (∑ a : Fin 8, weight a (prependEvents a b es) 2) =
      weight b es 0 + 8 * weight b es 1 + 6 * weight b es 2 := by
  cases es with
  | nil =>
    simp only [prependEvents, apply_ite, weight]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    fin_cases b <;> norm_num [Rel]
  | cons r rs =>
    by_cases ht : (r :: rs).IsChain Rel
    · simp only [prependEvents, apply_ite, weight, List.isChain_cons_cons, ht, and_true, if_true]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      fin_cases b <;> fin_cases r <;> norm_num [Rel]
    · simp [weight, prependEvents, apply_ite, List.isChain_cons_cons, ht]

private noncomputable def phaseCount (n : ℕ) (i : Fin 3) : ℕ :=
  ∑ w : Fin (n + 1) → Fin 8, weight (w 0) (eventLabels (List.ofFn w)) i

private theorem count_partition (n : ℕ) :
    count (n + 1) = phaseCount n 0 + phaseCount n 1 + phaseCount n 2 := by
  classical
  unfold count phaseCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have hw := (weight_partition (w 0) (eventLabels (List.ofFn w))).symm
  by_cases h : Admissible w
  · have h' : (eventLabels (List.ofFn w)).IsChain Rel := h
    simpa only [ite_eq_left h, ite_eq_left h'] using hw
  · have h' : ¬ (eventLabels (List.ofFn w)).IsChain Rel := h
    simpa only [ite_eq_right h, ite_eq_right h'] using hw

private theorem phaseCount_cons (n : ℕ) (i : Fin 3) :
    phaseCount (n + 1) i =
      ∑ w : Fin (n + 1) → Fin 8,
        ∑ a : Fin 8, weight a (prependEvents a (w 0) (eventLabels (List.ofFn w))) i := by
  classical
  unfold phaseCount
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1 + 1) => Fin 8)).sum_comp
    (fun w => weight (w 0) (eventLabels (List.ofFn w)) i)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro a _
  change weight a (eventLabels (List.ofFn (Fin.cons a w))) i = _
  rw [List.ofFn_cons, List.ofFn_succ (f := w), eventLabels_cons]

private theorem phaseCount_initial :
    phaseCount 0 0 = 8 ∧ phaseCount 0 1 = 0 ∧ phaseCount 0 2 = 0 := by
  simp [phaseCount, List.ofFn_succ, eventLabels, weight]

private theorem phaseCount_step (n : ℕ) :
    phaseCount (n + 1) 0 = 7 * phaseCount n 0 ∧
    phaseCount (n + 1) 1 = phaseCount n 2 ∧
    phaseCount (n + 1) 2 = phaseCount n 0 + 8 * phaseCount n 1 + 6 * phaseCount n 2 := by
  classical
  simp only [phaseCount_cons]
  unfold phaseCount
  constructor
  · simp_rw [(weight_transition _ _).1, Finset.mul_sum]
  constructor
  · simp_rw [(weight_transition _ _).2.1]
  · simp_rw [(weight_transition _ _).2.2, Finset.sum_add_distrib, Finset.mul_sum]

private theorem count_initial : count 1 = 8 ∧ count 2 = 64 ∧ count 3 = 504 := by
  norm_num [count_partition, phaseCount_step, phaseCount_initial]

private theorem count_recurrence (n : ℕ) :
    count (n + 4) + 34 * count (n + 2) + 56 * count (n + 1) =
      13 * count (n + 3) := by
  change count ((n + 3) + 1) + 34 * count ((n + 1) + 1) + 56 * count (n + 1) =
    13 * count ((n + 2) + 1)
  simp only [count_partition, phaseCount_step]
  ring

private noncomputable def closed (n : ℕ) : ℝ :=
  (-272 * (7 : ℝ) ^ n +
    (153 - 37 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n +
    (3 + Real.sqrt 17) ^ n * (153 + 37 * Real.sqrt 17)) / 34

private theorem power_recurrence (t : ℝ) (ht : t ^ 3 + 34 * t + 56 = 13 * t ^ 2) (n : ℕ) :
    t ^ (n + 3) + 34 * t ^ (n + 1) + 56 * t ^ n = 13 * t ^ (n + 2) := by
  let E : LinearRecurrence ℝ := ⟨3, ![-56, -34, 13]⟩
  have root : E.charPoly.IsRoot t := by
    simp [E, LinearRecurrence.charPoly, Polynomial.IsRoot, Fin.sum_univ_succ]
    linarith
  have h := ((E.geom_sol_iff_root_charPoly t).mpr root) n
  simp [E, Fin.sum_univ_succ] at h
  linarith

private theorem closed_recurrence (n : ℕ) :
    closed (n + 3) + 34 * closed (n + 1) + 56 * closed n = 13 * closed (n + 2) := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hp : (3 + Real.sqrt 17) ^ 3 + 34 * (3 + Real.sqrt 17) + 56 =
      13 * (3 + Real.sqrt 17) ^ 2 := by
    linear_combination (Real.sqrt 17 - 4) * hs
  have hm : (3 - Real.sqrt 17) ^ 3 + 34 * (3 - Real.sqrt 17) + 56 =
      13 * (3 - Real.sqrt 17) ^ 2 := by
    linear_combination (-Real.sqrt 17 - 4) * hs
  have h7 := power_recurrence 7 (by norm_num) n
  have hp' := power_recurrence _ hp n
  have hm' := power_recurrence _ hm n
  unfold closed
  linear_combination (-272 / 34 : ℝ) * h7 +
    ((153 - 37 * Real.sqrt 17) / 34) * hm' +
    ((153 + 37 * Real.sqrt 17) / 34) * hp'

private theorem closed_initial : closed 1 = 8 ∧ closed 2 = 64 ∧ closed 3 = 504 := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 17) ^ 3 = 17 * Real.sqrt 17 := by
    exact (pow_succ (Real.sqrt 17) 2).trans
      (congrArg (fun t : ℝ => t * Real.sqrt 17) hs)
  unfold closed
  constructor
  · nlinarith [hs]
  constructor
  · nlinarith [hs]
  · nlinarith [hs, hs3]

private theorem radical_count (n : ℕ) : (count (n + 1) : ℝ) = closed (n + 1) := by
  let E : LinearRecurrence ℝ := ⟨3, ![-56, -34, 13]⟩
  have hu : E.IsSolution (fun k => (count (k + 1) : ℝ)) := by
    intro k
    have h : (count (k + 4) : ℝ) + 34 * (count (k + 2) : ℝ) +
        56 * (count (k + 1) : ℝ) = 13 * (count (k + 3) : ℝ) := by
      exact_mod_cast count_recurrence k
    simp [E, Fin.sum_univ_succ]
    linarith
  have hv : E.IsSolution (fun k => closed (k + 1)) := by
    intro k
    have h := closed_recurrence (k + 1)
    simp [E, Fin.sum_univ_succ]
    linarith
  have heq := (E.eq_iff_eqOn_range_order
    (fun k => (count (k + 1) : ℝ)) (fun k => closed (k + 1)) hu hv).2
  apply congrFun (heq ?_) n
  intro k hk
  have hk' : k < 3 := Finset.mem_range.mp hk
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> simp [count_initial, closed_initial]

private noncomputable def stateSeries (i : Fin 3) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (phaseCount n i : ℚ))

private theorem stateSeries_equations :
    stateSeries 0 = 8 + 7 * (PowerSeries.X * stateSeries 0) ∧
    stateSeries 1 = PowerSeries.X * stateSeries 2 ∧
    stateSeries 2 = PowerSeries.X * (stateSeries 0 + 8 * stateSeries 1 + 6 * stateSeries 2) := by
  constructor
  · ext n
    cases n with
    | zero => simp [stateSeries, phaseCount_initial, show (8 : PowerSeries ℚ) = PowerSeries.C 8 from rfl]
    | succ n =>
      simpa [stateSeries, show (8 : PowerSeries ℚ) = PowerSeries.C 8 from rfl, Nat.cast_mul] using
        congrArg (fun k : ℕ => (k : ℚ)) (phaseCount_step n).1
  constructor
  · ext n
    cases n with
    | zero => simp [stateSeries, phaseCount_initial]
    | succ n =>
      simpa [stateSeries] using congrArg (fun k : ℕ => (k : ℚ)) (phaseCount_step n).2.1
  · ext n
    cases n with
    | zero => simp [stateSeries, phaseCount_initial, show (8 : PowerSeries ℚ) = PowerSeries.C 8 from rfl]
    | succ n =>
      simpa [stateSeries, Nat.cast_add, Nat.cast_mul] using
        congrArg (fun k : ℕ => (k : ℚ)) (phaseCount_step n).2.2

private noncomputable def sourceSeries : PowerSeries ℚ :=
  PowerSeries.X * (stateSeries 0 + stateSeries 1 + stateSeries 2)

private theorem sourceSeries_spec : IsSourceSeries sourceSeries := by
  constructor
  · simp [sourceSeries]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [sourceSeries, stateSeries, count_partition, Nat.cast_add]

private theorem sourceSeries_unique (F : PowerSeries ℚ) (hF : IsSourceSeries F) :
    F = sourceSeries := by
  ext n
  cases n with
  | zero => exact hF.1.trans sourceSeries_spec.1.symm
  | succ n => exact (hF.2 _ (by omega)).trans (sourceSeries_spec.2 _ (by omega)).symm

private theorem sourceSeries_formula :
    sourceSeries = 8 * PowerSeries.X * (1 - 5 * PowerSeries.X - 7 * PowerSeries.X ^ 2) *
      ((1 - 7 * PowerSeries.X) * (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2))⁻¹ := by
  have hu : (1 - 7 * PowerSeries.X) * stateSeries 0 = (8 : PowerSeries ℚ) := by
    linear_combination stateSeries_equations.1
  have ha := stateSeries_equations.2.1
  have hb : stateSeries 2 * (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2) =
      PowerSeries.X * stateSeries 0 := by
    have h := stateSeries_equations.2.2
    rw [ha] at h
    linear_combination h
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
    PowerSeries.constantCoeff ((1 - 7 * PowerSeries.X) *
      (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2) : PowerSeries ℚ) ≠ 0)).2
  unfold sourceSeries
  rw [ha]
  calc
    PowerSeries.X * (stateSeries 0 + PowerSeries.X * stateSeries 2 + stateSeries 2) *
        ((1 - 7 * PowerSeries.X) * (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (stateSeries 0 * (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2) +
        (1 + PowerSeries.X) * (stateSeries 2 * (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2))) *
        (1 - 7 * PowerSeries.X) := by ring
    _ = PowerSeries.X * (stateSeries 0 * (1 - 6 * PowerSeries.X - 8 * PowerSeries.X ^ 2) +
        (1 + PowerSeries.X) * (PowerSeries.X * stateSeries 0)) * (1 - 7 * PowerSeries.X) := by rw [hb]
    _ = PowerSeries.X * (1 - 5 * PowerSeries.X - 7 * PowerSeries.X ^ 2) *
        ((1 - 7 * PowerSeries.X) * stateSeries 0) := by ring
    _ = 8 * PowerSeries.X * (1 - 5 * PowerSeries.X - 7 * PowerSeries.X ^ 2) := by rw [hu]; ring

theorem result : claim := by
  refine ⟨⟨sourceSeries, sourceSeries_spec⟩, ?_, ?_⟩
  · intro F hF
    exact (sourceSeries_unique F hF).trans sourceSeries_formula
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact radical_count k

end D5.S1.Words.Patterns.BarkerCyclicRepetitionCounting
