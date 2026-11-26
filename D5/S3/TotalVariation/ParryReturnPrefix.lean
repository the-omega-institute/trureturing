/- GID: D5/S3/TotalVariation/ParryReturnPrefix
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryReturnPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Return-duration cylinders give the probability of raw prefixes ending inside a run. -/

import D5.S3.TotalVariation.ParryFirstReturn

/-! Finite prefixes under arbitrary iid return-duration weights. -/

namespace D5.S3.TotalVariation.ParryReturnPrefix

open MeasureTheory Set Function
open D5.S3.TotalVariation.ParryBilateralLaw
open D5.S3.TotalVariation.ParryFirstReturn
open scoped ENNReal
variable {k : ℕ}

/-- Read complete initial return durations followed by a run of true bits. -/
noncomputable def matchesReturnPrefix (r : RelationPath k) (ns : List (Fin k)) (j : ℕ) : Bool :=
  matchesReturnTimes r ns &&
    decide (∀ i : Fin j, r.val ((returnSpan ns + i.val : ℕ) : ℤ) = true)

private theorem matches_append (r : RelationPath k) (ns ys : List (Fin k)) :
    matchesReturnTimes r (ns ++ ys) = true ↔
      matchesReturnTimes r ns = true ∧
      matchesReturnTimes (returnMap^[ns.length] r) ys = true := by
  induction ns generalizing r with
  | nil => simp [matchesReturnTimes]
  | cons n ns ih =>
    simp only [List.cons_append, matchesReturnTimes, Bool.and_eq_true, decide_eq_true_eq,
      List.length_cons, Function.iterate_succ_apply, ih]
    exact and_assoc.symm

private theorem time_after_prefix (r : RelationPath k) (ns : List (Fin k))
    (h : matchesReturnTimes r ns = true) (t : ℤ) :
    (returnMap^[ns.length] r).val t = r.val (t + (returnSpan ns : ℤ)) := by
  induction ns generalizing r t with
  | nil => simp [returnSpan]
  | cons n ns ih =>
    obtain ⟨hd, ht⟩ : returnTime r = n.val + 1 ∧ matchesReturnTimes (returnMap r) ns = true := by
      simpa [matchesReturnTimes, Bool.and_eq_true] using h
    simp only [List.length_cons, Function.iterate_succ_apply]
    rw [ih (returnMap r) ht, returnMap, hd, shift_iterate]
    exact congrArg r.val (by
      simp only [returnSpan, Nat.cast_add, Nat.cast_one]
      ring)

private theorem tail_true_iff (r : RelationPath k) (j : ℕ) :
    (∀ i : Fin j, r.val (i.val : ℤ) = true) ↔ j < returnTime r := by
  have spec := returnTime_spec r
  constructor
  · intro allTrue
    by_contra! h
    let i : Fin j := ⟨returnTime r - 1, by omega⟩
    have ht := allTrue i
    have hz := spec.2.2.1
    change (relationShift^[returnTime r] r).val (-1) = false at hz
    rw [shift_iterate] at hz
    have same : (i.val : ℤ) = -1 + (returnTime r : ℤ) := by
      dsimp [i]
      omega
    rw [same, hz] at ht
    contradiction
  · intro h i
    apply Bool.eq_true_of_ne_false
    intro hfalse
    have notReturn := spec.2.2.2 (i.val + 1) (by omega) (by have := i.isLt; omega)
    apply notReturn
    change (relationShift^[i.val + 1] r).val (-1) = false
    rw [shift_iterate, show (-1 : ℤ) + ((i.val + 1 : ℕ) : ℤ) = i.val by omega]
    exact hfalse

private theorem matchesReturnTimes_measurable (ns : List (Fin k)) :
    MeasurableSet {r : RelationPath k | matchesReturnTimes r ns = true} := by
  induction ns with
  | nil => simp [matchesReturnTimes]
  | cons n ns ih =>
    let step := n.val + 1
    have fixedShift : Measurable (relationShift^[step] : RelationPath k → RelationPath k) := by
      apply Measurable.subtype_mk
      apply Measurable.of_eval
      intro t
      have same : (fun r : RelationPath k => (relationShift^[step] r).val t) =
          (fun r => r.val (t + (step : ℤ))) :=
        funext fun r => shift_iterate r step t
      change Measurable (fun r : RelationPath k => (relationShift^[step] r).val t)
      rw [same]
      have evaluation : Measurable (fun x : ℤ → Bool => x (t + (step : ℤ))) :=
        measurable_pi_apply _
      exact evaluation.comp measurable_subtype_coe
    have duration := measurable_returnTime (k := k) (measurableSet_singleton step)
    have event := duration.inter (fixedShift ih)
    convert event using 1
    ext r
    change matchesReturnTimes r (n :: ns) = true ↔
      returnTime r = step ∧ matchesReturnTimes (relationShift^[step] r) ns = true
    simp only [matchesReturnTimes, Bool.and_eq_true, decide_eq_true_eq]
    change returnTime r = step ∧ matchesReturnTimes (returnMap r) ns = true ↔ _
    exact and_congr_right fun h => by rw [returnMap, h]

/-- Index the durations strictly greater than j, stored one below their value. -/
def returnTailIndex (j : ℕ) (i : Fin (k - j)) : Fin k :=
  ⟨j + i.val, by have := i.isLt; omega⟩

/-- For arbitrary iid return-duration weights, a finite window ending inside
the next run has the complete-block factor times the remaining duration tail. -/
theorem iid_return_prefix (μ : Measure (RelationPath k)) (weights : Fin k → ℝ≥0∞)
    (hcyl : ∀ ns : List (Fin k),
      μ {r | matchesReturnTimes r ns = true} = (ns.map weights).prod)
    (ns : List (Fin k)) (j : ℕ) :
    μ {r | matchesReturnPrefix r ns j = true} =
      (ns.map weights).prod * ∑ i : Fin (k - j), weights (returnTailIndex j i) := by
  classical
  let C (i : Fin (k - j)) : Set (RelationPath k) :=
    {r | matchesReturnTimes r (ns ++ [returnTailIndex j i]) = true}
  have cyl (r : RelationPath k) (i : Fin (k - j)) :
      r ∈ C i ↔ matchesReturnTimes r ns = true ∧
        returnTime (returnMap^[ns.length] r) = j + i.val + 1 := by
    simp [C, matches_append, matchesReturnTimes, returnTailIndex]
  have windows : {r | matchesReturnPrefix r ns j = true} = ⋃ i : Fin (k - j), C i := by
    ext r
    simp only [matchesReturnPrefix, mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨h, ht⟩
      let r' := returnMap^[ns.length] r
      have allTrue (i : Fin j) : r'.val (i.val : ℤ) = true := by
        change (returnMap^[ns.length] r).val (i.val : ℤ) = true
        rw [time_after_prefix r ns h]
        simpa only [Nat.cast_add, add_comm] using ht i
      have tailBound := (tail_true_iff r' j).mp allTrue
      obtain ⟨positive, bound, _⟩ := returnTime_spec r'
      let i : Fin (k - j) := ⟨returnTime r' - (j + 1), by omega⟩
      refine ⟨i, (cyl r i).2 ⟨h, ?_⟩⟩
      change returnTime r' = j + i.val + 1
      dsimp [i]
      omega
    · rintro ⟨i, hC⟩
      obtain ⟨h, hd⟩ := (cyl r i).mp hC
      refine ⟨h, fun t => ?_⟩
      have bound : j < returnTime (returnMap^[ns.length] r) := by omega
      have bit := (tail_true_iff _ j).mpr bound t
      rw [time_after_prefix r ns h] at bit
      simpa only [Nat.cast_add, add_comm] using bit
  have disj : Pairwise (Disjoint on C) := by
    intro i l hil
    change Disjoint (C i) (C l)
    rw [Set.disjoint_left]
    intro r hr hrl
    apply hil
    apply Fin.ext
    have hi := ((cyl r i).mp hr).2
    have hl := ((cyl r l).mp hrl).2
    omega
  have measurableC (i : Fin (k - j)) : MeasurableSet (C i) :=
    matchesReturnTimes_measurable (ns ++ [returnTailIndex j i])
  rw [windows, measure_iUnion disj measurableC, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change μ {r | matchesReturnTimes r (ns ++ [returnTailIndex j i]) = true} = _
  rw [hcyl, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

#print axioms iid_return_prefix

end D5.S3.TotalVariation.ParryReturnPrefix
