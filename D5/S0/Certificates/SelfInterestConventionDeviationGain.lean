/- GID: D5/S0/Certificates/SelfInterestConventionDeviationGain
   generality: I
   mirror-B: D5/B/S0/Certificates/SelfInterestConventionDeviationGain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/SelfInterestConventionDeviationGain.noPositiveDiscrepancyToAvA; result=D5/S0/Certificates/SelfInterestConventionDeviationGain.both_deviations_refute_no_positive_discrepancy; claim=D5/S0/Certificates/SelfInterestConventionDeviationGain.noPositiveDiscrepancyToAvA
   digest: Each player can gain by changing friendly to antagonistic tie-breaking. -/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Profitable deviations towards antagonistic tie-breaking

Bhagat, Kulkarni, Larsson, and Murali, "Tie-breaking in self interest cumulative
subtraction games", arXiv:2510.24280v2 (20 January 2026), Section 6, asks:
"Problem 6. Is it true that no player can have a positive discrepancy by going from AvF or FvA
to AvA?"
The answer is no. The authors' own experimental results pointed the other way:
"Experimental results point towards that this cannot happen if deviating towards AvA."

For subtraction set {7, 12, 13, 38, 50}, at heap 122 the AvF and AvA outcomes
are (64, 57) and (64, 58): Bob, the second player, gains by changing his own
convention from friendly to antagonistic. At heap 172 the FvA and AvA outcomes
are (107, 64) and (108, 64): Alice, the first player, gains by the same change.
The main theorem includes both strict inequalities.
Problem 6's claim is stated as a proposition and refuted by a closed theorem of its negation.

Only Definition 2's mover-relative semantics is used: swap conventions at every
move, maximize the mover's total, and break indifference by minimizing the
opponent's total for an antagonistic mover or maximizing it for a friendly mover.
Positive legal subtractions are enumerated by a finite list; order and repeated
entries do not affect the optimality specification. Structural tabulation stores
all four outcomes at each heap, and its recurrence is proved below.

Nothing about Conjecture 4 (the FvF-to-AvA statement) is established here.
There is no classification and no claim of only or smallest witnesses.
-/

namespace D5.S0.Certificates.SelfInterestConventionDeviationGain

/-- Each Boolean says whether its player is antagonistic; the mover comes first. -/
abbrev Convention := Bool × Bool

def FvF : Convention := (false, false)
def AvF : Convention := (true, false)
def FvA : Convention := (false, true)
def AvA : Convention := (true, true)

/-- Role reversal at every move. -/
def dual (convention : Convention) : Convention := (convention.2, convention.1)

theorem dual_involutive (convention : Convention) : dual (dual convention) = convention := rfl

theorem dual_fixed_iff (convention : Convention) :
    dual convention = convention ↔ convention = FvF ∨ convention = AvA := by
  rcases convention with ⟨first, second⟩
  cases first <;> cases second <;> decide

/-- Own total is primary; the mover chooses the direction of the opponent tie-break. -/
def Preferred (convention : Convention) (chosen alternative : Nat × Nat) : Prop :=
  alternative.1 ≤ chosen.1 ∧ (alternative.1 = chosen.1 →
    if convention.1 then chosen.2 ≤ alternative.2 else alternative.2 ≤ chosen.2)

private def choose (convention : Convention) (left right : Nat × Nat) : Nat × Nat :=
  if left.1 > right.1 then left
  else if left.1 < right.1 then right
  else if convention.1 then
    if left.2 ≤ right.2 then left else right
  else if right.2 ≤ left.2 then left else right

private theorem choose_spec (convention : Convention) (left right : Nat × Nat) :
    (choose convention left right = left ∨ choose convention left right = right) ∧
      Preferred convention (choose convention left right) left ∧
      Preferred convention (choose convention left right) right := by
  rcases convention with ⟨first, second⟩
  cases first <;> simp only [choose, Preferred, Bool.false_eq_true, if_false, if_true]
    <;> split_ifs <;> simp_all <;> omega

private theorem preferred_trans (convention : Convention) (first second third : Nat × Nat)
    (left : Preferred convention first second) (right : Preferred convention second third) :
    Preferred convention first third := by
  rcases convention with ⟨mover, opponent⟩
  cases mover <;> simp_all [Preferred] <;> omega

private def best (convention : Convention) : List (Nat × Nat) → Nat × Nat
  | [] => (0, 0)
  | first :: rest => if rest.isEmpty then first else choose convention first (best convention rest)

private theorem best_spec (convention : Convention) (candidates : List (Nat × Nat))
    (nonempty : candidates ≠ []) :
    best convention candidates ∈ candidates ∧
      ∀ alternative ∈ candidates,
        Preferred convention (best convention candidates) alternative := by
  induction candidates with
  | nil => contradiction
  | cons first rest inductionHypothesis =>
    by_cases empty : rest = []
    · subst rest
      simp [best, Preferred]
    · obtain ⟨member, optimal⟩ := inductionHypothesis empty
      obtain ⟨selected, firstBound, restBound⟩ :=
        choose_spec convention first (best convention rest)
      simp only [best, List.isEmpty_eq_false_iff.mpr empty, Bool.false_eq_true, if_false]
      constructor
      · rcases selected with selected | selected
        · simp [selected]
        · simp [selected, member]
      · intro alternative membership
        rcases List.mem_cons.mp membership with equal | membership
        · subst alternative
          exact firstBound
        · exact preferred_trans _ _ _ _ restBound (optimal _ membership)

private abbrev Row := ((Nat × Nat) × (Nat × Nat)) × ((Nat × Nat) × (Nat × Nat))

private def zeroRow : Row := (((0, 0), (0, 0)), ((0, 0), (0, 0)))

private def lookup : List Row → Nat → Row
  | [], _ => zeroRow
  | row :: _, 0 => row
  | _ :: rest, heap + 1 => lookup rest heap

private theorem lookup_eq (table : List Row) (heap : Nat) :
    lookup table heap = (table[heap]?).getD zeroRow := by
  induction table generalizing heap with
  | nil => simp [lookup]
  | cons row rest inductionHypothesis => cases heap <;> simp [lookup, inductionHypothesis]

private def readRow (row : Row) (convention : Convention) : Nat × Nat :=
  if convention.1 then (if convention.2 then row.2.2 else row.2.1)
  else (if convention.2 then row.1.2 else row.1.1)

private def readTable (table : List Row) (heap : Nat) (convention : Convention) : Nat × Nat :=
  readRow (lookup table heap) convention

private def legal (subtractions : List Nat) (heap : Nat) : List Nat :=
  subtractions.filter fun step => decide (0 < step ∧ step ≤ heap)

private def candidates (subtractions : List Nat) (heap : Nat) (convention : Convention)
    (previous : Nat → Convention → Nat × Nat) : List (Nat × Nat) :=
  (legal subtractions heap).map fun step =>
    let continuation := previous (heap - step) (dual convention)
    (continuation.2 + step, continuation.1)

private def nextRow (subtractions : List Nat) (heap : Nat) (table : List Row) : Row :=
  let entry := fun convention =>
    best convention (candidates subtractions heap convention (readTable table))
  ((entry FvF, entry FvA), (entry AvF, entry AvA))

private def tabulate (subtractions : List Nat) : Nat → List Row
  | 0 => []
  | heap + 1 => let previous := tabulate subtractions heap
    previous ++ [nextRow subtractions heap previous]

/-- The tabulated mover and opponent totals, with zero payoff when no move is legal. -/
def outcome (subtractions : List Nat) (convention : Convention) (heap : Nat) : Nat × Nat :=
  readTable (tabulate subtractions (heap + 1)) heap convention

private theorem tabulate_length (subtractions : List Nat) (heap : Nat) :
    (tabulate subtractions heap).length = heap := by
  induction heap with
  | zero => rfl
  | succ heap inductionHypothesis => simp [tabulate, inductionHypothesis]

private theorem tabulate_stable (subtractions : List Nat) (bound heap : Nat)
    (below : heap < bound) (convention : Convention) :
    readTable (tabulate subtractions bound) heap convention =
      outcome subtractions convention heap := by
  induction bound with
  | zero => omega
  | succ bound inductionHypothesis =>
    by_cases equal : heap = bound
    · subst heap
      rfl
    · have smaller : heap < bound := by omega
      rw [← inductionHypothesis smaller]
      simp only [tabulate, readTable, lookup_eq]
      rw [List.getElem?_append_left (by simpa [tabulate_length] using smaller)]

private theorem outcome_best (subtractions : List Nat) (convention : Convention) (heap : Nat) :
    outcome subtractions convention heap =
      best convention (candidates subtractions heap convention
        (fun smaller mode => outcome subtractions mode smaller)) := by
  have last : (tabulate subtractions (heap + 1))[heap]? =
      some (nextRow subtractions heap (tabulate subtractions heap)) := by
    simp [tabulate, tabulate_length]
  conv_lhs =>
    unfold outcome readTable
    rw [lookup_eq, last]
  change readRow (nextRow subtractions heap (tabulate subtractions heap)) convention = _
  have entries : candidates subtractions heap convention (readTable (tabulate subtractions heap)) =
      candidates subtractions heap convention
        (fun smaller mode => outcome subtractions mode smaller) := by
    apply List.map_congr_left
    intro step membership
    have bounds : 0 < step ∧ step ≤ heap := by
      simpa [legal] using (List.mem_filter.mp membership).2
    rw [tabulate_stable subtractions heap (heap - step) (by omega)]
  have row : readRow (nextRow subtractions heap (tabulate subtractions heap)) convention =
      best convention (candidates subtractions heap convention
        (readTable (tabulate subtractions heap))) := by
    rcases convention with ⟨first, second⟩
    cases first <;> cases second <;> rfl
  exact row.trans (congrArg (best convention) entries)

/-- Definition 2: terminal zero, or a legal maximizing move with the mover's tie-break. -/
theorem outcome_recurrence (subtractions : List Nat) (convention : Convention) (heap : Nat) :
    ((¬ ∃ step ∈ subtractions, 0 < step ∧ step ≤ heap) →
      outcome subtractions convention heap = (0, 0)) ∧
    ((∃ step ∈ subtractions, 0 < step ∧ step ≤ heap) →
      ∃ step ∈ subtractions, 0 < step ∧ step ≤ heap ∧
        outcome subtractions convention heap =
          ((outcome subtractions (dual convention) (heap - step)).2 + step,
            (outcome subtractions (dual convention) (heap - step)).1) ∧
        ∀ alternative ∈ subtractions, 0 < alternative → alternative ≤ heap →
          Preferred convention (outcome subtractions convention heap)
            ((outcome subtractions (dual convention) (heap - alternative)).2 + alternative,
              (outcome subtractions (dual convention) (heap - alternative)).1)) := by
  rw [outcome_best]
  constructor
  · intro terminal
    have empty : legal subtractions heap = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro step membership
      simp only [legal, List.mem_filter, decide_eq_true_eq] at membership
      exact terminal ⟨step, membership.1, membership.2⟩
    simp [candidates, empty, best]
  · intro available
    have nonempty : candidates subtractions heap convention
        (fun smaller mode => outcome subtractions mode smaller) ≠ [] := by
      obtain ⟨step, member, bounds⟩ := available
      simp only [candidates, ne_eq, List.map_eq_nil_iff]
      intro empty
      have : step ∈ legal subtractions heap := by simp [legal, member, bounds]
      simp [empty] at this
    obtain ⟨member, optimal⟩ := best_spec convention _ nonempty
    obtain ⟨step, legalStep, selected⟩ := List.mem_map.mp member
    have bounds := List.mem_filter.mp legalStep
    simp only [decide_eq_true_eq] at bounds
    refine ⟨step, bounds.1, bounds.2.1, bounds.2.2, selected.symm, ?_⟩
    intro alternative membership positive small
    apply optimal
    apply List.mem_map.mpr
    exact ⟨alternative, by simp [legal, membership, positive, small], rfl⟩

/-- The finite subtraction set used by both witnesses. -/
def witnessSubtractions : List Nat := [7, 12, 13, 38, 50]

set_option maxRecDepth 100000 in
/-- Extra reduction resources are confined to the four kernel-checked table lookups. -/
theorem witness_values :
    outcome witnessSubtractions AvF 122 = (64, 57) ∧
    outcome witnessSubtractions AvA 122 = (64, 58) ∧
    outcome witnessSubtractions FvA 172 = (107, 64) ∧
    outcome witnessSubtractions AvA 172 = (108, 64) := by
  decide +kernel

/-- Bob gains from AvF to AvA, and Alice gains from FvA to AvA. -/
theorem both_deviations_profitable :
    (outcome witnessSubtractions AvF 122).2 < (outcome witnessSubtractions AvA 122).2 ∧
    (outcome witnessSubtractions FvA 172).1 < (outcome witnessSubtractions AvA 172).1 := by
  rcases witness_values with ⟨bobBefore, bobAfter, aliceBefore, aliceAfter⟩
  rw [bobBefore, bobAfter, aliceBefore, aliceAfter]
  decide

def noPositiveDiscrepancyToAvA : Prop :=
  ∀ (subtractions : List Nat) (heap : Nat),
    (outcome subtractions AvA heap).2 ≤ (outcome subtractions AvF heap).2 ∧
    (outcome subtractions AvA heap).1 ≤ (outcome subtractions FvA heap).1

theorem both_deviations_refute_no_positive_discrepancy : ¬ noPositiveDiscrepancyToAvA := by
  intro noPositiveDiscrepancy
  rcases both_deviations_profitable with ⟨bobGain, aliceGain⟩
  have bobBound := (noPositiveDiscrepancy witnessSubtractions 122).1
  have aliceBound := (noPositiveDiscrepancy witnessSubtractions 172).2
  exact (Nat.not_le_of_gt (Nat.add_lt_add bobGain aliceGain))
    (Nat.add_le_add bobBound aliceBound)

#print axioms Convention
#print axioms FvF
#print axioms AvF
#print axioms FvA
#print axioms AvA
#print axioms dual
#print axioms dual_involutive
#print axioms dual_fixed_iff
#print axioms Preferred
#print axioms outcome
#print axioms outcome_recurrence
#print axioms witnessSubtractions
#print axioms witness_values
#print axioms both_deviations_profitable
#print axioms noPositiveDiscrepancyToAvA
#print axioms both_deviations_refute_no_positive_discrepancy

end D5.S0.Certificates.SelfInterestConventionDeviationGain
