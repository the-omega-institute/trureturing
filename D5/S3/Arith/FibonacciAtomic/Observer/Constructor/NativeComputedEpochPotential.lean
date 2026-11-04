/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite occurrence cycles are equivalent to an input-derived natural epoch potential. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeComputedEpochPotential

open NativeGuardedFreeExtension
open NativeOriginalReconstructionBridge
open NativeCompletionPrefixLifting
open NativeAffineImageSaturation
open Maths
open Maths.MaxPlusPotential

/-! The position field is retained even though the max-plus criterion only uses
the endpoints and signed exponent difference. Parallel and repeated occurrences
therefore remain separate graph edges. -/
structure Occurrence (m : Nat) where
  head : Fin m
  target : Fin m
  headPower : Nat
  occPower : Nat
  position : List Bool

def occurrencesAt {k m : Nat} (head : Fin m) (headPower : Nat) :
    Expression k m → List (Occurrence m)
  | .ground _ => []
  | .token _ _ => []
  | .var b j => [{ head := head, target := j, headPower := headPower, occPower := b, position := [] }]
  | .pair A B =>
      (occurrencesAt head headPower A).map (fun o => { o with position := false :: o.position }) ++
      (occurrencesAt head headPower B).map (fun o => { o with position := true :: o.position })

def occurrenceList {n k m : Nat} (I : EpochInput n k m) : List (Occurrence m) :=
  (List.finRange m).flatMap fun i =>
    match I.base.equations i with
    | some E => occurrencesAt i (I.headPower i) E
    | none => []

def occurrenceAt {n k m : Nat} (I : EpochInput n k m)
    (e : Fin (occurrenceList I).length) : Occurrence m :=
  (occurrenceList I).get e

def occurrenceGraph {n k m : Nat} (I : EpochInput n k m) :
    EdgeGraph (Fin m) (Fin (occurrenceList I).length) where
  source e := (occurrenceAt I e).target
  target e := (occurrenceAt I e).head

def occurrenceWeight {n k m : Nat} (I : EpochInput n k m)
    (e : Fin (occurrenceList I).length) : Int :=
  (occurrenceAt I e).headPower - (occurrenceAt I e).occPower

def CycleCondition {n k m : Nat} (I : EpochInput n k m) : Prop :=
  ∀ (vertex : Fin m) (cycle : (occurrenceGraph I).Walk vertex vertex),
    walkWeight (occurrenceWeight I) cycle ≤ 0

private theorem occurrencesAt_bound_of_legal {k m : Nat}
    {s : Fin m → Nat} {i : Fin m} {headPower : Nat} {E : Expression k m}
    (headBound : headPower ≤ s i) (legal : ShiftLegal s (s i - headPower) E)
    {o : Occurrence m} (ho : o ∈ occurrencesAt i headPower E) :
    (s o.target : Int) + ((o.headPower : Int) - o.occPower) ≤ s o.head := by
  induction E generalizing o with
  | ground => simp [occurrencesAt] at ho
  | token => simp [occurrencesAt] at ho
  | var b j =>
      have ho' : o = { head := i, target := j, headPower := headPower, occPower := b, position := [] } := by
        simpa [occurrencesAt] using ho
      subst o
      change s j ≤ b + (s i - headPower) at legal
      change (s j : Int) + ((headPower : Int) - b) ≤ s i
      omega
  | pair A B ihA ihB =>
      rcases legal with ⟨legalA, legalB⟩
      simp only [occurrencesAt, List.mem_append, List.mem_map] at ho
      rcases ho with h | h
      · rcases h with ⟨a, ha, rfl⟩
        have hb : (s a.target : Int) + ((a.headPower : Int) - a.occPower) ≤ s a.head :=
          ihA legalA ha
        simpa using hb
      · rcases h with ⟨a, ha, rfl⟩
        have hb : (s a.target : Int) + ((a.headPower : Int) - a.occPower) ≤ s a.head :=
          ihB legalB ha
        simpa using hb

private theorem occurrencesAt_bound {n k m : Nat} (I : EpochInput n k m)
    {i : Fin m} {E : Expression k m} (he : I.base.equations i = some E)
    {s : Fin m → Nat} (valid : Potential I s)
    {o : Occurrence m} (ho : o ∈ occurrencesAt i (I.headPower i) E) :
    (s o.target : Int) + ((o.headPower : Int) - o.occPower) ≤ s o.head := by
  exact occurrencesAt_bound_of_legal (valid i E he).1 (valid i E he).2 ho

private theorem occurrenceList_mem {n k m : Nat} (I : EpochInput n k m)
    {o : Occurrence m} (ho : o ∈ occurrenceList I) :
    ∃ i E, I.base.equations i = some E ∧ o ∈ occurrencesAt i (I.headPower i) E := by
  change o ∈ (List.finRange m).flatMap (fun i =>
    match I.base.equations i with
    | some E => occurrencesAt i (I.headPower i) E
    | none => []) at ho
  rcases List.mem_flatMap.mp ho with ⟨i, hi, h⟩
  cases he : I.base.equations i with
  | none => simp [he] at h
  | some E =>
      simp only [he] at h
      exact ⟨i, E, he, h⟩

private theorem occurrence_index {n k m : Nat} (I : EpochInput n k m)
    {o : Occurrence m} (ho : o ∈ occurrenceList I) :
    ∃ e, occurrenceAt I e = o := by
  exact List.get_of_mem ho

private theorem potential_graph {n k m : Nat} (I : EpochInput n k m)
    {s : Fin m → Nat} (valid : Potential I s) :
    IsPotential (occurrenceGraph I) (occurrenceWeight I)
      (fun i => (s i : Int)) := by
  intro e
  obtain ⟨i, E, he, ho⟩ := occurrenceList_mem I (List.get_mem _ e)
  have hbound := occurrencesAt_bound I he valid ho
  have : (s (occurrenceAt I e).target : Int) + occurrenceWeight I e ≤
      s (occurrenceAt I e).head := by
    simpa [occurrenceAt, occurrenceWeight] using hbound
  exact this

private theorem occurrence_mem_of_equation {n k m : Nat} (I : EpochInput n k m)
    {i : Fin m} {E : Expression k m} (he : I.base.equations i = some E)
    {o : Occurrence m} (ho : o ∈ occurrencesAt i (I.headPower i) E) :
    o ∈ occurrenceList I := by
  unfold occurrenceList
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  simp only [he]
  exact ho

private theorem graph_occurrence_bound {n k m : Nat} (I : EpochInput n k m)
    {s : Fin m → Nat}
    (hgraph : IsPotential (occurrenceGraph I) (occurrenceWeight I)
      (fun i => (s i : Int)))
    {i : Fin m} {E : Expression k m} (he : I.base.equations i = some E)
    {o : Occurrence m} (ho : o ∈ occurrencesAt i (I.headPower i) E) :
    (s o.target : Int) + ((o.headPower : Int) - o.occPower) ≤ s o.head := by
  obtain ⟨e, heq⟩ := occurrence_index I (occurrence_mem_of_equation I he ho)
  have h := hgraph e
  change (s (occurrenceAt I e).target : Int) + occurrenceWeight I e ≤
    s (occurrenceAt I e).head at h
  rw [heq] at h
  simpa [occurrenceWeight, heq] using h

private theorem shiftLegal_of_occurrence_bounds {k m : Nat}
    {s : Fin m → Nat} {i : Fin m} {headPower : Nat} {E : Expression k m}
    (bounds : ∀ {o : Occurrence m}, o ∈ occurrencesAt i headPower E →
      (s o.target : Int) + ((o.headPower : Int) - o.occPower) ≤ s o.head) :
    ShiftLegal s (s i - headPower) E := by
  induction E with
  | ground => trivial
  | token => trivial
  | var b j =>
      have ho : ({ head := i, target := j, headPower := headPower, occPower := b, position := [] } : Occurrence m) ∈
          occurrencesAt (k := k) i headPower (.var b j : Expression k m) := by
        change ({ head := i, target := j, headPower := headPower, occPower := b, position := [] } : Occurrence m) ∈
          [({ head := i, target := j, headPower := headPower, occPower := b, position := [] } : Occurrence m)]
        exact List.mem_singleton_self _
      have h := bounds ho
      change s j ≤ b + (s i - headPower)
      change (s j : Int) + ((headPower : Int) - b) ≤ s i at h
      omega
  | pair A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · apply ihA
        intro o ho
        have hb := bounds (o := { o with position := false :: o.position })
          (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))
        simpa using hb
      · apply ihB
        intro o ho
        have hb := bounds (o := { o with position := true :: o.position })
          (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))
        simpa using hb

private theorem graph_shiftLegal {n k m : Nat} (I : EpochInput n k m)
    {s : Fin m → Nat} (hgraph : IsPotential (occurrenceGraph I) (occurrenceWeight I)
      (fun i => (s i : Int))) (i : Fin m) (E : Expression k m)
    (he : I.base.equations i = some E) :
    ShiftLegal s (s i - I.headPower i) E := by
  apply shiftLegal_of_occurrence_bounds
  intro o ho
  exact graph_occurrence_bound I hgraph he ho

/-! The zero-round value is exactly the source lower bound: head power at
an equation head and zero at an undefined state. Each further round takes
the maximum over one more incoming occurrence edge in the reversed graph. -/
private def lowerBound {n k m : Nat} (I : EpochInput n k m) (i : Fin m) : Int :=
  match I.base.equations i with
  | some _ => I.headPower i
  | none => 0

private def relaxation {n k m : Nat} (I : EpochInput n k m) : Nat → Fin m → Int
  | 0, i => lowerBound I i
  | t + 1, i =>
      ((List.finRange (occurrenceList I).length).map fun e =>
        if (occurrenceGraph I).target e = i then
          relaxation I t ((occurrenceGraph I).source e) + occurrenceWeight I e
        else lowerBound I i).foldr max (lowerBound I i)

/-- A terminating integer tuple computed solely from the input equations and
head powers, using exactly `m` finite max-plus relaxation rounds. -/
def computedSignedPotential {n k m : Nat} (I : EpochInput n k m) : Fin m → Int :=
  relaxation I m

/-- The natural tuple used for native functionalization. No potential witness,
parameter assignment, prefix depth or real-number oracle is an input. -/
def computedPotential {n k m : Nat} (I : EpochInput n k m) (i : Fin m) : Nat :=
  (computedSignedPotential I i).toNat

theorem base_le_fold_max (l : List Int) (b : Int) : b ≤ l.foldr max b := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

theorem fold_max_property {P : Int → Prop} (l : List Int) (b : Int)
    (hb : P b) (hl : ∀ a ∈ l, P a) : P (l.foldr max b) := by
  induction l with
  | nil => exact hb
  | cons a l ih =>
      simp only [List.foldr_cons]
      rcases le_total a (l.foldr max b) with h | h
      · rw [max_eq_right h]
        exact ih (fun x hx => hl x (List.mem_cons_of_mem a hx))
      · rw [max_eq_left h]
        exact hl a (List.mem_cons_self)

private theorem lower_le_relaxation {n k m : Nat} (I : EpochInput n k m)
    (t : Nat) (i : Fin m) : lowerBound I i ≤ relaxation I t i := by
  cases t with
  | zero => exact le_rfl
  | succ t => exact base_le_fold_max _ _

private theorem relaxation_edge {n k m : Nat} (I : EpochInput n k m)
    (t : Nat) (e : Fin (occurrenceList I).length) :
    relaxation I t ((occurrenceGraph I).source e) + occurrenceWeight I e ≤
      relaxation I (t + 1) ((occurrenceGraph I).target e) := by
  apply List.le_max_of_le' (lowerBound I ((occurrenceGraph I).target e))
  · exact List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩
  · simp only [ite_true]
    exact le_rfl

private theorem walk_le_relaxation {n k m : Nat} (I : EpochInput n k m)
    (t : Nat) {start finish : Fin m} (walk : (occurrenceGraph I).Walk start finish)
    (hlen : walk.length ≤ t) :
    walkWeight (occurrenceWeight I) walk + lowerBound I start ≤ relaxation I t finish := by
  induction t generalizing start finish with
  | zero =>
      cases walk with
      | nil => simp [walkWeight, EdgeGraph.Walk.edges, relaxation]
      | concat walk edge legal => simp at hlen
  | succ t ih =>
      cases walk with
      | nil => simpa [walkWeight, EdgeGraph.Walk.edges] using lower_le_relaxation I (t + 1) start
      | @concat finish walk edge legal =>
          have hprev := ih walk (by simpa using Nat.le_of_succ_le_succ hlen)
          have hedge := relaxation_edge I t edge
          rw [legal] at hedge
          rw [walkWeight_concat]
          omega

private theorem relaxation_attained {n k m : Nat} (I : EpochInput n k m)
    (t : Nat) (i : Fin m) :
    ∃ (start : Fin m) (walk : (occurrenceGraph I).Walk start i),
      walk.length ≤ t ∧ relaxation I t i = walkWeight (occurrenceWeight I) walk + lowerBound I start := by
  induction t generalizing i with
  | zero => exact ⟨i, .nil, le_rfl, by simp [relaxation, walkWeight, EdgeGraph.Walk.edges]⟩
  | succ t ih =>
      apply fold_max_property
        (P := fun z => ∃ (start : Fin m) (walk : (occurrenceGraph I).Walk start i),
          walk.length ≤ t + 1 ∧ z = walkWeight (occurrenceWeight I) walk + lowerBound I start)
      · exact ⟨i, .nil, Nat.zero_le _, by simp [walkWeight, EdgeGraph.Walk.edges]⟩
      · intro z hz
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp hz
        by_cases he : (occurrenceGraph I).target e = i
        · simp only [ite_eq_left he]
          obtain ⟨start, walk, hlen, hvalue⟩ := ih ((occurrenceGraph I).source e)
          refine ⟨start, (walk.concat e rfl).castFinish he, ?_, ?_⟩
          · simpa using Nat.add_le_add_right hlen 1
          · rw [walkWeight_castFinish, walkWeight_concat, hvalue]
            omega
        · simp only [ite_eq_right he]
          exact ⟨i, .nil, Nat.zero_le _, by simp [walkWeight, EdgeGraph.Walk.edges]⟩

private theorem computed_graph {n k m : Nat} (I : EpochInput n k m)
    (hcycle : CycleCondition I) :
    IsPotential (occurrenceGraph I) (occurrenceWeight I) (computedSignedPotential I) := by
  intro e
  obtain ⟨start, walk, _, hvalue⟩ := relaxation_attained I m ((occurrenceGraph I).source e)
  obtain ⟨pruned, hnodup, hweight⟩ :=
    exists_nodup_visited_walkWeight_le hcycle (walk.concat e rfl).length (walk.concat e rfl) le_rfl
  have hcard : pruned.length + 1 ≤ m := by
    simpa only [EdgeGraph.Walk.length_visited, Fintype.card_fin] using hnodup.length_le_card
  have hbound := walk_le_relaxation I m pruned (by omega)
  rw [walkWeight_concat] at hweight
  change relaxation I m ((occurrenceGraph I).source e) + occurrenceWeight I e ≤
    relaxation I m ((occurrenceGraph I).target e)
  omega

private theorem computed_nonneg {n k m : Nat} (I : EpochInput n k m)
    (i : Fin m) : 0 ≤ computedSignedPotential I i := by
  have h := lower_le_relaxation I m i
  have hl : 0 ≤ lowerBound I i := by
    unfold lowerBound
    cases I.base.equations i <;> simp
  exact hl.trans h

private theorem computed_valid {n k m : Nat} (I : EpochInput n k m)
    (hcycle : CycleCondition I) : Potential I (computedPotential I) := by
  have hcast (i : Fin m) : (computedPotential I i : Int) = computedSignedPotential I i :=
    Int.toNat_of_nonneg (computed_nonneg I i)
  have hgraph := computed_graph I hcycle
  intro i E he
  have hhead := lower_le_relaxation I m i
  have hhead' : I.headPower i ≤ computedPotential I i := by
    change lowerBound I i ≤ computedSignedPotential I i at hhead
    rw [← hcast i] at hhead
    simpa [lowerBound, he] using hhead
  refine ⟨hhead', graph_shiftLegal I ?_ i E he⟩
  intro e
  simpa only [hcast] using hgraph e

/-- The executable tuple together with its correctness proof. The cycle proof
is erased at runtime; the tuple itself is `computedPotential I`. -/
def constructPotential {n k m : Nat} (I : EpochInput n k m) (hcycle : CycleCondition I) :
    {s : Fin m → Nat // Potential I s} :=
  ⟨computedPotential I, computed_valid I hcycle⟩

theorem cycleCondition_iff_potential {n k m : Nat} (I : EpochInput n k m) :
    CycleCondition I ↔ ∃ s : Fin m → Nat, Potential I s := by
  constructor
  · intro hcycle
    exact ⟨(constructPotential I hcycle).val, (constructPotential I hcycle).property⟩
  · rintro ⟨s, hs⟩
    have hpot := potential_graph I hs
    intro vertex cycle
    have h := hpot.walkWeight_add_le cycle
    omega

/-! This is the source-facing consumer: the finite computed tuple is the
potential used by the exact equation/filter/reconstruction correspondence. -/
theorem cycleCondition_gives_epoch_transport {n k m : Nat} (I : EpochInput n k m)
    (hcycle : CycleCondition I) :
    ∃ s : Fin m → Nat, Potential I s ∧
      ∀ (p : Fin n → Nat) (w : Fin m → CompletionTree),
        (Legal (functionalInput I s) p ∧ SourceSatisfies (functionalInput I s) p w ∧
          SourcePasses (functionalInput I s) p w) ↔
        ∃! v, OriginalAdmissible I p v ∧ imageValues s v = w := by
  let result := constructPotential I hcycle
  refine ⟨result.val, result.property, ?_⟩
  intro p w
  exact epoch_solution_correspondence I result.val result.property p w

end D5.S3.Arith.FibonacciAtomic.Observer.NativeComputedEpochPotential
