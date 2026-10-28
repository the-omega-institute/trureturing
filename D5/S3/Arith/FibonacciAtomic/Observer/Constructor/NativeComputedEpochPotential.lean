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

private theorem graph_potential_occurrence {n k m : Nat} (I : EpochInput n k m)
    {s : Fin m → Nat}
    (headBound : ∀ i, I.headPower i ≤ s i)
    (hgraph : IsPotential (occurrenceGraph I) (occurrenceWeight I)
      (fun i => (s i : Int))) : Potential I s := by
  intro i E he
  refine ⟨headBound i, ?_⟩
  exact graph_shiftLegal I hgraph i E he

private theorem floor_graph {n k m : Nat} (I : EpochInput n k m)
    {φ : Fin m → ℝ}
    (hφ : IsPotential (occurrenceGraph I)
      (fun e => (occurrenceWeight I e : ℝ)) φ) :
    IsPotential (occurrenceGraph I) (occurrenceWeight I)
      (fun i => (⌊φ i⌋ : Int)) := by
  intro e
  have h := hφ e
  have hf := Int.floor_mono h
  simpa only [Int.floor_add_intCast, Int.cast_zero, add_zero] using hf

noncomputable def floorDeficit {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ)
    (i : Fin m) : Int := (I.headPower i : Int) - ⌊φ i⌋

noncomputable def floorOffset {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ) : Int :=
  ((List.finRange _).map (floorDeficit I φ)).foldr max 0

noncomputable def computedSignedPotential {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ)
    (i : Fin m) : Int := ⌊φ i⌋ + floorOffset I φ

noncomputable def computedPotential {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ)
    (i : Fin m) : Nat := (computedSignedPotential I φ i).toNat

private theorem floorOffset_bound {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ)
    (i : Fin m) : floorDeficit I φ i ≤ floorOffset I φ := by
  have mem : floorDeficit I φ i ∈ (List.finRange m).map (floorDeficit I φ) :=
    List.mem_map.mpr ⟨i, by simp, rfl⟩
  exact List.le_max_of_le' 0 mem le_rfl

private theorem computed_nonneg {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ)
    (i : Fin m) : 0 ≤ computedSignedPotential I φ i := by
  have h := floorOffset_bound I φ i
  unfold computedSignedPotential floorDeficit at *
  omega

private theorem computed_head {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ)
    (i : Fin m) : I.headPower i ≤ computedPotential I φ i := by
  have hdef := floorOffset_bound I φ i
  have hn := computed_nonneg I φ i
  have hcast : (computedPotential I φ i : Int) = computedSignedPotential I φ i := by
    simpa [computedPotential] using Int.toNat_of_nonneg hn
  unfold floorDeficit at hdef
  have hInt : (I.headPower i : Int) ≤ computedSignedPotential I φ i := by
    unfold computedSignedPotential
    omega
  have hInt' : (I.headPower i : Int) ≤ (computedPotential I φ i : Int) := by
    simpa [hcast] using hInt
  exact_mod_cast hInt'

private theorem computed_graph {n k m : Nat} (I : EpochInput n k m) (φ : Fin m → ℝ)
    (hφ : IsPotential (occurrenceGraph I)
      (fun e => (occurrenceWeight I e : ℝ)) φ) :
    IsPotential (occurrenceGraph I) (occurrenceWeight I)
      (fun i => ((computedPotential I φ i : Nat) : Int)) := by
  have hraw := floor_graph I hφ
  intro e
  have hbase := hraw e
  have hs : ∀ i, (⌊φ i⌋ : Int) + floorOffset I φ = computedSignedPotential I φ i :=
    fun i => rfl
  have hn : ∀ i, 0 ≤ computedSignedPotential I φ i := computed_nonneg I φ
  have hcast : ∀ i, ((computedPotential I φ i : Nat) : Int) = computedSignedPotential I φ i := by
    intro i
    simpa [computedPotential] using Int.toNat_of_nonneg (hn i)
  change ((computedPotential I φ ((occurrenceGraph I).source e) : Int) + occurrenceWeight I e ≤
    (computedPotential I φ ((occurrenceGraph I).target e) : Int))
  rw [hcast, hcast]
  have := add_le_add_right hbase (floorOffset I φ)
  simpa [computedSignedPotential, add_assoc, add_left_comm, add_comm] using this

private theorem walkWeight_cast {n k m : Nat} (I : EpochInput n k m)
    {start finish : Fin m} (walk : (occurrenceGraph I).Walk start finish) :
    walkWeight (fun e => (occurrenceWeight I e : ℝ)) walk =
      ((walkWeight (𝕜 := Int) (occurrenceWeight I) walk : Int) : ℝ) := by
  induction walk with
  | nil => simp [walkWeight]
  | concat walk edge legal ih =>
      simp only [walkWeight_concat, ih, Int.cast_add]

theorem cycleCondition_iff_potential {n k m : Nat} (I : EpochInput n k m) :
    CycleCondition I ↔ ∃ s : Fin m → Nat, Potential I s := by
  constructor
  · intro hcycle
    have hreal := (Maths.AdditiveTransport.worstDirectedResidualAtMost_iff_closedWalk_le
      (occurrenceGraph I) (fun e => (occurrenceWeight I e : ℝ)) 0).mpr (by
        intro vertex cycle
        have hc : walkWeight (fun e => (occurrenceWeight I e : ℝ)) cycle ≤ 0 := by
          rw [walkWeight_cast I cycle]
          exact_mod_cast hcycle vertex cycle
        simpa using hc)
    rcases hreal with ⟨φ, hφ⟩
    have hφ' : IsPotential (occurrenceGraph I)
        (fun e => (occurrenceWeight I e : ℝ)) φ := by
      intro e
      have h := hφ e
      simp only [MaxPlusPotential.defect] at h
      linarith
    refine ⟨computedPotential I φ, ?_⟩
    exact graph_potential_occurrence I (fun i => computed_head I φ i) (computed_graph I φ hφ')
  · rintro ⟨s, hs⟩
    have hpot := potential_graph I hs
    intro vertex cycle
    have h := hpot.walkWeight_add_le cycle
    omega

/-! This is the source-facing consumer: the cycle criterion supplies the
potential used by the already proved exact equation/filter/reconstruction
correspondence. -/
theorem cycleCondition_gives_epoch_transport {n k m : Nat} (I : EpochInput n k m)
    (hcycle : CycleCondition I) :
    ∃ s : Fin m → Nat, Potential I s ∧
      ∀ (p : Fin n → Nat) (w : Fin m → CompletionTree),
        (Legal (functionalInput I s) p ∧ SourceSatisfies (functionalInput I s) p w ∧
          SourcePasses (functionalInput I s) p w) ↔
        ∃! v, OriginalAdmissible I p v ∧ imageValues s v = w := by
  obtain ⟨s, hs⟩ := cycleCondition_iff_potential I |>.mp hcycle
  refine ⟨s, hs, ?_⟩
  intro p w
  exact epoch_solution_correspondence I s hs p w

end D5.S3.Arith.FibonacciAtomic.Observer.NativeComputedEpochPotential
