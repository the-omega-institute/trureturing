import Reg.Support.DependentFamily
import Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge OriginalAcquiredTrace
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.Support.KBonacciAcquisition.ExecutionSource
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

namespace SelectorObservation
abbrev signature : Signature where
  Params := Σ Y : Type z, ℕ
  State p := NarrowWindowCost.Selector p.2 p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := NarrowWindowCost.Selector p.2 p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ π => π) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ p _ _ _ => Sum.inr (fun _ : Fin p.2 => false)) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature.{z} actual := by
  intro role
  let p : signature.Params := ⟨PUnit.{z+1}, 1⟩
  let a : signature.State p := fun _ _ => Sum.inl PUnit.unit
  let b : signature.State p := fun _ _ => Sum.inr (fun _ => false)
  refine ⟨p, a, b, ?_⟩
  intro same
  have impossible := congrFun (congrFun same (none : Option (ZMod 2))) []
  change (Sum.inl PUnit.unit : PUnit.{z+1} ⊕ (Fin 1 → Bool)) =
    Sum.inr (fun _ => false) at impossible
  cases impossible

end SelectorObservation

namespace WindowObservation
abbrev signature : Signature where
  Params := Σ k : ℕ, ℕ
  State p := NarrowWindowCost.Archive p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (ZMod (p.1 + 1))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p archive => physicalWindow p.1 p.2 archive.length) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => ∅) (fun e => nomatch e)

theorem empty_support :
    initialSupport 4 3 (by decide) false 0
      ([] ++ [(fun _ : Fin 3 => false, some ((0 : ZMod 2) + 1))]) = ∅ := by
  ext j
  constructor
  · intro member
    have charged := (actual_positive_coordinates 4 3 (by decide) (by decide)
      false 0 0 ([] : NarrowWindowCost.Archive 3)
      (fun _ : Fin 3 => false) (by rfl)).2.1 j member
    have impossible : (0 : ZMod 2) = 1 := by
      simpa [wordIncrement] using charged
    exact zero_ne_one impossible
  · intro impossible
    exact False.elim impossible

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let a : signature.State ⟨4, 3⟩ := []
  let b : signature.State ⟨4, 3⟩ := [(fun _ => false, none)]
  refine ⟨⟨4, 3⟩, a, b, ?_⟩
  intro same
  change physicalWindow 4 3 0 = physicalWindow 4 3 1 at same
  have first : (2 : ZMod 5) ∈ physicalWindow 4 3 0 :=
    ⟨2, by decide, by norm_num [vertex]⟩
  have second : (2 : ZMod 5) ∈ physicalWindow 4 3 1 := by
    rw [← same]
    exact first
  obtain ⟨i, hi, equal⟩ := second
  have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases choices with rfl | rfl | rfl | rfl
  · exact (by decide : (2 : ZMod 5) ≠ vertex 4 3 1 0) equal
  · exact (by decide : (2 : ZMod 5) ≠ vertex 4 3 1 1) equal
  · exact (by decide : (2 : ZMod 5) ≠ vertex 4 3 1 2) equal
  · exact (by decide : (2 : ZMod 5) ≠ vertex 4 3 1 3) equal

end WindowObservation

namespace AcquiredExecutionTrace
open SelectorObservation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y)
    (history : List (AllowedBlock k m localAlphabet))
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
    (free : NarrowWindowCost.output k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) = y₀)
    (matched : ActualArchive k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) archive)
    (π : NarrowWindowCost.Selector m Y) (d c : ℕ),
    let w := history.flatMap (fun action => List.ofFn action.val)
    let initial := OriginalRecord k (by omega) w
    let current := OriginalRecord k (by omega) (w ++ archiveWords archive)
    NarrowWindowCost.execute k (by omega) (R.readout () ⟨Y, m⟩ π) d (w ++ archiveWords archive) y₀ archive =
        some (f initial, c) ↔
      ∃ issued, PaidTrace π y₀ current archive issued (f initial) ∧
        issued.length = c ∧ c ≤ d ∧ ActualArchive k (by omega) w (archive ++ issued) ∧
        (initial, OriginalRecord k (by omega) (w ++ archiveWords (archive ++ issued))) ∈
          AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ issued)

private theorem positive : arena.{z}.Law actual := @_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.acquired_execution_trace

private theorem negative : ¬ arena.{z}.Law rejected := by
  intro law
  obtain ⟨initial, current, member, phase⟩ :=
    Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates.support_member true
  obtain ⟨history, free, matched, initialEq, currentEq⟩ := member
  let acquired := Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates.acquired
  let f : Option (LiveRecord 3) → PUnit.{z+1} := fun _ => PUnit.unit
  let π : NarrowWindowCost.Selector 1 PUnit.{z+1} := fun _ _ => Sum.inl PUnit.unit
  have original := acquired_execution_trace 3 1 (by decide) true f history
    (some 0) acquired free matched π 0 0
  have rhs := original.mp (by rfl)
  have h := law 3 1 (by decide) true f history
    (some 0) acquired free matched π 0 0
  have impossible := h.mpr rhs
  change (none : Option (PUnit.{z+1} × ℕ)) = some (PUnit.unit, 0) at impossible
  cases impossible

def evidence : Registration arena.{z} (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.acquired_execution_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, negative⟩
      intro j different
      exact (different (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

#print axioms evidence
end AcquiredExecutionTrace

namespace ExecutePaidTrace
open SelectorObservation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool)
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) (y : Y) (c : ℕ),
    NarrowWindowCost.execute k (by omega) (R.readout () ⟨Y, m⟩ π) d w y₀ archive = some (y, c) ↔
      ∃ issued, PaidTrace π y₀ (OriginalRecord k (by omega) w) archive issued y ∧
        issued.length = c ∧ c ≤ d

private theorem positive : arena.{z}.Law actual := @_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.execute_paid_trace

private theorem negative : ¬ arena.{z}.Law rejected := by
  intro law
  have h := law (Y := PUnit.{z+1}) 3 1 (by decide)
    (fun _ _ => Sum.inl PUnit.unit) 0 [] none [] PUnit.unit 0
  have impossible := h.mpr ⟨[], rfl, rfl, le_rfl⟩
  change (none : Option (PUnit.{z+1} × ℕ)) = some (PUnit.unit, 0) at impossible
  cases impossible

def evidence : Registration arena.{z} (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.execute_paid_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, negative⟩
      intro j different
      exact (different (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

#print axioms evidence
end ExecutePaidTrace

namespace FullPositiveParent
open WindowObservation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ) (hm : 3 ≤ m) (odd : Odd m) (short : m < k)
    (localAlphabet : Bool) (v previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool) (prior : archiveEndpoint (some v) archive = some previous)
    (full : initialSupport k m (by omega) localAlphabet v
      (archive ++ [(parent, some (previous + 1))]) = R.readout () ⟨k, m⟩ archive),
    (∀ i : Fin m, parent i = decide (i.val % 2 = 0)) ∧
      ∀ initial current : LiveRecord k,
        (some initial, some current) ∈ AcquiredPairs k m (by omega) localAlphabet (some v)
          (archive ++ [(parent, some (previous + 1))]) → current.tail = 1

private theorem positive : arena.Law actual := @_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_parent

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law 4 3 (by decide) (by decide) (by decide) false 0 0
    ([] : NarrowWindowCost.Archive 3) (fun _ : Fin 3 => false) (by rfl) empty_support
  have impossible : (false : Bool) = true := by
    simpa using h.1 (⟨0, by decide⟩ : Fin 3)
  cases impossible

def evidence : Registration arena (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_parent)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, negative⟩
      intro j different
      exact (different (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

#print axioms evidence
end FullPositiveParent

namespace FullPositiveHistoryTrace
open WindowObservation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type z} (k m : ℕ) (hm : 3 ≤ m)
    (odd : Odd m) (critical : k = m + 1) (localAlphabet : Bool)
    (v previous : ZMod 2) (archive : NarrowWindowCost.Archive m) (parent : Fin m → Bool)
    (prior : archiveEndpoint (some v) archive = some previous)
    (full : initialSupport k m (by omega) localAlphabet v
      (archive ++ [(parent, some (previous + 1))]) = R.readout () ⟨k, m⟩ archive)
    (f : Option (LiveRecord k) → Y) (labels : ZMod (k + 1) → Y)
    (wellDefined : ∀ initial current : LiveRecord k,
      (some initial, some current) ∈ AcquiredPairs k m (by omega) localAlphabet (some v)
        (archive ++ [(parent, some (previous + 1))]) → f (some initial) = labels (-initial.phase)),
    let acquired := archive ++ [(parent, some (previous + 1))]
    (∀ i : Fin m, parent i = decide (i.val % 2 = 0)) ∧
    ∀ pair ∈ AcquiredPairs k m (by omega) localAlphabet (some v) acquired,
      ∃ initial current : LiveRecord k,
        pair.1 = some initial ∧ pair.2 = some current ∧
        f pair.1 = labels (-initial.phase) ∧ -initial.phase ∈ physicalWindow k m archive.length ∧
        current.value = previous + 1 ∧ current.tail = 1 ∧
        current.phase = initial.phase + (((archive.length + 1) * m : ℕ) : ZMod (k + 1)) ∧
        ∃ history : List (AllowedBlock k m localAlphabet),
          let w := history.flatMap (fun action => List.ofFn action.val)
          OriginalRecord k (by omega) w = some initial ∧
          OriginalRecord k (by omega) (w ++ archiveWords acquired) = some current ∧
          NarrowWindowCost.output k (by omega) w = some v ∧ ActualArchive k (by omega) w acquired ∧
          ∀ (π : NarrowWindowCost.Selector m Y) (d c : ℕ),
            NarrowWindowCost.execute k (by omega) π d (w ++ archiveWords acquired) (some v) acquired =
                some (f (some initial), c) ↔
              ∃ issued, PaidTrace π (some v) (some current) acquired issued (f (some initial)) ∧
                issued.length = c ∧ c ≤ d ∧ ActualArchive k (by omega) w (acquired ++ issued) ∧
                (some initial, OriginalRecord k (by omega) (w ++ archiveWords (acquired ++ issued))) ∈
                  AcquiredPairs k m (by omega) localAlphabet (some v) (acquired ++ issued)

private theorem positive : arena.{z}.Law actual := @_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_history_trace

private theorem negative : ¬ arena.{z}.Law rejected := by
  intro law
  have h := law (Y := PUnit.{z+1}) 4 3 (by decide) (by decide) (by decide)
    false 0 0 ([] : NarrowWindowCost.Archive 3) (fun _ : Fin 3 => false)
    (by rfl) empty_support (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (by intro initial current member; rfl)
  have impossible : (false : Bool) = true := by
    simpa using h.1 (⟨0, by decide⟩ : Fin 3)
  cases impossible

def evidence : Registration arena.{z} (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_history_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, negative⟩
      intro j different
      exact (different (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

#print axioms evidence
end FullPositiveHistoryTrace

namespace NativeExecutePaidTrace
open SelectorObservation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type z} (k m : ℕ)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ)
    (q : Option (LiveRecord k)) (y₀ : Option (ZMod 2))
    (archive : NarrowWindowCost.Archive m) (y : Y) (c : ℕ),
    NativeExecute (R.readout () ⟨Y, m⟩ π) d q y₀ archive = some (y, c) ↔
      ∃ issued, PaidTrace π y₀ q archive issued y ∧ issued.length = c ∧ c ≤ d

private theorem positive : arena.{z}.Law actual := @_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.native_execute_paid_trace

private theorem negative : ¬ arena.{z}.Law rejected := by
  intro law
  have h := law (Y := PUnit.{z+1}) 3 1
    (fun _ _ => Sum.inl PUnit.unit) 0 none none [] PUnit.unit 0
  have impossible := h.mpr ⟨[], rfl, rfl, le_rfl⟩
  change (none : Option (PUnit.{z+1} × ℕ)) = some (PUnit.unit, 0) at impossible
  cases impossible

def evidence : Registration arena.{z} (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.native_execute_paid_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, negative⟩
      intro j different
      exact (different (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

#print axioms evidence
end NativeExecutePaidTrace

end
end Reg.Support.KBonacciAcquisition.ExecutionSource
