import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths

/- UNCOMPILED SOURCE-SHAPED ATTEMPTS. The readouts below are actual source
operands, and the laws retain the source quantifiers and endpoint clauses.
No CompiledSourceScope/Operands/Contract or Scribe validator has run. Actual
correspondence is OPEN; sourceSelection is none. Packed Parameters are a
mathematical family presentation, not an asserted source binder/selector. -/
noncomputable section
open Set Finset
open scoped unitInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteGreedyFamilyTransport
open _root_.D5.S3.Geometry.FiniteIndependentPathGreedy
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open _root_.D5.S3.Geometry.FiniteElementaryCollapse
open _root_.D5.S3.Geometry.FiniteComponentClosure
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteCoordinateTruncation
open _root_.D5.S3.Geometry.FiniteVertexDominationCollapse (faceSet mem_faceSet)
namespace Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths

namespace intervalList_source
structure Parameters where
  n : Nat
  hn : 0 < n
  lo : Nat
  m : Nat
  bound : lo+m ≤ n

abbrev signature : Signature where
  Params := Parameters
  State p := List (Fin p.n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p z => intervalList p.hn p.lo p.m = z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n),
    R.readout () ⟨n, hn, lo, m, h⟩ (((List.finRange n).drop lo).take m) ∧
    R.readout () ⟨n, hn, lo, m, h⟩ ((List.finRange m).map (intervalEmbedding lo m h))
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.intervalList_source)) ↔ arena.Law actual := Iff.rfl
private def testParameters : Parameters := ⟨1, by omega, 0, 0, by omega⟩
private def presentState : signature.State testParameters := []
private def absentState : signature.State testParameters := [⟨0, by omega⟩]
private theorem present : actual.readout () testParameters presentState := by rfl
private theorem absent : ¬ actual.readout () testParameters absentState := by
  change ([] : List (Fin 1)) ≠ [⟨0, by omega⟩]
  simp
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (n := 1) (by omega) 0 0 (by omega)).1

private theorem source_law : arena.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.intervalList_source)

def family : Registration arena (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.intervalList_source)) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.intervalList_source) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.intervalList_source.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.intervalList_source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end intervalList_source

namespace mem_paths_interval
structure Parameters where
  n : Nat
  hn : 0 < n
  lo : Nat
  m : Nat
  bound : lo+m ≤ n

abbrev signature : Signature where
  Params := Parameters
  State p := Finset (Fin p.n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p z => z ∈ paths (intervalList p.hn p.lo p.m)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n) (a : Finset (Fin n)),
    R.readout () ⟨n, hn, lo, m, h⟩ a ↔
      (∀ i ∈ a, lo ≤ i.val ∧ i.val < lo+m) ∧
      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m → i ∉ a ∨ successor hn i ∉ a)
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_paths_interval)) ↔ arena.Law actual := Iff.rfl
private def testParameters : Parameters := ⟨1, by omega, 0, 0, by omega⟩
private def presentState : signature.State testParameters := ∅
private def absentState : signature.State testParameters := {⟨0, by omega⟩}
private theorem present : actual.readout () testParameters presentState := by
  change (∅ : Finset (Fin 1)) ∈ paths []
  simp [paths]
private theorem absent : ¬ actual.readout () testParameters absentState := by
  change ({⟨0, by omega⟩} : Finset (Fin 1)) ∉ paths []
  simp [paths]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) (by omega) 0 0 (by omega) ∅
  apply hh.mpr
  constructor
  · intro i hi; exact (Finset.not_mem_empty i hi).elim
  · intro i hi hib; omega

private theorem source_law : arena.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_paths_interval)

def family : Registration arena (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_paths_interval)) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_paths_interval) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_paths_interval.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_paths_interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end mem_paths_interval

namespace mem_pathChosen_interval
structure Parameters where
  n : Nat
  hn : 0 < n
  lo : Nat
  m : Nat
  bound : lo+m ≤ n

abbrev signature : Signature where
  Params := Parameters
  State p := Fin p.n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p z => z ∈ pathChosen (intervalList p.hn p.lo p.m)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n) (i : Fin n),
    R.readout () ⟨n, hn, lo, m, h⟩ i ↔
      lo+1 ≤ i.val ∧ i.val < lo+m ∧ (i.val-lo)%3 = 1
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval)) ↔ arena.Law actual := Iff.rfl
private def testParameters : Parameters := ⟨2, by omega, 0, 2, by omega⟩
private def presentState : signature.State testParameters := ⟨1, by omega⟩
private def absentState : signature.State testParameters := ⟨0, by omega⟩
private theorem present : actual.readout () testParameters presentState := by
  change (⟨1, by omega⟩ : Fin 2) ∈ pathChosen [⟨0, by omega⟩, ⟨1, by omega⟩]
  simp [pathChosen]
private theorem absent : ¬ actual.readout () testParameters absentState := by
  change (⟨0, by omega⟩ : Fin 2) ∉ pathChosen [⟨0, by omega⟩, ⟨1, by omega⟩]
  simp [pathChosen]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (n := 2) (by omega) 0 2 (by omega) ⟨1, by omega⟩).mpr (by decide)

private theorem source_law : arena.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval)

def family : Registration arena (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval)) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end mem_pathChosen_interval

universe u

namespace pinnedImage_iff
structure Parameters where
  V : Type u
  dv : DecidableEq V
  n : Nat
  hn : 0 < n
  s : Fin n ↪ V
  lo : Nat
  m : Nat
  bound : lo+m ≤ n
  fixed : Finset (Fin n)
  outside : ∀ i ∈ fixed, i.val < lo ∨ lo+m ≤ i.val
attribute [instance] Parameters.dv

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ p z => z ∈ pinnedImage p.hn p.s p.lo p.m p.fixed) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [dv : DecidableEq V] {n : Nat} (hn : 0 < n)
    (s : Fin n ↪ V) (lo m : Nat) (h : lo+m ≤ n)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) (a : Finset V),
    R.readout () ⟨V, dv, n, hn, s, lo, m, h, S, hS⟩ a ↔ a ⊆ ground s ∧
      (∀ i : Fin n, (i.val < lo ∨ lo+m ≤ i.val) → (s i ∉ a ↔ i ∈ S)) ∧
      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m → s i ∈ a ∨ s (successor hn i) ∈ a)
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff.{u})) ↔ arena.{u}.Law actual := Iff.rfl
private def testEmbedding : Fin 1 ↪ ULift.{u} (Fin 1) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def answer : Finset (ULift.{u} (Fin 1)) := complementMap testEmbedding ∅
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 1), inferInstance, 1, by omega, testEmbedding, 0, 0, by omega,
    ∅, by simp⟩
private def presentState : signature.State testParameters := answer
private def absentState : signature.State testParameters := ∅
private theorem answer_nonempty : answer.{u}.Nonempty := by
  refine ⟨testEmbedding ⟨0, by omega⟩, ?_⟩
  simp [answer, complementMap]
private theorem image_answer : pinnedImage (show 0 < 1 by omega) testEmbedding 0 0 ∅ = {answer.{u}} := by
  change (paths []).image (fun b => complementMap testEmbedding (∅ ∪ b)) = _
  simp [paths, answer]
private theorem present : actual.{u}.readout () testParameters presentState := by
  change answer ∈ pinnedImage (show 0 < 1 by omega) testEmbedding 0 0 ∅
  rw [image_answer]
  exact Finset.mem_singleton_self _
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  change ∅ ∉ pinnedImage (show 0 < 1 by omega) testEmbedding 0 0 ∅
  rw [image_answer, Finset.mem_singleton]
  exact fun he => answer_nonempty.ne_empty he.symm
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (V := ULift.{u} (Fin 1)) (n := 1) (by omega) testEmbedding 0 0
    (by omega) ∅ (by simp) answer
  exact hh.mpr ((_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff (by omega)
    testEmbedding 0 0 (by omega) ∅ (by simp) answer).mp present)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end pinnedImage_iff

namespace survivors_pinnedImage
structure Parameters where
  V : Type u
  dv : DecidableEq V
  n : Nat
  hn : 0 < n
  s : Fin n ↪ V
  lo : Nat
  m : Nat
  bound : lo+m ≤ n
  fixed : Finset (Fin n)
  outside : ∀ i ∈ fixed, i.val < lo ∨ lo+m ≤ i.val
  k : Nat
  before : k ≤ lo
attribute [instance] Parameters.dv

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ p z => z ∈ survivors (pinnedImage p.hn p.s p.lo p.m p.fixed) (((List.finRange p.n).drop p.k).map p.s)) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [dv : DecidableEq V] {n : Nat} (hn : 0 < n)
    (s : Fin n ↪ V) (k lo m : Nat) (hk : k ≤ lo) (h : lo+m ≤ n)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) (a : Finset V),
    R.readout () ⟨V, dv, n, hn, s, lo, m, h, S, hS, k, hk⟩ a ↔
      a ∈ if m%3 = 1 then ∅ else {complementMap s (S ∪ pathChosen (intervalList hn lo m))}
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V dv n hn s k lo m hk hb S hS a
    exact Finset.ext_iff.mp (h hn s k lo m hk hb S hS) a
  · intro h V dv n hn s k lo m hk hb S hS
    apply Finset.ext
    intro a
    exact h hn s k lo m hk hb S hS a
private def testEmbedding : Fin 1 ↪ ULift.{u} (Fin 1) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def answer : Finset (ULift.{u} (Fin 1)) := complementMap testEmbedding ∅
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 1), inferInstance, 1, by omega, testEmbedding, 0, 0, by omega,
    ∅, by simp, 0, by omega⟩
private def presentState : signature.State testParameters := answer
private def absentState : signature.State testParameters := ∅
private theorem answer_nonempty : answer.{u}.Nonempty := by
  refine ⟨testEmbedding ⟨0, by omega⟩, ?_⟩
  simp [answer, complementMap]
private theorem run_answer : survivors (pinnedImage (show 0 < 1 by omega)
    testEmbedding 0 0 ∅) (((List.finRange 1).drop 0).map testEmbedding) = {answer.{u}} := by
  rw [_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage (by omega)
    testEmbedding 0 0 0 (by omega) (by omega) ∅ (by simp)]
  rfl
private theorem present : actual.{u}.readout () testParameters presentState := by
  change answer ∈ survivors (pinnedImage (show 0 < 1 by omega) testEmbedding 0 0 ∅)
    (((List.finRange 1).drop 0).map testEmbedding)
  rw [run_answer]
  exact Finset.mem_singleton_self _
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  change ∅ ∉ survivors (pinnedImage (show 0 < 1 by omega) testEmbedding 0 0 ∅)
    (((List.finRange 1).drop 0).map testEmbedding)
  rw [run_answer, Finset.mem_singleton]
  exact fun he => answer_nonempty.ne_empty he.symm
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (V := ULift.{u} (Fin 1)) (n := 1) (by omega) testEmbedding
    0 0 0 (by omega) (by omega) ∅ (by simp) answer
  apply hh.mpr
  change answer ∈ ({answer} : Finset (Finset (ULift.{u} (Fin 1))))
  exact Finset.mem_singleton_self _

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end survivors_pinnedImage

end Reg.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths
