import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly

/-- A separate one-core, zero-branch realization checks the whole-family intervention. -/
private def one : Decomposition where
  n := 1
  k := 1
  m := 0
  size := fun i => Fin.elim0 i
  graph := ⊥
  adjDec := inferInstance
  labels := {
    toFun := fun a => match a with
      | .inl c => c
      | .inr v => Fin.elim0 v.1
    invFun := Sum.inl
    left_inv := by intro a; cases a with
      | inl c => rfl
      | inr v => exact Fin.elim0 v.1
    right_inv := by intro c; rfl }
  root := fun i => Fin.elim0 i
  leaf := fun i => Fin.elim0 i
  incidence := fun i => Fin.elim0 i
  leaf_neighbors := by intro i; exact Fin.elim0 i
  root_leaf_edge := by intro i; exact Fin.elim0 i
  nonroot_neighbors := by intro i; exact Fin.elim0 i
  core_neighbors := by intro c v; simp

abbrev RSig : Signature where
  Params := Decomposition
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def rActual : Realization RSig :=
  realize RSig (fun _ d x => evaluation d.graph x) (fun e => nomatch e)
def rBad : Realization RSig :=
  realize RSig (fun _ _ _ => 0) (fun e => nomatch e)
def rArena : Arena where
  signature := RSig
  Law r := ∀ (d : Decomposition) (x : ℤ), r.readout () d x = stateEvaluation d x

theorem rBridge : (∀ (d : Decomposition) (x : ℤ),
    evaluation d.graph x = stateEvaluation d x) ↔ rArena.Law rActual := Iff.rfl

theorem rBadLaw : ¬ rArena.Law rBad := by
  intro h
  have he := h one 1
  have hv : stateEvaluation one 1 = 1 := by decide
  change 0 = stateEvaluation one 1 at he
  rw [hv] at he
  norm_num at he

theorem rDependence : ObservationalDependence RSig rActual := by
  intro i
  refine ⟨one, 0, 1, ?_⟩
  change evaluation one.graph 0 ≠ evaluation one.graph 1
  rw [reassembly, reassembly]
  decide

def rRegistration : Registration rArena
    (∀ (d : Decomposition) (x : ℤ), evaluation d.graph x = stateEvaluation d x) where
  actual := rActual
  bridge := rBridge
  variation := ⟨reassembly, rBad, rBadLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rBad, ?_, rfl, rBadLaw⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := rDependence

abbrev ZSig : Signature where
  Params := Decomposition
  State d := ℤ × (Fin d.m → Bool → ℤ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def zActual : Realization ZSig :=
  realize ZSig (fun _ d s => evaluation d.graph s.1) (fun e => nomatch e)
def zBad : Realization ZSig :=
  realize ZSig (fun _ _ _ => 1) (fun e => nomatch e)
def zArena : Arena where
  signature := ZSig
  Law r := ∀ (d : Decomposition) (x : ℤ) (table : Fin d.m → Bool → ℤ),
    (∀ i b, message d x i b = table i b) → tableEvaluation d x table = 0 →
      r.readout () d (x,table) = 0

theorem zBridge : (∀ (d : Decomposition) (x : ℤ) (table : Fin d.m → Bool → ℤ),
    (∀ i b, message d x i b = table i b) → tableEvaluation d x table = 0 →
      evaluation d.graph x = 0) ↔ zArena.Law zActual := Iff.rfl

theorem zBadLaw : ¬ zArena.Law zBad := by
  intro h
  let table : Fin one.m → Bool → ℤ := fun i => Fin.elim0 i
  have he := h one 0 table (by intro i; exact Fin.elim0 i) (by decide)
  change (1 : ℤ) = 0 at he
  norm_num at he

theorem zDependence : ObservationalDependence ZSig zActual := by
  intro i
  let table : Fin one.m → Bool → ℤ := fun i => Fin.elim0 i
  refine ⟨one, (0,table), (1,table), ?_⟩
  change evaluation one.graph 0 ≠ evaluation one.graph 1
  rw [reassembly, reassembly]
  decide

def zRegistration : Registration zArena
    (∀ (d : Decomposition) (x : ℤ) (table : Fin d.m → Bool → ℤ),
      (∀ i b, message d x i b = table i b) → tableEvaluation d x table = 0 →
        evaluation d.graph x = 0) where
  actual := zActual
  bridge := zBridge
  variation := ⟨zero_of_messages, zBad, zBadLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zBad, ?_, rfl, zBadLaw⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := zDependence


noncomputable def registration_1 : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.reassembly)
    (type_of% (realize RSig (fun _ d x => evaluation d.graph x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.reassembly.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.rRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rArena⟩
  objectArena := .source ⟨rArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rArena ⟨rRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RSig (fun _ d x => evaluation d.graph x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_2 : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.zero_of_messages)
    (type_of% (realize ZSig (fun _ d s => evaluation d.graph s.1) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.zero_of_messages.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.zRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨zArena⟩
  objectArena := .source ⟨zArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zArena ⟨zRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ZSig (fun _ d s => evaluation d.graph s.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
