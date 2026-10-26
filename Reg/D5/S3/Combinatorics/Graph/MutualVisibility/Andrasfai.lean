import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai

/-! Source-faithful dependent-family observations for the original-host
obstruction and periodic-avoidance theorems. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai

open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev obstructionScope := type_of% (@visible_iff_no_obstruction)
abbrev periodicScope := type_of% (@visible_iff_periodic_avoidance)

abbrev sourceSignature : Signature where
  Params := ℕ
  State m := Finset (Vertex m)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun i m X => by
    classical
    exact if i then decide (¬ Obstruction m X) else decide (Visible (host m) X))
    (fun e => nomatch e)

abbrev obstructionArena : Arena where
  signature := sourceSignature
  Law r := ∀ m X, (r.readout false m X = true ↔ r.readout true m X = true)

theorem obstruction_source_bridge : obstructionScope ↔ obstructionArena.Law actual := by
  simp [obstructionScope, obstructionArena, actual, realize]

theorem obstruction_actual_positive : obstructionArena.Law actual :=
  obstruction_source_bridge.mp visible_iff_no_obstruction

private theorem actual_empty (i : Bool) (m : ℕ) : actual.readout i m ∅ = true := by
  have hn : ¬ Obstruction m ∅ := (visible_iff_no_obstruction m ∅).mp (visible_empty _)
  cases i <;> simp [actual, realize, visible_empty, hn]

private theorem actual_full (i : Bool) : actual.readout i 1 Finset.univ = false := by
  have ho : Obstruction 1 Finset.univ :=
    ⟨0,1,by omega,by omega,by simp,by simp,by simp⟩
  have hv : ¬ Visible (host 1) Finset.univ := by
    intro h
    exact (visible_iff_no_obstruction 1 Finset.univ).mp h ho
  cases i <;> simp [actual, realize, hv, ho]

def rejected (i : Bool) : Realization sourceSignature :=
  realize sourceSignature (fun j m X => if j=i then false else actual.readout j m X)
    (fun e => nomatch e)

private theorem rejected_law (i : Bool) : ¬ obstructionArena.Law (rejected i) := by
  intro h
  have he := h 0 ∅
  cases i <;> simp [rejected,realize] at he <;> rw [actual_empty] at he <;> contradiction

def obstructionFamily : Registration obstructionArena obstructionScope where
  actual := actual
  bridge := obstruction_source_bridge
  variation := ⟨obstruction_actual_positive, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      funext m X
      simp [rejected,realize,hji]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1,∅,Finset.univ,?_⟩
    rw [actual_empty,actual_full]
    intro he
    cases he

noncomputable def registration_obstruction :
    Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0} (@visible_iff_no_obstruction)
      (type_of% (realize sourceSignature (fun i m X => by
        classical
        exact if i then decide (¬ Obstruction m X) else decide (Visible (host m) X))
          (fun e => nomatch e))) (Type → Type) Unit where
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai.visible_iff_no_obstruction
    "Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai/obstructionArena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai.obstructionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨obstructionArena⟩
  objectArena := .source ⟨obstructionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source obstructionArena ⟨obstructionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sourceSignature (fun i m X => by
    classical
    exact if i then decide (¬ Obstruction m X) else decide (Visible (host m) X))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Finset
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body","body","fn","arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := true },
      { path := #["body","body","arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg","arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def periodicActual : Realization sourceSignature :=
  realize sourceSignature (fun i m X => by
    classical
    exact if i then decide (∀ u k, ¬ ForbiddenFactor m X u k)
      else decide (Visible (host m) X)) (fun e => nomatch e)

abbrev periodicArena : Arena where
  signature := sourceSignature
  Law r := ∀ m, 1 ≤ m → ∀ X,
    (r.readout false m X = true ↔ r.readout true m X = true)

theorem periodic_source_bridge : periodicScope ↔ periodicArena.Law periodicActual := by
  simp [periodicScope,periodicArena,periodicActual,realize]

theorem periodic_actual_positive : periodicArena.Law periodicActual :=
  periodic_source_bridge.mp visible_iff_periodic_avoidance

/-- The periodic source bridge is retained without claiming a finished audit. -/
def periodicCertificate : Option (Registration periodicArena periodicScope) := none

end
end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
