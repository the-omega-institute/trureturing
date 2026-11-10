import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteGreedyFamilyTransport

/- UNCOMPILED source-operand registration. The selected semantic occurrence is
   the original `a ∈ F` operand of `@mem_remaining`; sourceSelection remains none
   because the compiled occurrence path and binder selector are still a native
   phase obligation. The source law and all witness proofs are complete here. -/

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteGreedyFamilyTransport

namespace Reg.D5.S3.Geometry.FiniteGreedyFamilyTransport
universe u

abbrev signature : Signature where
  Params := Σ V : Type u, Finset (Finset V)
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p a =>
      @Decidable.decide (a ∈ p.2) (Classical.propDecidable (a ∈ p.2)))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [dv : DecidableEq V]
    (F : Finset (Finset V)) (v : V) (a : Finset V),
    a ∈ remaining F v ↔
      (R.readout () ⟨V, F⟩ a = true) ∧ flip v a ∉ F

private theorem bridge : (type_of% (@mem_remaining.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V dv F v a
    simpa [actual, realize] using (@h V dv F v a)
  · intro h V dv F v a
    simpa [actual, realize] using (@h V dv F v a)

private def testV : Type u := ULift.{u} Unit
private def testv : testV := ⟨()⟩
private def testParameters : signature.Params := ⟨testV, {∅}⟩
private def presentState : signature.State testParameters := ∅
private def absentState : signature.State testParameters := {testv}

private theorem present : actual.{u}.readout () testParameters presentState = true := by
  simp [actual, realize, testParameters, testV, testv, presentState]

private theorem absent : ¬ (actual.{u}.readout () testParameters absentState = true) := by
  simp [actual, realize, testParameters, testV, testv, absentState]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testV (Classical.decEq testV) ({∅} : Finset (Finset testV)) testv ∅
  have hl : (∅ : Finset testV) ∈ remaining ({∅} : Finset (Finset testV)) testv := by
    apply (mem_remaining _ _ _).mpr
    simp [flip, testv]
  have hx := hh.mp hl
  simpa [rejected, realize] using hx.1

private theorem source_law : arena.{u}.Law actual :=
  bridge.mp (@mem_remaining.{u})

private theorem actual_nonconstant :
    ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨testParameters, presentState, absentState, ?_⟩
  simp [actual, realize, testParameters, testV, testv, presentState, absentState]

def family : Registration arena.{u} (type_of% (@mem_remaining.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_nonconstant

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_remaining.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGreedyFamilyTransport.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGreedyFamilyTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a =>
      @Decidable.decide (a ∈ p.2) (Classical.propDecidable (a ∈ p.2)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Native pending: resolve the compiled `a ∈ F` occurrence and its selector later.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteGreedyFamilyTransport
