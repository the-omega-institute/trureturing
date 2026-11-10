import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCoordinateGreedyMatching

/- UNCOMPILED source-operand registration. The selected semantic occurrence is
   the original `v ∉ a` operand of `@mem_lowers`; sourceSelection remains none
   because the compiled occurrence path and binder selector are still a native
   phase obligation. The source law and all witness proofs are complete here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching

namespace Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching
universe u

abbrev signature : Signature where
  Params := Σ V : Type u, V
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
      @Decidable.decide (p.2 ∉ a) (Classical.propDecidable (p.2 ∉ a)))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (F : Finset (Finset V)) (v : V) (a : Finset V),
    a ∈ lowers F v ↔
      a ∈ F ∧ (R.readout () ⟨V, v⟩ a = true) ∧ insert v a ∈ F

private theorem bridge : (type_of% (@mem_lowers.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv F v a
    simpa [actual, realize] using (@h V fv dv F v a)
  · intro h V fv dv F v a
    simpa [actual, realize] using (@h V fv dv F v a)

private abbrev testV : Type u  := ULift.{u} Unit
private def testv : testV := ⟨()⟩
private def testParameters : signature.Params := ⟨testV, testv⟩

private theorem present : actual.{u}.readout () testParameters ∅ = true := by
  simp [actual, realize, testParameters, testV, testv]

private theorem absent : ¬ (actual.{u}.readout () testParameters {testv} = true) := by
  simp [actual, realize, testParameters, testV, testv]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testV (inferInstance : Fintype testV) (inferInstance : DecidableEq testV) ({∅, {testv}} : Finset (Finset testV))
    testv ∅
  have hl : (∅ : Finset testV) ∈ lowers ({∅, {testv}} : Finset (Finset testV)) testv := by
    apply (mem_lowers _ _ _).mpr
    simp [testv]
  have hx := hh.mp hl
  simpa [rejected, realize] using hx.2.1

private theorem source_law : arena.{u}.Law actual :=
  bridge.mp (@mem_lowers.{u})

private theorem actual_nonconstant :
    ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨testParameters, ∅, {testv}, ?_⟩
  simp [actual, realize, testParameters, testV, testv]

def family : Registration arena.{u} (type_of% (@mem_lowers.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_nonconstant

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_lowers.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching.family
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
      @Decidable.decide (p.2 ∉ a) (Classical.propDecidable (p.2 ∉ a)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Native pending: resolve the compiled `v ∉ a` occurrence and its selector later.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching
