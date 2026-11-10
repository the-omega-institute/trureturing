import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteVertexDominationCollapse

/- SOURCE-ONLY REPAIR; UNCOMPILED.
The unchanged original orderedLowers_mem is the binding. Only its literal RHS
atom v ∈ s is observed, with the original s as the state operand. The original
type V and original vertex v : V are the only coordinates, in that order.
No complex, dictionary, distinctness proof or extension proof is a coordinate.
The complete original telescope and all other clauses remain in arena.Law.
No native source selection, kernel acceptance or enrollment is claimed. -/

noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteGraphVertexSubstitution
open _root_.D5.S3.Geometry.FiniteVertexDominationCollapse

namespace Reg.D5.S3.Geometry.FiniteVertexDominationCollapse
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

/-- Symbolic predicate reflection matches CompiledSourceScope.mkDecide. -/
def actual : Realization signature.{u} :=
  realize signature
    (fun _ p s => @Decidable.decide (p.2 ∈ s)
      (Classical.propDecidable (p.2 ∈ s)))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- The original universal law, replacing only the original RHS v ∈ s atom. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (K : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (hExt : Extends K u v) (s : Finset V),
    s ∈ orderedLowers K u v huv hExt ↔
      s ∈ K ∧ (R.readout () ⟨V, v⟩ s = true) ∧ u ∉ s

private theorem actual_eq_true {V : Type u} (v : V) (s : Finset V) :
    actual.{u}.readout () ⟨V, v⟩ s = true ↔ v ∈ s := by
  classical
  simp [actual, realize]

private theorem bridge :
    (type_of% (@orderedLowers_mem.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv K u v huv hExt s
    simpa only [actual_eq_true] using (@h V fv dv K u v huv hExt s)
  · intro h V fv dv K u v huv hExt s
    simpa only [actual_eq_true] using (@h V fv dv K u v huv hExt s)

private theorem source_law : arena.{u}.Law actual :=
  bridge.mp (@orderedLowers_mem.{u})

/- The counterfactual is tested on the original edgeless restricted complex,
with a genuine extension hypothesis and the genuine nonempty face {v}. -/
private abbrev testV : Type u := ULift.{u} Bool
private abbrev testu : testV.{u} := ⟨false⟩
private abbrev testv : testV.{u} := ⟨true⟩

private abbrev testK : PreAbstractSimplicialComplex testV.{u} :=
  restricted (⊥ : SimpleGraph testV.{u}) (fun _ => True)

private theorem test_distinct : testu.{u} ≠ testv.{u} := by
  intro h
  exact Bool.false_ne_true (congrArg ULift.down h)

private theorem test_extension : Extends testK.{u} testu testv :=
  graph_extends (⊥ : SimpleGraph testV.{u}) (fun _ => True) testu testv
    test_distinct trivial (by intro a _ ha; simp at ha)

private theorem test_face : ({testv.{u}} : Finset testV.{u}) ∈ testK := by
  refine ⟨Finset.singleton_nonempty _, ?_, fun _ _ => trivial⟩
  intro a ha b hb hab hadj
  exact hadj

private theorem test_lower :
    ({testv.{u}} : Finset testV.{u}) ∈
      orderedLowers testK testu testv test_distinct test_extension := by
  exact (orderedLowers_mem testK testu testv test_distinct test_extension _).2
    ⟨test_face, by simp, by simpa using test_distinct.{u}⟩

private theorem test_present :
    actual.{u}.readout () ⟨testV.{u}, testv⟩ {testv} = true := by
  exact (actual_eq_true testv _).mpr (Finset.mem_singleton_self _)

private theorem test_absent :
    actual.{u}.readout () ⟨testV.{u}, testv⟩ ∅ = false := by
  simp [actual, realize]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testV.{u} (inferInstance : Fintype testV.{u})
    (inferInstance : DecidableEq testV.{u}) testK testu testv
    test_distinct test_extension {testv}
  have hf := (hh.mp test_lower).2.1
  change (false : Bool) = true at hf
  cases hf

private theorem variation : Variation arena.{u} actual :=
  ⟨source_law, rejected, rejected_law⟩

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

/-- Two different states at the SAME original (V,v) coordinate. -/
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨testV.{u}, testv⟩, ∅, {testv}, ?_⟩
  intro he
  have hf : (false : Bool) = true :=
    test_absent.symm.trans (he.trans test_present)
  cases hf

def family : Registration arena.{u} (type_of% (@orderedLowers_mem.{u})) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@orderedLowers_mem.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteVertexDominationCollapse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteVertexDominationCollapse.family
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
    (fun _ p s => @Decidable.decide (p.2 ∈ s)
      (Classical.propDecidable (p.2 ∈ s)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/- sourceSelection = none is a remaining obligation, never an audit receipt.
Semantic occurrence: the RHS middle atom v ∈ s of orderedLowers_mem, inside
s ∈ K ∧ v ∈ s ∧ u ∉ s. State operand: its actual original Finset V argument s.
Raw coordinates: the original V : Type u, then the original v : V; the packing
is exactly Sigma, with state Finset V and Bool output, Unit role, Empty anchor.
Pending REAL compiled evidence: owner/universe/telescope and binder modes;
occurrence path, lexical coordinate ordinals and operand path; resolveOriginal
and resolve; dependency closure and inverse projection; field/output/readout
shape checks and exact explicit decision dictionary; reconstruction of the
complete original theorem. No numeric selector or compiled path is supplied.
Kernel, axiom closure, all source audits, independent review and delivery remain
pending. This repairs neither the geometry suppliers nor their native reports. -/

end Reg.D5.S3.Geometry.FiniteVertexDominationCollapse
