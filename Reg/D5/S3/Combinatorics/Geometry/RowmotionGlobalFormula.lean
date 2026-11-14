import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula

/-! The literal final state is the observation of the full initial-set family. -/

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
open _root_.D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula

namespace Reg.D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula

universe u

structure Parameters where
  carrier : Type u
  order : PartialOrder carrier
  length : ℕ
  extension : Fin length ≃ carrier

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Parameters
    (fun p => Set p.carrier) (fun p => Set p.carrier)

def actual : Realization signature.{u} := realize signature
  (fun _ p I => @trace p.carrier p.order p.length p.extension I p.length) Empty.elim

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => ∅) Empty.elim

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {P : Type u} [po : PartialOrder P] {N : ℕ}
    (e : Fin N ≃ P) (_he : ReverseExtension e) (I : Set P) (_hI : I.OrdConnected),
    R.readout () ⟨P, po, N, e⟩ I = formula I

private theorem bridge : (type_of% (@trace_eq_formula.{u})) ↔ arena.{u}.Law actual := Iff.rfl

private theorem empty_image {P : Type u} [PartialOrder P] (x : P) :
    x ∈ formula (∅ : Set P) := by
  refine Or.inl ⟨?_, Set.notMem_empty x⟩
  intro c hc
  obtain ⟨a, ha, _⟩ := mem_upperClosure.mp hc.1.1
  exact False.elim (Set.notMem_empty a ha)

private def oneExtension : Fin 1 ≃ ULift.{u} (Fin 1) := Equiv.ulift.symm

private theorem oneReverse : ReverseExtension oneExtension.{u} := by
  intro x y hxy
  exact False.elim ((not_lt_of_ge (Subsingleton.elim y x ▸ le_refl y)) hxy)

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} (Fin 1)) inferInstance 1 oneExtension oneReverse
    ∅ Set.ordConnected_empty
  change (∅ : Set (ULift.{u} (Fin 1))) = formula ∅ at hh
  have hx := empty_image (ULift.up (0 : Fin 1))
  rw [← hh] at hx
  exact hx

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let P := ULift.{u} (Fin 1)
  let p : Parameters := ⟨P, inferInstance, 1, oneExtension⟩
  refine ⟨p, ∅, Set.univ, ?_⟩
  intro heq
  change trace oneExtension (∅ : Set P) 1 = trace oneExtension Set.univ 1 at heq
  rw [trace_eq_formula oneExtension oneReverse ∅ Set.ordConnected_empty,
    trace_eq_formula oneExtension oneReverse Set.univ Set.ordConnected_univ] at heq
  have hx : ULift.up (0 : Fin 1) ∈ formula (Set.univ : Set P) := by
    rw [← heq]
    exact empty_image _
  have hc : ceiling (Set.univ : Set P) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    exact hc.1.2 (Set.mem_univ c)
  unfold formula at hx
  rw [hc] at hx
  rcases hx with hx | hx
  · exact hx.2 (Set.mem_univ _)
  · obtain ⟨c, hc', _⟩ := mem_lowerClosure.mp hx.1
    exact hc'

def family : Registration arena.{u} (type_of% (@trace_eq_formula.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@trace_eq_formula.{u}), rejected, negative⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected negative
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trace_eq_formula.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula.unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula.family
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
    (fun _ p I => @trace p.carrier p.order p.length p.extension I p.length) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula
