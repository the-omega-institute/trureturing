import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.DesignatedTupleEuler
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Partitions.DesignatedTupleEuler
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Partitions.DesignatedTupleEuler

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ N : ℕ, r.readout () () (count 6 N : ℤ)
    (PowerSeries.coeff N (quotient ^ 6))

theorem sourceBridge :
    (type_of% (@D5.S3.Combinatorics.Partitions.DesignatedTupleEuler.count_six_eq_coeff)) ↔
      arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := count_six_eq_coeff

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℤ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

def family : Registration arena
    (type_of% (@D5.S3.Combinatorics.Partitions.DesignatedTupleEuler.count_six_eq_coeff)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.DesignatedTupleEuler.count_six_eq_coeff)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.DesignatedTupleEuler.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.DesignatedTupleEuler.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.DesignatedTupleEuler
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.DesignatedTupleEuler
