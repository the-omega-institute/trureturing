import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber

/-! The full-telescope intrinsic actual-image source audit attempt. -/

noncomputable section
open Set Matrix MvPolynomial LeanInformationAudit
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Word)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber

namespace IntrinsicActual

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => Prop × ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ m => (intrinsicActualQ2Fiber m, m)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ m => (False, m)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, (R.readout () () m).1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [actual, realize]

def family : Registration arena (type_of% (@intrinsic_actual_q2_fiber)) where
  actual := actual
  bridge := by
    simp [arena, actual, realize]
  variation := ⟨by
    intro m
    exact intrinsic_actual_q2_fiber m, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@intrinsic_actual_q2_fiber) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber.IntrinsicActual.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber.IntrinsicActual.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => (intrinsicActualQ2Fiber m, m))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber
    definition := none
    coordinates := #[0]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end IntrinsicActual


namespace quotientValidityDomain_open
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @quotientValidityDomain_open)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @quotientValidityDomain_open) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotientValidityDomain_open,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@quotientValidityDomain_open) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber.quotientValidityDomain_open.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber.quotientValidityDomain_open.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end quotientValidityDomain_open

namespace quotientValidityDomain_nonempty
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @quotientValidityDomain_nonempty)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @quotientValidityDomain_nonempty) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotientValidityDomain_nonempty,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@quotientValidityDomain_nonempty) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber.quotientValidityDomain_nonempty.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber.quotientValidityDomain_nonempty.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end quotientValidityDomain_nonempty

end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber
