import D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open _root_.D5.S1.Dynamics.Symbolic.KhetanLaurent
open _root_.D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra
open _root_.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer

noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ R : Type u, CommRing R
  State p := Configuration p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Configuration p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ _ h => h) (fun e => nomatch e)

abbrev bad : Realization signature.{u} :=
  realize signature (fun _ p _ => by
    letI := p.2
    exact fun x => if x = 0 then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law s := ∀ {R : Type u} [inst : CommRing R] [IsDomain R]
    (h : Configuration R) (hh : FiniteRange h) (v : Lattice) (hv : v ≠ 0)
    (q : Polynomial R) (hq : q ≠ 0)
    (hann : coefficientAct (linePolynomial v q) h = 0),
      Periodic (s.readout () ⟨R, inst⟩ h)

private theorem bad_law : ¬ arena.{u}.Law bad := by
  intro hb
  have hp := @hb (ULift.{u} ℤ) inferInstance inferInstance
    0 (by simp [FiniteRange]) (1, 0) (by simp) 1 (by simp) (by simp)
  obtain ⟨v, hv, hperiod⟩ := hp
  have he := hperiod 0
  have hz : (0 : ULift.{u} ℤ) = 1 := by
    simpa [bad, realize, hv] using he
  exact zero_ne_one hz

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℤ, inferInstance⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have h := congrArg (fun h => (h (0 : Lattice)).down) he
  norm_num [actual, realize] at h

def recurrenceEvidence : Registration arena.{u}
    (∀ {R : Type u} [CommRing R] [IsDomain R]
      (h : Configuration R) (hh : FiniteRange h) (v : Lattice) (hv : v ≠ 0)
      (q : Polynomial R) (hq : q ≠ 0)
      (hann : coefficientAct (linePolynomial v q) h = 0), Periodic h) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonzero_line_annihilator_periodic.{u}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def nonzero_line_annihilator_periodic_registration :
    Contract.Registration
      (@_root_.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer.recurrence_unit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer.recurrenceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨recurrenceEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ h => h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
