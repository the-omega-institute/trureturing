import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.LegalMatrixMonoid
import Reg.Support.SingleDependentReadout

/-! Source-bound finite-word readouts on the full theorem telescopes. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.PrimeForms.Crossing.ExactPropagation
open _root_.D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced
open _root_.D5.S3.PrimeForms.SternBrocot.UnimodularGeneration
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.LegalMatrixMonoid

noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.LegalMatrixMonoid

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => List Bool) (fun _ => Mat)

def actual : Realization signature :=
  realize signature (fun _ _ u => futureProduct u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : Mat)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ H : Mat,
    (∃ u : List Bool, R.readout () () u = H) ↔
      (∀ i j, 0 ≤ H i j ∧ ∃ z : ℤ, H i j = (z : ℝ)) ∧
        (H.det = 1 ∨ H.det = -1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hclass := (legal_matrix_monoid actionM).mp
    ⟨[false], by simp [futureProduct]⟩
  obtain ⟨u, hu⟩ := (h actionM).mpr hclass
  have hentry := congrArg (fun A : Mat => A 0 0) hu
  norm_num [rejected, realize, actionM] at hentry

def family : Registration arena (type_of% @legal_matrix_monoid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨legal_matrix_monoid, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), [], [false], ?_⟩
    intro h
    have hentry := congrArg (fun A : Mat => A 0 0) h
    norm_num [actual, realize, futureProduct, actionM] at hentry

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@legal_matrix_monoid) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LegalMatrixMonoid.legal_matrix_monoid.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LegalMatrixMonoid.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => futureProduct u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LegalMatrixMonoid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.LegalMatrixMonoid
