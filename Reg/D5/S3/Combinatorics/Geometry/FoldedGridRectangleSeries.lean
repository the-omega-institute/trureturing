import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries
import Reg.Support.SingleDependentReadout

/-! A source-bound variation of the complete rectangle-count family. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries
open LeanInformationAudit PowerSeries

noncomputable section
namespace Reg.D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (mk (fun n => (R.readout () () n : ℚ)) =
      (1-3*X-9*X^2+24*X^3)*((1-2*X)*(1-4*X)*(1-8*X^2))⁻¹) ∧
    (∀ n : ℕ, 4 ≤ n → (R.readout () () n : ℤ) =
      6*(R.readout () () (n-1):ℤ)-48*(R.readout () () (n-3):ℤ)+
      64*(R.readout () () (n-4):ℤ))

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have h0 := congrArg (coeff 0) h.1
  norm_num [rejected, realize] at h0

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    change ObservationalDependence signature actual
    intro i
    cases i
    exact ⟨(), 0, 1, by decide⟩

noncomputable def resultRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries.result)
    (type_of% (realize signature (fun _ _ n => a n) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries.resultUnit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries
    definition := some {
      owner := `D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries
      name := `D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries
