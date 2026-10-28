import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.LaplaceEntropy
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open _root_.D5.S3.Quantum.Subentropy.LaplaceEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Subentropy.LaplaceEntropy

universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
    (p x : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hx : ∀ i, 0 ≤ x i),
    let a := ∑ i, p i * x i
    IntegrableOn (fun t : ℝ => a / (t + a) - ∑ i, p i * (x i / (t + x i)))
        (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), a / (t + a) - ∑ i, p i * (x i / (t + x i))) =
        ∑ i, p i * (x i * Real.log (x i)) - a * R.readout () () a
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hv := @h (ULift.{u} Unit) inferInstance (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num)
  norm_num [rejected, realize] at hv
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, Real.exp 1, ?_⟩
  simp [actual, realize]
def source_registration : Registration arena.{u} (type_of% @entropy_jensen_resolvent.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_jensen_resolvent, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entropy_jensen_resolvent.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.LaplaceEntropy.entropy_jensen_resolvent.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.LaplaceEntropy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.LaplaceEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Laplace
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
    (p x : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hx : ∀ i, 0 ≤ x i),
    let a := ∑ i, p i * x i
    IntegrableOn
      (fun s : ℝ => (∑ i, p i * Real.exp (-s*x i) - Real.exp (-s*a)) / s^2)
        (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ),
        (∑ i, p i * Real.exp (-s*x i) - Real.exp (-s*a)) / s^2) =
        ∑ i, p i * (x i * Real.log (x i)) - a * R.readout () () a
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hv := @h (ULift.{u} Unit) inferInstance (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (by simp) (fun _ => by norm_num)
  norm_num [rejected, realize] at hv

def source_registration : Registration arena.{u} (type_of% @entropy_jensen_laplace.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_jensen_laplace, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entropy_jensen_laplace.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.LaplaceEntropy.entropy_jensen_laplace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.LaplaceEntropy.Laplace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.LaplaceEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Laplace

end Reg.D5.S3.Quantum.Subentropy.LaplaceEntropy
