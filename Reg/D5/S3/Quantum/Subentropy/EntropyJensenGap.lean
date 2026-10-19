import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.EntropyJensenGap
import Reg.Support.SingleDependentReadout

/-! Full-source registration for the finite entropy Jensen gap laws. -/

noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Quantum.Subentropy.EntropyJensenGap
open _root_.D5.S3.Quantum.Subentropy.EntropyJensenGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x y => x + 1 = y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S : Type u} [Fintype S] [Nonempty S],
    (∀ (a : S → ℝ), (∀ s, 0 ≤ a s) → 0 ≤ entropyJensenGap a) ∧
    (∀ (c : ℝ) (a : S → ℝ), 0 ≤ c →
      R.readout () () (entropyJensenGap (fun s => c * a s)) (c * entropyJensenGap a)) ∧
    ConvexOn ℝ {a : S → ℝ | ∀ s, 0 ≤ a s} entropyJensenGap

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := (@h (ULift.{u} Unit) inferInstance inferInstance).2.1 0 0 (le_refl 0)
  norm_num [rejected, realize, entropyJensenGap, finiteAverage] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def source_registration : Registration arena.{u} (type_of% @entropyJensenGap_laws.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropyJensenGap_laws, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entropyJensenGap_laws.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.EntropyJensenGap.entropyJensenGap_laws.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.EntropyJensenGap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.EntropyJensenGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end Reg.D5.S3.Quantum.Subentropy.EntropyJensenGap
