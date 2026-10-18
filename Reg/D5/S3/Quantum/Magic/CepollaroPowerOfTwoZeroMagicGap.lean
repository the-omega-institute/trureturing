import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap

open _root_.D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) [NeZero d] (a b x y : ZMod d),
    R.readout () () (_root_.D5.S3.Quantum.Algebra.WeylDisplacement.displacement d a b x y)
      (if x.val = (y.val + a.val) % d then
        _root_.D5.S3.Observer.WindowRegister.windowRoot d ^ (b.val * y.val) else 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  intro he
  have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @displacement_entry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@displacement_entry, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@displacement_entry) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap.displacement_entry.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap.source_registration
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
    owner := `D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap
