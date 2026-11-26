import D5.S3.Arith.CMJet.Prime
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The restricted derivative is observed on every polynomial pair over the residue ring. -/

noncomputable section

namespace Reg.D5.S3.Arith.CMJet.Prime

open LeanInformationAudit
open _root_.D5.S3.Arith.CMJet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

abbrev readoutSignature : Signature :=
  signature ℕ (fun p => Curve (ZMod p)) (fun p => Curve (ZMod p))

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ p z => iter p z) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {p : ℕ} [Fact p.Prime], p % 4 = 3 → ∀ z : Curve (ZMod p),
    R.readout () p z = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbad : (1 : Curve (ZMod 3)) = 0 := h (p := 3) (by decide) 0
  exact one_ne_zero hbad

def family : Registration arena (type_of% @inert_iter_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inert_iter_zero, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨0, 0, 1, ?_⟩
    simpa [actual, realize] using (zero_ne_one : (0 : Curve (ZMod 0)) ≠ 1)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@inert_iter_zero) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.Prime.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.Prime.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature (fun _ p z => iter p z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.Prime
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.CMJet.Prime
