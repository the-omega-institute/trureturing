import D5.S1.Words.Powers.ZeckendorfDeletion
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S1.Words.Powers.ZeckendorfDeletion
open _root_.D5.S1.Words.Powers.ZeckendorfDeletion
open _root_.D5.S1.Words
open _root_.D5.S1.Words.Powers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev sig : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig := realize sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law R := ∀ n : ℕ, goldenSubstStart (deleteLeast (R.readout () () n)) ≤ n ∧
    n < goldenSubstStart (deleteLeast n + 1)
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).1
  have hd : deleteLeast 2 = 1 := by decide +kernel
  have hs : goldenSubstStart 1 = 2 := by decide +kernel
  change goldenSubstStart (deleteLeast 2) ≤ 0 at h0
  rw [hd, hs] at h0
  omega
private theorem depends : ObservationalDependence sig actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; omega⟩
def evidence : Registration arena (type_of% @deletion_block) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨deletion_block, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@deletion_block) (Realization sig) Unit Unit where
  unitName := `D5.S1.Words.Powers.ZeckendorfDeletion.deletion_block.__information_unit
  realizationName := `Reg.D5.S1.Words.Powers.ZeckendorfDeletion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Powers.ZeckendorfDeletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
end

end Reg.D5.S1.Words.Powers.ZeckendorfDeletion
