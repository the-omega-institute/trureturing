import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.AffinePartitionFlagMaximum
import Reg.Support.DependentFamily

/-! Source-bound audit of the attained affine partition flag value. -/

namespace Reg.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum

open _root_.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the flag value as the dimension varies, retaining the modulus. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => flagValue p n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the partition, attained value, and upper bound for every competing partition. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (n : ℕ),
    isAffinePartition p n (flagPartition p n) ∧
    sqSum (flagPartition p n) = R.readout () p n ∧
    ∀ parts, isAffinePartition p n parts → sqSum parts ≤ flagValue p n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (h 2 1).2.1
  change sqSum (flagPartition 2 1) = 0 at hzero
  have hvalue := (result 2 1).2.1
  rw [hvalue] at hzero
  norm_num [flagValue] at hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  change flagValue 2 0 ≠ flagValue 2 1
  norm_num [flagValue]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum.unit
  realizationName := `Reg.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p n => flagValue p n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.AffinePartitionFlagMaximum
    definition := some {
      owner := `D5.S3.Quantum.Magic.AffinePartitionFlagMaximum
      name := `D5.S3.Quantum.Magic.AffinePartitionFlagMaximum.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum.result
#print _root_.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Magic.AffinePartitionFlagMaximum
