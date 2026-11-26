import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets

open _root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation (NumericalSet members
  Semigroup Symmetric AlmostSymmetric phi)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Partitions

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the total count of symmetric
numerical sets with Frobenius number `2h - 1`. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    (∀ (U : NumericalSet) (k : ℕ), Symmetric U →
      DelgadoSuerYesilPhiRefutation.frobenius U ≠ 2 * k) ∧
    (∀ h : ℕ, 1 ≤ h →
      Q.readout () ()
        {U : NumericalSet | Symmetric U ∧
          DelgadoSuerYesilPhiRefutation.frobenius U = 2 * h - 1}.ncard (2 ^ (h - 1))) ∧
    (∀ h : ℕ, 2 ≤ h →
      {U : NumericalSet | Symmetric U ∧ DelgadoSuerYesilPhiRefutation.frobenius U = 2 * h - 1 ∧
        1 ∈ members U}.ncard = 2 ^ (h - 2) ∧
      {U : NumericalSet | Symmetric U ∧ DelgadoSuerYesilPhiRefutation.frobenius U = 2 * h - 1 ∧
        1 ∉ members U}.ncard = 2 ^ (h - 2) ∧
      2 ^ (h - 2) ≤ {U : NumericalSet | Symmetric U ∧
        DelgadoSuerYesilPhiRefutation.frobenius U = 2 * h - 1 ∧
        ∀ S : NumericalSet, Semigroup S → phi S ≠ members U}.ncard) ∧
    (∀ U : NumericalSet, DelgadoSuerYesilPhiRefutation.frobenius U = 1 →
      members U = {n | n ≠ 1} ∧ ∃ S : NumericalSet, AlmostSymmetric S ∧ phi S = members U)

private theorem rejected_law : ¬ arena.Law rejected := fun h => h.2.1 1 le_rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℕ)
  norm_num [actual, realize] at hh

def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets.result, rejected,
      rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets.result)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets
