import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound

open _root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation (NumericalSet members
  Symmetric AlmostSymmetric phi)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Partitions

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the bound on the number of
row-deletion outputs at source Frobenius number `F`. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    (∀ S : NumericalSet, AlmostSymmetric S → ∃ V : NumericalSet, members V = phi S ∧
      Symmetric V ∧ V.gaps.card = DelgadoSuerYesilPhiRefutation.frobenius S - S.gaps.card + 1 ∧
      DelgadoSuerYesilPhiRefutation.frobenius V =
        2 * (DelgadoSuerYesilPhiRefutation.frobenius S - S.gaps.card + 1) - 1 ∧
      DelgadoSuerYesilPhiRefutation.frobenius V ≤ DelgadoSuerYesilPhiRefutation.frobenius S) ∧
    (∀ F : ℕ,
      (1 ≤ F → 1 ≤ {X | X ∈ phi '' {S | AlmostSymmetric S ∧
            DelgadoSuerYesilPhiRefutation.frobenius S = F} ∧
          ∀ a b, a ∈ X → b ∈ X → a + b ∈ X}.ncard) ∧
      {X | X ∈ phi '' {S | AlmostSymmetric S ∧ DelgadoSuerYesilPhiRefutation.frobenius S = F} ∧
          ∀ a b, a ∈ X → b ∈ X → a + b ∈ X}.ncard ≤
        (phi '' {S | AlmostSymmetric S ∧ DelgadoSuerYesilPhiRefutation.frobenius S = F}).ncard ∧
      Q.readout () ()
        (phi '' {S | AlmostSymmetric S ∧ DelgadoSuerYesilPhiRefutation.frobenius S = F}).ncard
        (2 ^ ((F + 1) / 2 - 1)))

private theorem rejected_law : ¬ arena.Law rejected := fun h => (h.2 0).2.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℕ)
  norm_num [actual, realize] at hh

def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound.result, rejected,
      rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound.result)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound
