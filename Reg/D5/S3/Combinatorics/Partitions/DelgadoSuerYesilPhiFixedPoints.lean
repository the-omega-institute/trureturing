import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints

open _root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints
open _root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation (NumericalSet members
  Semigroup Symmetric PseudoFrobenius AlmostSymmetric phi)
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

/-- The original statement is retained; the readout observes the genus identity of symmetric
semigroups. -/
abbrev arena : Arena where
  signature := signature
  Law Q := ∀ (U : NumericalSet),
    (Symmetric U → phi U = members U ∧
      (∀ f, PseudoFrobenius U f → f = DelgadoSuerYesilPhiRefutation.frobenius U) ∧
      Q.readout () () (2 * U.gaps.card) (DelgadoSuerYesilPhiRefutation.frobenius U + 1)) ∧
    (Semigroup U →
      (phi U = members U ↔ Symmetric U) ∧
      (Symmetric U ↔ ∀ f, PseudoFrobenius U f → f = DelgadoSuerYesilPhiRefutation.frobenius U) ∧
      (Symmetric U → AlmostSymmetric U))

/-- The numerical set with the single gap `1`. -/
private def gapOne : NumericalSet := ⟨{1}, ⟨1, by simp⟩, by simp⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hF : DelgadoSuerYesilPhiRefutation.frobenius gapOne = 1 := by
    simp [DelgadoSuerYesilPhiRefutation.frobenius, gapOne]
  have hsym : Symmetric gapOne := by
    intro a ha
    rw [hF] at ha ⊢
    simp only [members, gapOne, Finset.mem_singleton, Set.mem_ofPred_eq]
    omega
  exact ((h gapOne).1 hsym).2.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℕ)
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints.result)) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints.result, rejected,
      rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints.result) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints.family
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
    owner := `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "arg", "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints
