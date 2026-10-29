import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Permutation.StronglyComplementaryPermutationMaximum
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the exact maximum size of strongly complementary permutation families. -/

namespace Reg.D5.S3.Combinatorics.Permutation.StronglyComplementaryPermutationMaximum

open _root_.StronglyComplementaryPermutationMaximum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The equality relation on the two natural-number operands of the maximum formula. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain the full dimension quantifier, positivity hypothesis, and maximum formula. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    R.readout () () (maxStronglyComplementary n) (2 ^ padicValNat 2 n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by decide)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hbad : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  exact Nat.one_ne_zero hbad

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.StronglyComplementaryPermutationMaximum.result)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Permutation.StronglyComplementaryPermutationMaximum.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Permutation.StronglyComplementaryPermutationMaximum.source_registration
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
    owner := `D5.S3.Combinatorics.Permutation.StronglyComplementaryPermutationMaximum
    definition := some {
      owner := `D5.S3.Combinatorics.Permutation.StronglyComplementaryPermutationMaximum
      name := `StronglyComplementaryPermutationMaximum.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Permutation.StronglyComplementaryPermutationMaximum
