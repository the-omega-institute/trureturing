import D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Criterion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! A source-bound audit of the odd predecessor sigma-totient criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Criterion

open _root_.D5.S3.Arith.MakowskiSchinzel.EulerCondition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => psi n * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout () () n ≤ 2 * (ArithmeticFunction.sigma 1 n.totient : ℚ) ∧
      (Odd n → psi n * n ≤ (ArithmeticFunction.sigma 1 n.totient : ℚ)) ∧
      ((_root_.D5.S3.Arith.MakowskiSchinzel.nonFermatFactors n).Nonempty →
        psi n * n < 2 * (ArithmeticFunction.sigma 1 n.totient : ℚ) ∧
          (Odd n → psi n * n < (ArithmeticFunction.sigma 1 n.totient : ℚ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1).1
  norm_num [rejected, realize] at hh

def evidence : Registration arena (type_of% @psi_mul_le_sigma_totient) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨psi_mul_le_sigma_totient, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, psi, oddPredecessorPart,
      _root_.D5.S3.Arith.MakowskiSchinzel.nonFermatFactors, Nat.abundancyIndex]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@psi_mul_le_sigma_totient) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.EulerCondition.psi_mul_le_sigma_totient.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Criterion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => psi n * n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Criterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Criterion
