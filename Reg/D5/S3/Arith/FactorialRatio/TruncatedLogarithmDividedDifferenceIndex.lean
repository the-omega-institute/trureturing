import D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The observed integer is the LCM index or its exact relative quotient.
Each law reads that integer before taking its logarithm or prime valuation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex

open _root_.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset ArithmeticFunction

namespace Index

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n r => differenceIndex n r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨3, 1, 3, ?_⟩
  change differenceIndex 3 1 ≠ differenceIndex 3 3
  decide

namespace Logarithm

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n r : ℕ), 0 < r →
    Real.log (R.readout () n r : ℝ) =
      ∑ q ∈ range n, ((n - r * q : ℕ) : ℝ) * vonMangoldt q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Real.log (2 : ℝ) = 0 := by simpa [rejected, realize] using h 0 1 (by decide)
  exact (ne_of_gt (Real.log_pos (by norm_num))) hz

def family : Registration arena (type_of% @log_differenceIndex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_differenceIndex, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := Index.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_differenceIndex) (Realization signature) ℕ Unit where
  unitName := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.log_differenceIndex.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.Index.Logarithm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => differenceIndex n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Logarithm

namespace Valuation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n r : ℕ), 0 < r → ∀ {p : ℕ}, p.Prime →
    (R.readout () n r).factorization p = ∑ a ∈ range n, (n - r * p ^ (a + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 1 (by decide) Nat.prime_two
  change (2 : ℕ).factorization 2 = _ at hbad
  simpa [Nat.prime_two.factorization_self] using hbad

def family : Registration arena (type_of% @factorization_differenceIndex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@factorization_differenceIndex, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := Index.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@factorization_differenceIndex) (Realization signature) ℕ Unit where
  unitName := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.factorization_differenceIndex.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.Index.Valuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => differenceIndex n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Valuation

end Index

namespace Relative

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => relativeIndex x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change relativeIndex 0 ≠ relativeIndex 1
  decide

namespace ExactQuotient

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℕ,
    differenceIndex (4 * x) 2 ^ 3 ∣
      differenceIndex (4 * x) 1 ^ 2 * differenceIndex (4 * x) 4 ∧
    R.readout () () x * differenceIndex (4 * x) 2 ^ 3 =
      differenceIndex (4 * x) 1 ^ 2 * differenceIndex (4 * x) 4 ∧
    0 < relativeIndex x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 0).2.1
  change 2 * differenceIndex 0 2 ^ 3 = differenceIndex 0 1 ^ 2 * differenceIndex 0 4 at hbad
  simp [differenceIndex] at hbad

def family : Registration arena (type_of% @relativeIndex_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@relativeIndex_spec, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := Relative.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@relativeIndex_spec) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.relativeIndex_spec.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.Relative.ExactQuotient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => relativeIndex x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExactQuotient

namespace Valuation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℕ) {p : ℕ}, p.Prime →
    (R.readout () () x).factorization p =
      ∑ a ∈ range (4 * x), 2 * tentWeight x (p ^ (a + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 Nat.prime_two
  change (2 : ℕ).factorization 2 = _ at hbad
  simpa [Nat.prime_two.factorization_self] using hbad

def family : Registration arena (type_of% @factorization_relativeIndex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@factorization_relativeIndex, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := Relative.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@factorization_relativeIndex) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.factorization_relativeIndex.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.Relative.Valuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => relativeIndex x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Valuation

namespace Logarithm

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℕ,
    Real.log (R.readout () () x : ℝ) =
      2 * ∑ q ∈ range (4 * x), (tentWeight x q : ℝ) * vonMangoldt q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Real.log (2 : ℝ) = 0 := by simpa [rejected, realize] using h 0
  exact (ne_of_gt (Real.log_pos (by norm_num))) hz

def family : Registration arena (type_of% @log_relativeIndex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_relativeIndex, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := Relative.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_relativeIndex) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.log_relativeIndex.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex.Relative.Logarithm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => relativeIndex x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Logarithm

end Relative
end Reg.D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
