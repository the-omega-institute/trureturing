import D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution

open _root_.D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ+ → ℂ) (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ f n => A f n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ f : ℕ+ → ℂ,
    (∀ n : ℕ, 0 < n →
      R.readout () f n =
        ∑ d ∈ n.divisors, positiveLift f d * (Nat.totient d : ℂ) * H (n / d)) ∧
    (PositiveMultiplicative f →
      A f 1 = 1 ∧ ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b →
        A f (a*b) = A f a * A f b) ∧
    (∀ z : ℂ, ∀ n : ℕ, 0 < n →
      square (fun d => if hd : 0 < d then f ⟨d, hd⟩ else z) n = A f n) ∧
    (∀ n : ℕ, A (fun d : ℕ+ => (d.val : ℂ)) n =
      (_root_.D5.S3.ArithSums.SchulteGcdQuotientRowSumConvolution.rowSum n : ℂ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (fun _ => 1)).1 1 Nat.zero_lt_one
  norm_num [rejected, realize, positiveLift, H] at hbad

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => 1), 0, 1, ?_⟩
    norm_num [actual, realize, A, square, positiveLift]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution.auditUnit
  realizationName := `Reg.D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f n => A f n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution
