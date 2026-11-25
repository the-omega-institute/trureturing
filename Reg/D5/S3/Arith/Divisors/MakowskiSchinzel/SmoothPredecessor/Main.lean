import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Main
import Reg.Support.DependentFamily

/-! Source-bound audit of both sigma-totient inequalities under smooth predecessors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Main

open _root_.D5.S3.Arith.MakowskiSchinzel
open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => ArithmeticFunction.sigma 1 n.totient) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), (∀ q ∈ n.primeFactors, q - 1 ∈ Nat.smoothNumbers 98) →
    n ≤ 2 * R.readout () () n ∧
      (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hbad := (h 1 (by simp)).1
  norm_num [rejected, realize] at hbad

def evidence : Registration arena (type_of% @makowski_schinzel_of_smooth_predecessors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨makowski_schinzel_of_smooth_predecessors, rejected, rejected_law⟩
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
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@makowski_schinzel_of_smooth_predecessors) (Realization signature) Type Unit where
  unitName := .str
    (.str `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
      "makowski_schinzel_of_smooth_predecessors") "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Main.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => ArithmeticFunction.sigma 1 n.totient) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Main
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Main
