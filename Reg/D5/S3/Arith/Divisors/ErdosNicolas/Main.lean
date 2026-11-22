import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.ErdosNicolas.Main
import Reg.Support.DependentFamily

/-! Source-bound audit of the original universal divisor-gap inequality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.ErdosNicolas.Main

open _root_.D5.S3.Arith.ErdosNicolas
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

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
  realize signature (fun _ _ n => hHat n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => (n.divisors.card : ℚ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 5040 < n → R.readout () () n < (n.divisors.card : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change ∀ n : ℕ, 5040 < n → (n.divisors.card : ℚ) < (n.divisors.card : ℚ) at h
  simp only [lt_self_iff_false] at h
  exact h 5041 (by decide)

def evidence : Registration arena (type_of% @erdos_nicolas) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨erdos_nicolas, rejected, rejected_law⟩
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
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize, hHat, pairSum,
      Nat.Prime.divisors (by norm_num : Nat.Prime 2)]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@erdos_nicolas) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ErdosNicolas.erdos_nicolas.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.ErdosNicolas.Main.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => hHat n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.ErdosNicolas.Main
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms audit

end
end Reg.D5.S3.Arith.Divisors.ErdosNicolas.Main
