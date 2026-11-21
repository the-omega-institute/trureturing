import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.ErdosNicolas.KernelCriterion
import Reg.Support.DependentFamily

/-! Source-bound audit of the complete prime-power induction criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.ErdosNicolas.KernelCriterion

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
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p a m L : ℕ} {bA bB F : ℚ}
    (_ : p.Prime) (_ : ¬p ∣ m) (_ : 0 < L)
    (_ : hHat m ≤ bA * m.divisors.card)
    (_ : hHat ((p ^ a * m) / p) ≤ bB * a * m.divisors.card)
    (_ : crossResidual L m.divisors
      (((p ^ a * m) / p).divisors.image (p * ·)) ≤ F * m.divisors.card)
    (_ : KernelTest a p L bA bB F),
    R.readout () () (p ^ a * m) < ((p ^ a * m).divisors.card : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (p := 2) (a := 1) (m := 1) (L := 2)
    (bA := 0) (bB := 0) (F := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hHat, pairSum])
    (by norm_num [hHat, pairSum])
    (by norm_num [crossResidual, w, Nat.dist])
    (by norm_num [KernelTest, criterionGap])
  norm_num [rejected, realize, Nat.Prime.divisors (by norm_num : Nat.Prime 2)] at he

def evidence : Registration arena (type_of% @kernel_criterion_prime_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_criterion_prime_power, rejected, rejected_law⟩
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
    (@kernel_criterion_prime_power) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ErdosNicolas.kernel_criterion_prime_power.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.ErdosNicolas.KernelCriterion.evidence
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
    owner := `D5.S3.Arith.Divisors.ErdosNicolas.KernelCriterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms audit

end
end Reg.D5.S3.Arith.Divisors.ErdosNicolas.KernelCriterion
