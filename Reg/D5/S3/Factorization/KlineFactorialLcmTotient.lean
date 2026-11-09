import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Factorization.KlineFactorialLcmTotient

namespace Reg.D5.S3.Factorization.KlineFactorialLcmTotient
open _root_.D5.S3.Factorization.KlineFactorialLcmTotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => a (Nat.nth Nat.Prime (j.toNat - 1) - 1))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : ℤ, 1 ≤ j →
    let p := Nat.nth Nat.Prime (j.toNat - 1)
    let m := p - 1
    R.readout () () j =
      (Nat.totient m.factorial : ℚ) / (Nat.totient (Nat.lcmUpto m) : ℚ)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := h 1 (by decide)
  norm_num [rejected, realize, Nat.lcmUpto] at bad

def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 3, ?_⟩
    change a (Nat.nth Nat.Prime ((1 : ℤ).toNat - 1) - 1) ≠
      a (Nat.nth Nat.Prime ((3 : ℤ).toNat - 1) - 1)
    simp only [show (1 : ℤ).toNat - 1 = 0 from rfl,
      show (3 : ℤ).toNat - 1 = 2 from rfl,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_two_eq_five]
    norm_num [a, Nat.lcmUpto, lcm_eq_nat_lcm, Nat.lcm,
      show Finset.Icc 1 1 = {1} from by decide,
      show Finset.Icc 1 4 = {1, 2, 3, 4} from by decide]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Factorization.KlineFactorialLcmTotient.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.KlineFactorialLcmTotient.unit
  realizationName := `Reg.D5.S3.Factorization.KlineFactorialLcmTotient.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ j => a (Nat.nth Nat.Prime (j.toNat - 1) - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.KlineFactorialLcmTotient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Factorization.KlineFactorialLcmTotient
