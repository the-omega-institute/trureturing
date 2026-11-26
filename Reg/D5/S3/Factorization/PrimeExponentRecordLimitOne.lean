import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.PrimeExponentRecordLimitOne
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the odd-part prime-product bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Factorization.PrimeExponentRecordLimitOne

namespace Reg.D5.S3.Factorization.PrimeExponentRecordLimitOne

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => List ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ m => m.primeFactorsList) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, m ≠ 0 → Odd m → 3 ^ (R.readout () () m).length ≤ m

def rejected : Realization signature :=
  realize signature (fun _ _ m => List.replicate m 3) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by decide) (by decide)
  norm_num [rejected, realize] at hb

def family : Registration arena (type_of% @odd_part_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@odd_part_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 3, ?_⟩
    change Nat.primeFactorsList 1 ≠ Nat.primeFactorsList 3
    simp [Nat.primeFactorsList_prime Nat.prime_three]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@odd_part_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Factorization.PrimeExponentRecordLimitOne.odd_part_lower.audit
  realizationName := `Reg.D5.S3.Factorization.PrimeExponentRecordLimitOne.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.PrimeExponentRecordLimitOne
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Factorization.PrimeExponentRecordLimitOne
