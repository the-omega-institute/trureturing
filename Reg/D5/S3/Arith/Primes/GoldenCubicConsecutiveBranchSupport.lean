import D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-! Source-bound registration of the exact consecutive branch exponent. -/

set_option autoImplicit false
namespace Reg.D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport
open _root_.D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
noncomputable section
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ k => 3^k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ k : ℕ,
    let D := r.readout () () k
    ∀ {K : Type u} [Field K] (_h3 : (3:K) ≠ 0),
      (∀ v : K, (v-1)*branchProduct v k = v^D-1) ∧
      (∀ (a : K) (_ha : a ≠ 0),
        (∃ i < k, (orbit (a-a⁻¹) i)^2 = -3) ↔ (a^2)^D=1 ∧ a^2≠1) ∧
      (∀ (x δ : K) (i j : ℕ) (_hδ : δ^2 = -3)
        (_hi : orbit x i = δ) (_hj : (orbit x j)^2 = -3),
        i=j ∧ x^2+4 ≠ 0 ∧ ((orbit (C x + X : K[X]) i)-C δ).coeff 1 ≠ 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let K := ULift.{u} (ZMod 5)
  have h3 : (3:K) ≠ 0 := fun hh =>
    (by decide : (3:ZMod 5) ≠ 0) (congrArg ULift.down hh)
  have hz := (@h 0 K inferInstance h3).1 (0:K)
  change ((0:K)-1)*1=0^0-1 at hz
  have hn : -(1:K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  exact hn (by simpa using hz)

def family : Registration arena.{u} (type_of% @consecutive_branch_support.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@consecutive_branch_support.{u},rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨(),0,1,by decide +kernel⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@consecutive_branch_support.{u}) (type_of% actual) Unit Unit where
  unitName := .str
    `D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport.consecutive_branch_support
    "__information_unit"
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Arith.Primes.GoldenCubicConsecutiveBranchSupport
