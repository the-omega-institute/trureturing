import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound sum observations for the mixed-exponent multiplicity criterion. -/

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid

abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ × ℕ
  State := fun _ => List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ L => L.sum) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a b m n : ℕ, Nat.Coprime m 6 →
    let k := 2 ^ (a + 1) * 3 ^ (b + 1) * m
    let r := 2 ^ a * 3 ^ b
    (∃ L : List ℕ, R.readout () (a,b,m,n) L = n ∧ ∀ ell ∈ L,
      0 < ell ∧ ell ∣ k ∧
        (Nat.gcd (k / ell) 36 = 1 ∨ Nat.gcd (k / ell) 36 = 2 ∨
          Nat.gcd (k / ell) 36 = 3)) ↔ (r ∣ n ∧ n ≠ r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨L, hL, _⟩ := (h 0 0 1 0 (by decide)).mpr (by norm_num)
  change 1 = 0 at hL
  exact Nat.one_ne_zero hL

def family : Registration arena (type_of% allowed_sum_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨allowed_sum_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(0,0,1,0), [], [1], by change (0 : ℕ) ≠ 1; decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@allowed_sum_iff)
    (type_of% (realize signature (fun _ _ L => L.sum) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid.allowed_sum_iff.audit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => L.sum) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (List ℕ)
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","arg","body","fn","arg","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid
