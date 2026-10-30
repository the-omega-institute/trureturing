import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PrimeValuation5040Bridge
import Reg.Support.DependentFamily

/-! Source-bound audit for the exact 5040 valuation fibre. -/

namespace Reg.D5.S3.Arith.Robin.PrimeValuation5040Bridge

open _root_.D5.S3.Arith.Robin.PrimeValuation5040Bridge
open _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def anchorFn : ∀ (_ : signature.Anchor) p, signature.State p :=
  fun e => nomatch e

def actual : Realization signature :=
  realize signature
    (fun _ _ b => if b then False else
      ∀ {W n : ℕ}, (∀ p ∈ primes5040, p.Coprime W) →
        (jointFiber primes5040 profile5040 W (5040 * n) ↔
          n ≠ 0 ∧ n.Coprime (W * 210)))
    anchorFn

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () false

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) anchorFn

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [arena, rejected, realize] using h

def registration : Registration arena (type_of% @jointFiber5040_mul_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using @jointFiber5040_mul_iff,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), false, true, ?_⟩
    change (∀ {W n : ℕ}, (∀ p ∈ primes5040, p.Coprime W) →
      (jointFiber primes5040 profile5040 W (5040 * n) ↔
        n ≠ 0 ∧ n.Coprime (W * 210))) ≠ False
    intro h
    have hp : (∀ {W n : ℕ}, (∀ p ∈ primes5040, p.Coprime W) →
      (jointFiber primes5040 profile5040 W (5040 * n) ↔
        n ≠ 0 ∧ n.Coprime (W * 210))) := @jointFiber5040_mul_iff
    exact h ▸ hp

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@jointFiber5040_mul_iff) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PrimeValuation5040Bridge.jointFiber5040_mul_iff.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeValuation5040Bridge.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ b => if b then False else
      ∀ {W n : ℕ}, (∀ p ∈ primes5040, p.Coprime W) →
        (jointFiber primes5040 profile5040 W (5040 * n) ↔
          n ≠ 0 ∧ n.Coprime (W * 210)))
    anchorFn)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.PrimeValuation5040Bridge
