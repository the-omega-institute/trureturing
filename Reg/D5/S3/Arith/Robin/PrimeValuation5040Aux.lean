import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PrimeValuation5040Bridge
import Reg.Support.DependentFamily

/-! Source-bound registrations for the two restored 5040 divisibility facts. -/

open _root_.D5.S3.Arith.Robin.PrimeValuation5040Bridge
open _root_.D5.S3.Factorization.PrimePowers.FiniteCrtJoin
open _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PrimeValuation5040Aux

namespace JointFiberBlockDvd

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
  realize signature (fun _ _ b => if b then False else
    ∀ {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℕ) {W n : ℕ},
      jointFiber S a W n → primePowerProduct S a ∣ n) anchorFn

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) anchorFn

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () false

private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]

def registration : Registration arena (type_of% @jointFiber_block_dvd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using @jointFiber_block_dvd,
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
    change (∀ {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℕ) {W n : ℕ},
      jointFiber S a W n → primePowerProduct S a ∣ n) ≠ False
    intro h
    have hp : (∀ {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℕ) {W n : ℕ},
      jointFiber S a W n → primePowerProduct S a ∣ n) := @jointFiber_block_dvd
    exact h ▸ hp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@jointFiber_block_dvd) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PrimeValuation5040Bridge.jointFiber_block_dvd.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeValuation5040Aux.JointFiberBlockDvd.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => if b then False else
    ∀ {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℕ) {W n : ℕ},
      jointFiber S a W n → primePowerProduct S a ∣ n) anchorFn)
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

end JointFiberBlockDvd

namespace JointFiber5040BlockDvd

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
  realize signature (fun _ _ b => if b then False else
    ∀ {W n : ℕ}, jointFiber primes5040 profile5040 W n → 5040 ∣ n) anchorFn

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) anchorFn

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () false

private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]

def registration : Registration arena (type_of% @jointFiber5040_block_dvd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using @jointFiber5040_block_dvd,
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
    change (∀ {W n : ℕ}, jointFiber primes5040 profile5040 W n → 5040 ∣ n) ≠ False
    intro h
    have hp : (∀ {W n : ℕ}, jointFiber primes5040 profile5040 W n → 5040 ∣ n) :=
      @jointFiber5040_block_dvd
    exact h ▸ hp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@jointFiber5040_block_dvd) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PrimeValuation5040Bridge.jointFiber5040_block_dvd.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeValuation5040Aux.JointFiber5040BlockDvd.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => if b then False else
    ∀ {W n : ℕ}, jointFiber primes5040 profile5040 W n → 5040 ∣ n) anchorFn)
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

end JointFiber5040BlockDvd

end Reg.D5.S3.Arith.Robin.PrimeValuation5040Aux

