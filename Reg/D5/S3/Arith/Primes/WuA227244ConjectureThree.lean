import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.WuA227244ConjectureThree
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.WuA227244ConjectureThree
open _root_.D5.S3.Arith.Primes.WuA227244ConjectureThree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ n => ((2 : ℤ) ^ (2 ^ (72*n+32)) + 1) *
    2 ^ (2 ^ (2 ^ (72*n+32))) - 1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    (¬ ∃ k : ℕ, 72*n+32 = 20*k+16) →
    (¬ ∃ k : ℕ, 72*n+32 = 220*k+8) →
    Nat.Prime 149 ∧ (149 : ℤ) ∣ r.readout () () n ∧
    ∀ q : ℕ, Nat.Prime q → (q : ℤ) ∣ r.readout () () n → 149 ≤ q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0 (by omega) (by omega)
  have hbad := hzero.2.2 2 (by norm_num) (by simp [rejected, realize])
  norm_num at hbad

def family : Registration arena (∀ n : ℕ,
  (¬ ∃ k : ℕ, 72*n+32 = 20*k+16) →
  (¬ ∃ k : ℕ, 72*n+32 = 220*k+8) →
  Nat.Prime 149 ∧
  (149 : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (72*n+32)) + 1) *
    2 ^ (2 ^ (2 ^ (72*n+32))) - 1) ∧
  ∀ q : ℕ, Nat.Prime q →
    (q : ℤ) ∣ (((2 : ℤ) ^ (2 ^ (72*n+32)) + 1) *
      2 ^ (2 ^ (2 ^ (72*n+32))) - 1) → 149 ≤ q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change G 32 ≠ G 104
    apply ne_of_lt
    dsimp [G]
    gcongr <;> norm_num

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.Primes.WuA227244ConjectureThree.result)
      (type_of% (realize signature actual.readout actual.anchor)) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Arith.Primes.WuA227244ConjectureThree.unit,
  realizationName := `Reg.D5.S3.Arith.Primes.WuA227244ConjectureThree.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some ℕ,
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.WuA227244ConjectureThree,
    definition := none, coordinates := #[],
    readouts := #[
      { path := #["body", "body", "body", "arg", "fn", "arg", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "arg", "body", "body", "body", "domain", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end Reg.D5.S3.Arith.Primes.WuA227244ConjectureThree
