import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.WuA227244ConjectureFour
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Primes.WuA227244ConjectureFour

namespace Reg.D5.S3.Arith.Primes.WuA227244ConjectureFour

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => 2 ^ (168 * n + 43)) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, n % 55 ≠ 26 →
    Nat.Prime 59 ∧
    (59 : ℤ) ∣ (((2 : ℤ) ^ r.readout () () n + 1) *
      2 ^ (2 ^ r.readout () () n) - 1) ∧
    ∀ q : ℕ, Nat.Prime q →
      (q : ℤ) ∣ (((2 : ℤ) ^ r.readout () () n + 1) *
        2 ^ (2 ^ r.readout () () n) - 1) → 59 ≤ q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd := (h 0 (by decide)).2.1
  norm_num [rejected, realize] at hd

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (2 : ℕ) ^ (168 * 0 + 43) ≠ 2 ^ (168 * 1 + 43)
    exact Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.Arith.Primes.WuA227244ConjectureFour.result)
    (type_of% (realize signature (fun _ _ n => 2 ^ (168 * n + 43)) (fun a => nomatch a)))
    Unit Unit := {
  unitName := `D5.S3.Arith.Primes.WuA227244ConjectureFour.result.__information_unit,
  realizationName := `Reg.D5.S3.Arith.Primes.WuA227244ConjectureFour.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => 2 ^ (168 * n + 43)) (fun a => nomatch a)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Arith.Primes.WuA227244ConjectureFour
