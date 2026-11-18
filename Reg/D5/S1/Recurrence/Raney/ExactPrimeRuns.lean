import D5.S1.Recurrence.Raney.ExactPrimeRuns
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Full original-telescope source-family audit for the exact prime R31 spectrum. -/

namespace Reg.D5.S1.Recurrence.Raney.ExactPrimeRuns

open TrureTuring.Raney TrureTuring.Raney.ExactPrime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun p => ZMod p)

def actual : Realization signature :=
  realize signature (fun _ p n => (raneyNumber 3 1 n : ZMod p)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) (_hp : p.Prime) (_hp5 : 5 ≤ p),
    (∀ m : ℕ, 1 ≤ m → ∀ j : ℕ, (j = 1 ∨ j = 2) →
      let q := p ^ m
      let a := (j * q + 2) / 3
      let b := if j = 1 then (q - 3) / 2 else q - 1
      (a ≤ b ↔ j = 2 ∨ (q ≠ 5 ∧ q ≠ 7)) ∧
      b + 1 - a =
        (if j = 1 then (if q % 6 = 1 then (q - 7) / 6 else (q - 5) / 6) else q / 3) ∧
      (a ≤ b →
        IsMaximalDeltaInterval {0} (R.readout () p) a b ∧
        ∀ c d : ℕ,
          IsMaximalDeltaInterval {0} (R.readout () p) c d →
          c < a → d + 1 - c < b + 1 - a)) ∧
    (∀ a b : ℕ,
      IsMaximalDeltaInterval {0} (R.readout () p) a b →
      ∃ m j : ℕ, 1 ≤ m ∧ (j = 1 ∨ j = 2) ∧
        let q := p ^ m
        let c := (j * q + 2) / 3
        let d := if j = 1 then (q - 3) / 2 else q - 1
        c ≤ d ∧ b + 1 - a = d + 1 - c) ∧
    (∀ m h j k : ℕ, 1 ≤ m → 1 ≤ h → (j = 1 ∨ j = 2) → (k = 1 ∨ k = 2) →
      (m < h ∨ (m = h ∧ j < k)) →
      (if j = 1 then (p ^ m - 3) / 2 else p ^ m - 1) + 1 - (j * p ^ m + 2) / 3 <
        (if k = 1 then (p ^ h - 3) / 2 else p ^ h - 1) + 1 - (k * p ^ h + 2) / 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hSpec := (h 5 Nat.prime_five (by decide)).1 1 (by decide) 2 (Or.inr rfl)
  have hMax := (hSpec.2.2 (by decide)).1
  have hz := hMax.2.1 4 (by decide) (by decide)
  change (1 : ZMod 5) ∈ ({0} : Finset (ZMod 5)) at hz
  simp only [Finset.mem_singleton] at hz
  exact (by decide : (1 : ZMod 5) ≠ 0) hz

def family : Registration arena (type_of% @raney_prime_ge_five_spectrum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨raney_prime_ge_five_spectrum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨5, 0, 4, ?_⟩
    change (raneyNumber 3 1 0 : ZMod 5) ≠ (raneyNumber 3 1 4 : ZMod 5)
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@raney_prime_ge_five_spectrum) (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Raney.ExactPrimeRuns.raney_prime_ge_five_spectrum.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Raney.ExactPrimeRuns.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => (raneyNumber 3 1 n : ZMod p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Raney.ExactPrimeRuns
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg",
        "body", "fn", "arg", "fn", "fn", "arg"],
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "fn", "arg", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg",
        "body", "arg", "body", "body", "domain", "fn", "fn",
        "arg"],
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "fn", "arg", "body",
        "body", "domain", "fn", "fn", "arg"],
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Raney.ExactPrimeRuns
