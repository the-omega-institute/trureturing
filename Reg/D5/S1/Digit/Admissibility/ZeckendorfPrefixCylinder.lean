import D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder
open _root_.D5.S1.Words
open _root_.D5.S1.Words.Powers

namespace Reg.D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder

noncomputable section

abbrev signature : Signature where
  Params := Σ _m : Nat, Nat
  State := fun p => Fin p.1 → Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p w => prefixValue w + (goldenSubstStart^[prefixHeight w]) p.2)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} (t : Nat) (w : Fin m → Fin 2), legalPrefix w →
    prefixCylinder w (R.readout () ⟨m, t⟩ w)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let one : Fin 1 → Fin 2 := fun _ => 1
  have hlegal : legalPrefix one := by
    intro i
    exact Fin.elim0 i
  have hbad := h 0 one hlegal ⟨0, by decide⟩
  have hz : D5.S1.Digit.GoldenBase4AutomataOracle.zeckendorfBit 0 0 = 0 := by
    simp [D5.S1.Digit.GoldenBase4AutomataOracle.zeckendorfBit,
      D5.S0.Conventions.wdigits]
  simp [rejected, realize, one, hz] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro m t w hw
    exact prefixCylinder_of_shift t w hw
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let zero : Fin 1 → Fin 2 := fun _ => 0
    let one : Fin 1 → Fin 2 := fun _ => 1
    refine ⟨⟨1, 0⟩, zero, one, ?_⟩
    change prefixValue zero + (goldenSubstStart^[prefixHeight zero]) 0 ≠
      prefixValue one + (goldenSubstStart^[prefixHeight one]) 0
    have hzero (k : Nat) : (goldenSubstStart^[k]) 0 = 0 := by
      induction k with
      | zero => rfl
      | succ k ih => simpa [Function.iterate_succ_apply', ih, goldenSubstStart_zero]
    simp [hzero, prefixValue, zero, one]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder
  coordinates := #[0, 1]
  readouts := #[{path := #["body", "body", "body", "body", "arg"], stateBinder := 2}] }

register_information_theorem prefixCylinder_of_shift in arena
  readout via (realize signature
    (fun _ p w => prefixValue w + (goldenSubstStart^[prefixHeight w]) p.2)
    (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

open Lean in
run_meta do
  let target := `D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder.prefixCylinder_of_shift
  let some event := (LeanInformationAudit.TemplateBinding.inventory (← getEnv)).find?
      (·.key.theoremName == target) | throwError "original occurrence absent"
  let some (_, claim) := (LeanInformationAudit.TemplateBinding.ownedClaims (← getEnv)).find?
      (·.2.key == event.key) | throwError "original claim absent"
  let record ← LeanInformationAudit.TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "registration failed: {(← LeanInformationAudit.TemplateBinding.recordJson record).compress}"
  unless record.escape.fromObject.isSome && record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "four slots incomplete"
  logInfo m!"declared_validated {cert.evidenceRef}"

#print axioms registration

end
end Reg.D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder
