import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.Permutations.FriedenAdaptedWords
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Powerset

open D5.S1.Words.Permutations.Frieden
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Permutations.FriedenAdaptedWords

abbrev signature := Reg.Support.SingleDependentReadout.signature Nat Word (fun _ => Bool)

private instance decidableAvoidsX {n : Nat} (w : Word n) : Decidable (AvoidsX w) :=
  inferInstanceAs (Decidable (∀ (S : Finset (Fin n)), S.card = 4 → restrict w S ∉ forbidden))

def actual : Realization signature :=
  realize signature (fun _ _ w => decide (AvoidsX w))
    (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

def forwardArena : Arena where
  signature := signature
  Law r := ∀ (n : Nat) (w : Word n), ReducedReversal w → r.readout () n w = true → Adapted w

def iffArena : Arena where
  signature := signature
  Law r := ∀ (n : Nat) (w : Word n), ReducedReversal w →
    (r.readout () n w = true ↔ Adapted w)

private def reentrantWord : Word 4 := [0, 1, 2, 1, 0, 1]

private theorem reentrantReduced : ReducedReversal reentrantWord := by
  constructor
  · decide
  · ext j
    fin_cases j <;> decide

private theorem reentrantHitsX : ¬ AvoidsX reentrantWord := by
  intro h
  exact h Finset.univ (by decide) (by decide)

private theorem reentrantNotAdapted : ¬ Adapted reentrantWord :=
  fun h => reentrantHitsX ((conjecture410 _ _ reentrantReduced).mpr h)

private theorem forwardErasedFails : ¬ forwardArena.Law erased :=
  fun h => reentrantNotAdapted (h _ reentrantWord reentrantReduced rfl)

private theorem iffErasedFails : ¬ iffArena.Law erased :=
  fun h => reentrantNotAdapted ((h _ reentrantWord reentrantReduced).mp rfl)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨4, [], reentrantWord, ?_⟩
  have hempty : AvoidsX ([] : Word 4) := by
    intro S _ hS
    change [] ∈ forbidden at hS
    exact (by decide : [] ∉ forbidden) hS
  change decide (AvoidsX ([] : Word 4)) ≠ decide (AvoidsX reentrantWord)
  simp [hempty, reentrantHitsX]

private theorem forwardBridge : (type_of% (@avoidance_implies_adapted)) ↔
    forwardArena.Law actual := by
  simp [forwardArena, actual, realize]

private theorem iffBridge : (type_of% (@conjecture410)) ↔ iffArena.Law actual := by
  simp [claim, iffArena, actual, realize]

noncomputable def forwardFamily :
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration
      forwardArena (type_of% (@avoidance_implies_adapted)) where
  actual := actual
  bridge := forwardBridge
  variation := ⟨forwardBridge.mp avoidance_implies_adapted, erased, forwardErasedFails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ forwardErasedFails
  dependence := dependence

noncomputable def iffFamily :
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration
      iffArena (type_of% (@conjecture410)) where
  actual := actual
  bridge := iffBridge
  variation := ⟨iffBridge.mp conjecture410, erased, iffErasedFails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ iffErasedFails
  dependence := dependence

noncomputable def avoidance_implies_adaptedRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S1.Words.Permutations.Frieden.avoidance_implies_adapted) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.Frieden.avoidance_implies_adapted.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.FriedenAdaptedWords.forwardFamily
  realizationSource := none
  generated := false
  arena := .source ⟨forwardArena⟩
  objectArena := .source ⟨forwardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source forwardArena ⟨forwardFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.FriedenAdaptedWords
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def conjecture410Registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S1.Words.Permutations.Frieden.conjecture410) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.Frieden.conjecture410.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.FriedenAdaptedWords.iffFamily
  realizationSource := none
  generated := false
  arena := .source ⟨iffArena⟩
  objectArena := .source ⟨iffArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source iffArena ⟨iffFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.FriedenAdaptedWords
    definition := some {
      owner := `D5.S1.Words.Permutations.FriedenAdaptedWords
      name := `D5.S1.Words.Permutations.Frieden.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Permutations.FriedenAdaptedWords
