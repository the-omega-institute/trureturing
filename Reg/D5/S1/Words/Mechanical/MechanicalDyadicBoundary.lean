import LeanInformationAudit.Syntax
import D5.S1.Words.Mechanical.MechanicalDyadicBoundary
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.upperArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq,
      statementIdentity := "sha256:cd129c14a2561274769568cc1b202f52388daa5a0bade1344c03ab7761260418",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.stableArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits,
      statementIdentity := "sha256:a4092d2733c8819e7e7bae60e764686bbcbb4ab064a2adbcf8601fce8ed682ae",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.upperArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq,
      statementIdentity := "sha256:cd129c14a2561274769568cc1b202f52388daa5a0bade1344c03ab7761260418",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.stableArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits,
      statementIdentity := "sha256:a4092d2733c8819e7e7bae60e764686bbcbb4ab064a2adbcf8601fce8ed682ae",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary

open _root_.D5.S1.Words.Mechanical
open _root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq UpperOutput := Classical.decEq _
local instance : DecidableEq StableOutput := Classical.decEq _

theorem upperBridge : LegacyPrimitiveRealization upperArena.toPrimitiveLawArena
    (∀ (alpha x : ℝ) (n : ℕ), ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ j < n,
      lowerMechanicalWord (dyadicUpper alpha p) x j = lowerMechanicalWord alpha x j)
    upperRealization := by
  constructor
  change (∀ (alpha x : ℝ) (n : ℕ), ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ j < n,
      lowerMechanicalWord (dyadicUpper alpha p) x j = lowerMechanicalWord alpha x j) ↔
    (∀ (alpha x : ℝ) (n : ℕ), ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ j < n,
      lowerMechanicalWord (dyadicUpper alpha p) x j = lowerMechanicalWord alpha x j)
  exact Iff.rfl

def upperBad : PrimitiveRealization upperArena.signature :=
  @mechanicalReadoutRealization UpperOutput (Classical.decEq _)
    (fun _ : Unit => fun _ _ _ _ => true)

private theorem upperBad_not_law : ¬ upperArena.Law upperBad := by
  intro h
  obtain ⟨p₀, hp₀⟩ := h 0 0 1
  have hBit : lowerMechanicalWord (0 : ℝ) 0 0 = false := by
    norm_num [lowerMechanicalWord, lowerMechanicalLetter]
  have hFalse := hp₀ p₀ le_rfl 0 (by omega)
  simp [upperBad, mechanicalReadoutRealization, hBit] at hFalse

theorem upperVariation : upperArena.Law upperRealization ∧
    ¬ upperArena.Law upperBad := by
  exact ⟨upperBridge.equivalence.mp dyadic_upper_eventually_word_eq,
    upperBad_not_law⟩

theorem upperSensitivity : FiniteSlotSensitivity upperArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨upperRealization, upperBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => upperBad_not_law, fun _ => upperVariation.1⟩
  · intro i
    exact Fin.elim0 i

theorem stableBridge : LegacyPrimitiveRealization stableArena.toPrimitiveLawArena
    (∀ (alpha x : ℝ) (n : ℕ),
      (∀ k : ℕ, 0 < k → k ≤ n → ∀ z : ℤ, x + (k : ℝ) * alpha ≠ (z : ℝ)) →
      ∃ radius : ℝ, 0 < radius ∧ ∀ beta : ℝ, |beta - alpha| < radius →
        (∀ k ≤ n, ⌊x + (k : ℝ) * beta⌋ = ⌊x + (k : ℝ) * alpha⌋) ∧
        (∀ j < n, lowerMechanicalWord beta x j = lowerMechanicalWord alpha x j))
    stableRealization := by
  constructor
  change (∀ (alpha x : ℝ) (n : ℕ),
      (∀ k : ℕ, 0 < k → k ≤ n → ∀ z : ℤ, x + (k : ℝ) * alpha ≠ (z : ℝ)) →
      ∃ radius : ℝ, 0 < radius ∧ ∀ beta : ℝ, |beta - alpha| < radius →
        (∀ k ≤ n, ⌊x + (k : ℝ) * beta⌋ = ⌊x + (k : ℝ) * alpha⌋) ∧
        (∀ j < n, lowerMechanicalWord beta x j = lowerMechanicalWord alpha x j)) ↔
    (∀ (alpha x : ℝ) (n : ℕ),
      (∀ k : ℕ, 0 < k → k ≤ n → ∀ z : ℤ, x + (k : ℝ) * alpha ≠ (z : ℝ)) →
      ∃ radius : ℝ, 0 < radius ∧ ∀ beta : ℝ, |beta - alpha| < radius →
        (∀ k ≤ n, ⌊x + (k : ℝ) * beta⌋ = ⌊x + (k : ℝ) * alpha⌋) ∧
        (∀ j < n, lowerMechanicalWord beta x j = lowerMechanicalWord alpha x j))
  exact Iff.rfl

def stableBad : PrimitiveRealization stableArena.signature :=
  @mechanicalReadoutRealization StableOutput (Classical.decEq _)
    (fun _ : Unit => fun beta _ _ =>
      (if beta = 0 then (0 : ℤ) else 1, false))

private theorem stableBad_not_law : ¬ stableArena.Law stableBad := by
  intro h
  have hreg : ∀ k : ℕ, 0 < k → k ≤ 0 → ∀ z : ℤ,
      (0 : ℝ) + (k : ℝ) * 0 ≠ (z : ℝ) := by
    intro k hk hkn
    omega
  obtain ⟨radius, hr, hs⟩ := h 0 0 0 hreg
  let beta : ℝ := radius / 2
  have hb : |beta - (0 : ℝ)| < radius := by
    dsimp [beta]
    rw [sub_zero, abs_of_pos (by linarith)]
    linarith
  have hne : beta ≠ 0 := by
    dsimp [beta]
    linarith
  have hFloor := (hs beta hb).1 0 (by omega)
  simp [stableBad, mechanicalReadoutRealization, hne] at hFloor

theorem stableVariation : stableArena.Law stableRealization ∧
    ¬ stableArena.Law stableBad := by
  exact ⟨stableBridge.equivalence.mp finite_word_stable_off_integer_hits,
    stableBad_not_law⟩

theorem stableSensitivity : FiniteSlotSensitivity stableArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨stableRealization, stableBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => stableBad_not_law, fun _ => stableVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq
  in upperArena
  readout via (@mechanicalReadoutRealization UpperOutput (Classical.decEq _)
    (fun _ : Unit => upperReadout))
  primitives upperRealization.toPrimitiveBundle
  realization upperBridge
  variation upperVariation sensitivity upperSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits
  in stableArena
  readout via (@mechanicalReadoutRealization StableOutput (Classical.decEq _)
    (fun _ : Unit => stableReadout))
  primitives stableRealization.toPrimitiveBundle
  realization stableBridge
  variation stableVariation sensitivity stableSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq,
      `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "mechanical dyadic information registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
