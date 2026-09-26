import LeanInformationAudit.Syntax
import D5.S1.Words.Mechanical.MechanicalDyadicBoundary
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
import Reg.Support.MechanicalDyadicRegistration

open Lean Elab Command LeanInformationAudit

run_cmd do
  let root := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
  let owner := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary
  let source := (← getEnv)
  let rows : Array SnapshotOccurrence := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.lowerArena,
      theoremName := owner ++ `dyadic_lower_boundary_mismatch,
      statementIdentity := theoremStatementIdentity source (owner ++ `dyadic_lower_boundary_mismatch),
      registrationModuleName := root },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.upperArena,
      theoremName := owner ++ `dyadic_upper_eventually_word_eq,
      statementIdentity := theoremStatementIdentity source (owner ++ `dyadic_upper_eventually_word_eq),
      registrationModuleName := root },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.stableArena,
      theoremName := owner ++ `finite_word_stable_off_integer_hits,
      statementIdentity := theoremStatementIdentity source (owner ++ `finite_word_stable_off_integer_hits),
      registrationModuleName := root }]
  RootCatalogs.declare {
    rootId := root
    expected := rows
    source := rows
    companionPrefix := some root }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary

open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalDyadicBoundary
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq LowerOutput := Classical.decEq _
local instance : DecidableEq UpperOutput := Classical.decEq _
local instance : DecidableEq StableOutput := Classical.decEq _

theorem lowerBridge : LegacyPrimitiveRealization lowerArena.toPrimitiveLawArena
    (∀ (alpha : ℝ), Irrational alpha → 0 < alpha → alpha < 1 → ∀ p : ℕ,
      0 ≤ dyadicLower alpha p ∧
      0 < alpha - dyadicLower alpha p ∧
      alpha - dyadicLower alpha p < (1 : ℝ) / ((2 ^ p : ℕ) : ℝ) ∧
      lowerMechanicalWord alpha (1 - alpha) 0 = true ∧
      lowerMechanicalWord (dyadicLower alpha p) (1 - alpha) 0 = false)
    lowerRealization := by
  constructor
  change (∀ (alpha : ℝ), Irrational alpha → 0 < alpha → alpha < 1 → ∀ p : ℕ,
      0 ≤ dyadicLower alpha p ∧
      0 < alpha - dyadicLower alpha p ∧
      alpha - dyadicLower alpha p < (1 : ℝ) / ((2 ^ p : ℕ) : ℝ) ∧
      lowerMechanicalWord alpha (1 - alpha) 0 = true ∧
      lowerMechanicalWord (dyadicLower alpha p) (1 - alpha) 0 = false) ↔
    (∀ (alpha : ℝ), Irrational alpha → 0 < alpha → alpha < 1 → ∀ p : ℕ,
      0 ≤ dyadicLower alpha p ∧
      0 < alpha - dyadicLower alpha p ∧
      alpha - dyadicLower alpha p < (1 : ℝ) / ((2 ^ p : ℕ) : ℝ) ∧
      lowerMechanicalWord alpha (1 - alpha) 0 = true ∧
      lowerMechanicalWord (dyadicLower alpha p) (1 - alpha) 0 = false)
  exact Iff.rfl

def lowerBad : PrimitiveRealization lowerArena.signature :=
  @mechanicalReadoutRealization LowerOutput (Classical.decEq _)
    (fun _ : Unit => fun _ _ => ((-1 : ℝ), true))

private theorem lowerBad_not_law : ¬ lowerArena.Law lowerBad := by
  intro h
  have hIrr : Irrational (Real.sqrt 2 / 2) :=
    irrational_sqrt_two.div_natCast (by norm_num : (2 : ℕ) ≠ 0)
  have hPos : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hLt : Real.sqrt 2 / 2 < (1 : ℝ) := by
    have hs := Real.sqrt_nonneg (2 : ℝ)
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hFirst := (h (Real.sqrt 2 / 2) hIrr hPos hLt 0).1
  norm_num [lowerBad, mechanicalReadoutRealization] at hFirst

theorem lowerVariation : lowerArena.Law lowerRealization ∧
    ¬ lowerArena.Law lowerBad := by
  exact ⟨lowerBridge.equivalence.mp
    (fun alpha hIrr hPos hLt p =>
      dyadic_lower_boundary_mismatch alpha hIrr hPos hLt p), lowerBad_not_law⟩

theorem lowerSensitivity : FiniteSlotSensitivity lowerArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨lowerRealization, lowerBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => lowerBad_not_law, fun _ => lowerVariation.1⟩
  · intro i
    exact Fin.elim0 i

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
  _root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch
  in lowerArena
  readout via (@mechanicalReadoutRealization LowerOutput (Classical.decEq _)
    (fun _ : Unit => lowerReadout))
  primitives lowerRealization.toPrimitiveBundle
  realization lowerBridge
  variation lowerVariation sensitivity lowerSensitivity
  escape from (ℝ) escape continues (open)

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
      `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch,
      `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq,
      `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "mechanical dyadic information registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
