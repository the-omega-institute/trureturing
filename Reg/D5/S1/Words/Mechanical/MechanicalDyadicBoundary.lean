import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S1.Words.Mechanical.MechanicalDyadicBoundary
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
import Reg.Support.MechanicalDyadicRegistration



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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq) (type_of% (upperArena)) (type_of% (upperArena)) (type_of% (@mechanicalReadoutRealization UpperOutput (Classical.decEq.{1} _)
    (fun _ : Unit => upperReadout))) (type_of% (upperVariation)) (type_of% (upperSensitivity)) (type_of% (ℝ)) (Unit) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.upperBridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(upperArena)⟩,
  objectArena := ⟨(upperArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.upperArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.upperRealization) (upperRealization.toPrimitiveBundle) ⟨(upperBridge)⟩,
  readout := some (@mechanicalReadoutRealization UpperOutput (Classical.decEq.{1} _)
    (fun _ : Unit => upperReadout)),
  variation := some ⟨(upperVariation)⟩,
  sensitivity := some ⟨(upperSensitivity)⟩,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits) (type_of% (stableArena)) (type_of% (stableArena)) (type_of% (@mechanicalReadoutRealization StableOutput (Classical.decEq.{1} _)
    (fun _ : Unit => stableReadout))) (type_of% (stableVariation)) (type_of% (stableSensitivity)) (type_of% (ℝ)) (Unit) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.stableBridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(stableArena)⟩,
  objectArena := ⟨(stableArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.stableArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.stableRealization) (stableRealization.toPrimitiveBundle) ⟨(stableBridge)⟩,
  readout := some (@mechanicalReadoutRealization StableOutput (Classical.decEq.{1} _)
    (fun _ : Unit => stableReadout)),
  variation := some ⟨(stableVariation)⟩,
  sensitivity := some ⟨(stableSensitivity)⟩,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
