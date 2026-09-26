import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.slopeArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law,
      statementIdentity := "sha256:cd8771064a2ef41ff0a64b8419849ed8b69981f7bf5a40ebfe2d070a43075b25",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.slopeArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law,
      statementIdentity := "sha256:cd8771064a2ef41ff0a64b8419849ed8b69981f7bf5a40ebfe2d070a43075b25",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity

open Set MeasureTheory
open LeanInformationAudit
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq SlopeOutput := Classical.decEq _

def slopeClaim : Prop :=
  ∀ (alpha : ℝ), Irrational alpha → 0 < alpha → alpha < 1 → ∀ (n : ℕ),
    ∃ radius : ℝ, 0 < radius ∧ alpha + radius < 1 ∧
      (∀ lower : ℝ, lower ≤ 1 - alpha →
        (∀ i : Fin n, lower ≤
          1 - Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha)) →
        (∀ i j : Fin n, i ≠ j → lower ≤
          |Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) -
            Int.fract (((j.val + 1 : ℕ) : ℝ) * alpha)|) →
        lower / (2 * ((n : ℝ) + 1)) ≤ radius) ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ radius →
      let c : Fin n → ℝ := fun i =>
        1 - Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha)
      let swept : Fin n → Set ℝ := fun i =>
        Ico (c i - ((i.val + 1 : ℕ) : ℝ) * delta) (c i)
      slopeDisagreement alpha (alpha + delta) n = ⋃ i, swept i ∧
      Pairwise (fun i j => Disjoint (swept i) (swept j)) ∧
      volume (slopeDisagreement alpha (alpha + delta) n) =
        ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) / 2 * delta) ∧
      ∀ i x, x ∈ swept i → ∀ j : Fin n,
        lowerMechanicalLetter (alpha + delta) x j.val -
          lowerMechanicalLetter alpha x j.val =
          (if j.val = i.val then (1 : ℤ) else 0) -
            (if j.val = i.val + 1 then (1 : ℤ) else 0)

theorem slopeBridge : LegacyPrimitiveRealization slopeArena.toPrimitiveLawArena
    slopeClaim slopeRealization := by
  constructor
  exact Iff.rfl

def slopeBad : PrimitiveRealization slopeArena.signature :=
  @mechanicalReadoutRealization SlopeOutput (Classical.decEq _)
    (fun _ : Unit => fun _ _ _ => (Set.univ : Set ℝ))

private theorem slopeBad_not_law : ¬ slopeArena.Law slopeBad := by
  intro h
  have hIrr : Irrational (Real.sqrt 2 / 2) :=
    irrational_sqrt_two.div_natCast (by norm_num : (2 : ℕ) ≠ 0)
  have hPos : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hLt : Real.sqrt 2 / 2 < (1 : ℝ) := by
    have hs := Real.sqrt_nonneg (2 : ℝ)
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  obtain ⟨radius, hr, _, _, hmain⟩ := h (Real.sqrt 2 / 2) hIrr hPos hLt 0
  have hset := (hmain 0 (by norm_num) hr.le).1
  simp [slopeBad, mechanicalReadoutRealization] at hset

theorem slopeVariation : slopeArena.Law slopeRealization ∧
    ¬ slopeArena.Law slopeBad := by
  exact ⟨slopeBridge.equivalence.mp
    (fun alpha halpha h0 h1 n =>
      local_slope_disagreement_law alpha halpha h0 h1 n),
    slopeBad_not_law⟩

theorem slopeSensitivity : FiniteSlotSensitivity slopeArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨slopeRealization, slopeBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => slopeBad_not_law, fun _ => slopeVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law
  in slopeArena
  readout via (@mechanicalReadoutRealization SlopeOutput (Classical.decEq _)
    (fun _ : Unit => slopeReadout))
  primitives slopeRealization.toPrimitiveBundle
  realization slopeBridge
  variation slopeVariation sensitivity slopeSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law
  unless row.any (fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false) do
    throwError "slope-sensitivity information registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
