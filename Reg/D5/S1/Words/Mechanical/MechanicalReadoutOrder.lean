import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.localOrderArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights,
      statementIdentity := "sha256:11aadd35f6b85336828d84b165fbeeaa864ee887c147903bedd58ba8f017e6fd",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.isometricArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion,
      statementIdentity := "sha256:89c5ad6ba8c8a28280ac3325089a6260e8d0a103e4225d75d42ff950c5e54762",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.localOrderArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights,
      statementIdentity := "sha256:11aadd35f6b85336828d84b165fbeeaa864ee887c147903bedd58ba8f017e6fd",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.isometricArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion,
      statementIdentity := "sha256:89c5ad6ba8c8a28280ac3325089a6260e8d0a103e4225d75d42ff950c5e54762",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder

open Set MeasureTheory
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : DecidableEq PrefixOutput := Classical.decEq _
local instance : DecidableEq CompletionOutput := Classical.decEq _

theorem orderBridge : LegacyPrimitiveRealization localOrderArena.toPrimitiveLawArena
    (localOrderClaim actualPrefix) localOrderRealization := ⟨Iff.rfl⟩

theorem isometricBridge : LegacyPrimitiveRealization isometricArena.toPrimitiveLawArena
    (isometricClaim actualCompletion) completionRealization := ⟨Iff.rfl⟩

def badPrefix : PrimitiveRealization localOrderArena.signature :=
  @mechanicalReadoutRealization PrefixOutput (Classical.decEq _)
    (fun _ : Unit => fun _ _ _ _ => (0 : ℝ))

def badCompletion : PrimitiveRealization isometricArena.signature :=
  @mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => ((fun _ _ _ => (0 : ℝ)), (fun _ _ _ _ => (0 : ℝ))))

theorem orderVariation : localOrderArena.Law localOrderRealization ∧
    ¬ localOrderArena.Law badPrefix := by
  constructor
  · apply orderBridge.equivalence.mp
    intro alpha halpha h0 h1 weights m
    exact local_order_iff_decreasing_weights alpha halpha h0 h1 weights m
  · intro h
    let alpha : ℝ := Real.sqrt 2 / 2
    have halpha : Irrational alpha :=
      irrational_sqrt_two.div_natCast (by norm_num : (2 : ℕ) ≠ 0)
    have h0 : 0 < alpha := by dsimp [alpha]; positivity
    have h1 : alpha < 1 := by
      dsimp [alpha]
      have hs := Real.sqrt_nonneg (2 : ℝ)
      have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    have hiff := h alpha halpha h0 h1 (fun _ : ℕ => (-1 : ℝ)) 0
    have hmono : ∃ radius : ℝ, 0 < radius ∧ alpha + radius < 1 ∧
        ∀ delta : ℝ, 0 ≤ delta → delta ≤ radius → ∀ x ∈ Ico (0 : ℝ) 1,
          badPrefix.readout () () (fun _ : ℕ => (-1 : ℝ)) alpha x (0 + 1) ≤
          badPrefix.readout () () (fun _ : ℕ => (-1 : ℝ)) (alpha + delta) x (0 + 1) := by
      refine ⟨(1 - alpha) / 2, by linarith, by linarith, ?_⟩
      intro delta _ _ x _
      norm_num [badPrefix, mechanicalReadoutRealization]
    have hweights := (hiff.mp hmono).1
    norm_num at hweights

theorem orderSensitivity : FiniteSlotSensitivity localOrderArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨localOrderRealization, badPrefix, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => orderVariation.2, fun _ => orderVariation.1⟩
  · intro i
    exact Fin.elim0 i

theorem isometricVariation : isometricArena.Law completionRealization ∧
    ¬ isometricArena.Law badCompletion := by
  constructor
  · apply isometricBridge.equivalence.mp
    intro r alpha beta hr0 hr1 ha hb
    exact geometric_readout_isometric_completion r alpha beta hr0 hr1 ha hb
  · intro h
    have hbad := (h 0 0 (1 / 2) (by norm_num) (by norm_num)
      (by norm_num [Set.mem_Ico]) (by norm_num [Set.mem_Ico])).2.2.2.1 1
    norm_num [badCompletion, mechanicalReadoutRealization] at hbad

theorem isometricSensitivity : FiniteSlotSensitivity isometricArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨completionRealization, badCompletion, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => isometricVariation.2, fun _ => isometricVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights
  in localOrderArena
  readout via (@mechanicalReadoutRealization PrefixOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.actualPrefix))
  primitives localOrderRealization.toPrimitiveBundle
  realization orderBridge
  variation orderVariation sensitivity orderSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion
  in isometricArena
  readout via (@mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion))
  primitives completionRealization.toPrimitiveBundle
  realization isometricBridge
  variation isometricVariation sensitivity isometricSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights,
      `D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "mechanical order registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder
