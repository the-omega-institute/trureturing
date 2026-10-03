import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import Reg.Support.MechanicalDyadicRegistration



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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights) (type_of% (localOrderArena)) (type_of% (localOrderArena)) (type_of% (@mechanicalReadoutRealization PrefixOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualPrefix))) (type_of% (orderVariation)) (type_of% (orderSensitivity)) (type_of% (ℝ)) (Unit) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder.D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder.orderBridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(localOrderArena)⟩,
  objectArena := ⟨(localOrderArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.localOrderArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.localOrderRealization) (localOrderRealization.toPrimitiveBundle) ⟨(orderBridge)⟩,
  readout := some (@mechanicalReadoutRealization PrefixOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualPrefix)),
  variation := some ⟨(orderVariation)⟩,
  sensitivity := some ⟨(orderSensitivity)⟩,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion) (type_of% (isometricArena)) (type_of% (isometricArena)) (type_of% (@mechanicalReadoutRealization CompletionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion))) (type_of% (isometricVariation)) (type_of% (isometricSensitivity)) (type_of% (ℝ)) (Unit) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder.D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder.isometricBridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(isometricArena)⟩,
  objectArena := ⟨(isometricArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.isometricArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.completionRealization) (completionRealization.toPrimitiveBundle) ⟨(isometricBridge)⟩,
  readout := some (@mechanicalReadoutRealization CompletionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion)),
  variation := some ⟨(isometricVariation)⟩,
  sensitivity := some ⟨(isometricSensitivity)⟩,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder
