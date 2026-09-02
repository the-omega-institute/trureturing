/- GID: D5/S3/ObserverMemory/FourierFibers/ThreeLayerTimeSeparation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/ThreeLayerTimeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A reversible three-mode system separates dynamical iteration, first pairwise visibility, and full observation depth. -/

import D5.S3.CompletionDynamics.ObserverJet.FirstBreakOrder
import D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
import Mathlib.Tactic

/-!
The repository already owns the three ingredients separately: function
iteration, canonical finite future words, and a totalized first-break order.
This module introduces no competing time API. It supplies one finite spectral
witness in which the notions have different values.

The one-step modal update is reversible. Two states have the same static scalar
readout and first separate at positive time one. Yet the whole three-mode state
space is not reconstructed by observations through time one; observations
through time two are injective by the frozen Vandermonde theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.ThreeLayerTimeSeparation

open D5.S3.CompletionDynamics.ObserverJet.FirstBreakOrder
open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport
open D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge

/-- Three distinct nonzero modal multipliers. -/
def threeModes : Fin 3 → ℚ := ![1, 2, 3]

/-- A state supported on the first mode. -/
def firstModeState : Fin 3 → ℚ := ![1, 0, 0]

/-- A state supported on the second mode. -/
def secondModeState : Fin 3 → ℚ := ![0, 1, 0]

/-- A nonzero state invisible through times zero and one. -/
def depthOneHiddenState : Fin 3 → ℚ := ![1, -2, 1]

/-- The selected three modes are pairwise distinct. -/
theorem three_modes_injective : Function.Injective threeModes := by
  intro left right h
  fin_cases left <;> fin_cases right <;>
    simp [threeModes] at h ⊢

/-- Diagonal evolution by the three nonzero modes is reversible. -/
theorem three_mode_update_bijective :
    Function.Bijective (oneStepSpectralUpdate threeModes) := by
  constructor
  · intro left right h
    funext mode
    have hmode := congrFun h mode
    fin_cases mode <;>
      norm_num [oneStepSpectralUpdate, spectralFiberTransport, threeModes]
        at hmode ⊢ <;>
      linarith
  · intro target
    refine ⟨fun mode => target mode / threeModes mode, ?_⟩
    funext mode
    fin_cases mode <;>
      norm_num [oneStepSpectralUpdate, spectralFiberTransport, threeModes]

/-- The two selected hidden states collide under the static scalar readout. -/
theorem selected_states_static_collision :
    crystalTimeSample threeModes firstModeState 0 =
      crystalTimeSample threeModes secondModeState 0 := by
  native_decide

/-- Pairwise visibility predicate for the selected hidden states. -/
def selectedStatesBreakAt (time : ℕ) : Prop :=
  crystalTimeSample threeModes firstModeState time ≠
    crystalTimeSample threeModes secondModeState time

/-- The selected pair enters the visible channel after one update. -/
theorem selected_states_break_at_one : selectedStatesBreakAt 1 := by
  native_decide

/-- The pair-specific break time is exactly one. -/
theorem selected_states_first_break_order :
    firstBreakOrder selectedStatesBreakAt = (1 : WithTop ℕ) :=
  first_order_break_characterization selected_states_break_at_one

/-- The nonzero Vandermonde-kernel witness is invisible through times zero and
one, so the depth-one joint observation is not faithful on all amplitudes. -/
theorem depth_one_crystal_word_not_injective :
    ¬Function.Injective (crystalTimeWord threeModes 1) := by
  intro hinjective
  have hword :
      crystalTimeWord threeModes 1 depthOneHiddenState =
        crystalTimeWord threeModes 1 (fun _ => 0) := by
    funext time
    fin_cases time <;> native_decide
  have hstate := hinjective hword
  have hfirst := congrFun hstate 0
  norm_num [depthOneHiddenState] at hfirst

/-- Adding the time-two coordinate makes the complete three-mode observation
faithful. -/
theorem depth_two_crystal_word_injective :
    Function.Injective (crystalTimeWord threeModes 2) := by
  simpa only [crystalTimeWord, firstCrystalTimeWindow] using
    (first_crystal_time_window_injective three_modes_injective)

/-- In one concrete system, reversible dynamical iteration, pairwise first
visibility, and full observation depth are genuinely different notions. -/
theorem three_layer_time_separation :
    Function.Bijective (oneStepSpectralUpdate threeModes) ∧
    crystalTimeSample threeModes firstModeState 0 =
      crystalTimeSample threeModes secondModeState 0 ∧
    firstBreakOrder selectedStatesBreakAt = (1 : WithTop ℕ) ∧
    ¬Function.Injective (crystalTimeWord threeModes 1) ∧
    Function.Injective (crystalTimeWord threeModes 2) :=
  ⟨three_mode_update_bijective,
    selected_states_static_collision,
    selected_states_first_break_order,
    depth_one_crystal_word_not_injective,
    depth_two_crystal_word_injective⟩

#print axioms three_modes_injective
#print axioms three_mode_update_bijective
#print axioms selected_states_first_break_order
#print axioms depth_one_crystal_word_not_injective
#print axioms depth_two_crystal_word_injective
#print axioms three_layer_time_separation

end D5.S3.ObserverMemory.FourierFibers.ThreeLayerTimeSeparation
