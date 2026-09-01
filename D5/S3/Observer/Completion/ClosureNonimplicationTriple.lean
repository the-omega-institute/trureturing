/- GID: D5/S3/Observer/Completion/ClosureNonimplicationTriple
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/ClosureNonimplicationTriple
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three concrete observers separate four closure notions. -/

import D5.S3.Observer.WindowAlgebra.OperationalClassicalSeparation
import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
import D5.S3.Quantum.Algebra.CovariantCommutator
import D5.S3.Quantum.Measurements.DeterministicReadoutPvm
import D5.S3.Quantum.Tomography.ObserverDiagonalSeparation

/- Library-search audit trail (2026-09-02):
   * D5 searches for constant-readout prediction closure, operational full-matrix
     generation, character exclusion, tomography, and diagonal escape found the
     exact component owners imported above, but no theorem containing all three
     nonimplications.
   * `predictionStableAt`, `deterministicProjection`, `shiftMatrix`,
     `windowGeneratedAlgebra`, and `contextReadout` are the canonical source
     primitives; no replacement definition is introduced here.
   * Pinned Mathlib has no observer-completion theorem. Its exact generic hit
     `Algebra.commute_of_mem_adjoin_of_forall_mem_commute` proves that the
     constant-readout operational algebra commutes with the cyclic shift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Completion.ClosureNonimplicationTriple

open D5.S3.Observer.WindowAlgebra.OperationalClassicalSeparation
open D5.S3.Observer.WindowAlgebra.WindowGeneration
open D5.S3.Observer.WindowRegister
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape
open D5.S3.Quantum.Algebra.CovariantCommutator
open D5.S3.Quantum.Measurements.DeterministicReadoutPvm
open D5.S3.Quantum.Tomography.ObserverDiagonalSeparation
open D5.S3.Quantum.Tomography.RankOneContextCommutator

/-- Three concrete countermodels separate prediction closure from operational
algebra completeness, operational algebra completeness from classical character
completeness, and tomography from same-level self-description. -/
theorem closure_nonimplication_triple :
    (predictionStableAt
        (fun state : ZMod 2 => state - 1)
        (fun _ : ZMod 2 => ()) 0 ∧
      Algebra.adjoin ℂ
        ({deterministicProjection (fun _ : ZMod 2 => ()) (), shiftMatrix 2} :
          Set (Matrix (ZMod 2) (ZMod 2) ℂ)) ≠ ⊤) ∧
    (windowGeneratedAlgebra 2 = ⊤ ∧
      IsEmpty (windowGeneratedAlgebra 2 →ₐ[ℂ] ℂ)) ∧
    ∃ context : Fin 2 -> RankOneContext 1,
      Function.Injective (contextReadout context) ∧
      ∃ (evaluation : Matrix (Fin 1) (Fin 1) ℂ ->
          Matrix (Fin 1) (Fin 1) ℂ -> Bool)
        (twist : Bool -> Bool),
        (∀ y, twist y ≠ y) ∧
          (fun a => twist (evaluation a a)) ∉ Set.range evaluation := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro first second _
      rfl
    · intro htop
      have hclock : clockMatrix 2 ∈
          Algebra.adjoin ℂ
            ({deterministicProjection (fun _ : ZMod 2 => ()) (), shiftMatrix 2} :
              Set (Matrix (ZMod 2) (ZMod 2) ℂ)) := by
        rw [htop]
        trivial
      have hcommute : Commute (shiftMatrix 2) (clockMatrix 2) :=
        Algebra.commute_of_mem_adjoin_of_forall_mem_commute hclock (by
          intro generator hgenerator
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgenerator
          rcases hgenerator with hprojection | hshift
          · subst generator
            simp [deterministicProjection]
          · subst generator
            exact Commute.refl _)
      apply window_two_commutator_ne_zero
      exact sub_eq_zero.mpr hcommute.eq.symm
  · have fullWindow := operational_complete_not_classically_complete 2 (by norm_num)
    exact ⟨fullWindow.1, fullWindow.2.2.1⟩
  · obtain ⟨context, _, injective, _, _, _, _⟩ :=
      empirical_observer_diagonal_separation
    refine ⟨context, injective, fun _ _ => true, fun value => !value, by decide, ?_⟩
    change IsEscaped (fun value : Bool => !value)
      (fun _ _ : Matrix (Fin 1) (Fin 1) ℂ => true)
    exact escaped_of_fixedPointFree (fun value : Bool => !value) (by decide)
      (fun _ _ : Matrix (Fin 1) (Fin 1) ℂ => true)

#print axioms closure_nonimplication_triple

end D5.S3.Observer.Completion.ClosureNonimplicationTriple
