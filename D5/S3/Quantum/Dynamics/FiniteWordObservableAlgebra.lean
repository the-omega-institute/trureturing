/- GID: D5/S3/Quantum/Dynamics/FiniteWordObservableAlgebra
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FiniteWordObservableAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite pullback algebras are exactly functions on realized readout words. -/

import D5.S3.Quantum.Dynamics.LeastInvariantObservableAlgebra

/- Library-search audit trail (2026-08-25):
   * Repository searches for finite word algebras, fiber-constant complex
     functions, and algebra dimensions found no public theorem with all three clauses.
   * Exact family hits `finiteObservableAlgebraEquiv`, `finiteWordRangeEquiv`,
     `finiteKoopmanClosure`, and `futureReadoutWord` are imported and reused.
   * The prescribed body-shape search for a composition of those two equivalences
     missed, so the named canonical composition below is new rather than a fork.
   * Pinned Mathlib has no finite-word observable-algebra theorem. Exact component
     hits `StarAlgebra.adjoin_le`, `Quotient.lift`, `LinearEquiv.finrank_eq`, and
     `Module.finrank_pi_fintype` are applied directly. Loogle and LeanSearch are
     unavailable on PATH. -/

noncomputable section

namespace D5.S3.Quantum.Dynamics.FiniteWordObservableAlgebra

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift
open D5.S3.Quantum.Dynamics.LeastInvariantObservableAlgebra
open D5.S3.QuantumStates.ObservableAlgebraClosureDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The canonical equivalence from the bounded pullback algebra to complex
functions on the realized finite readout words. -/
def finiteWordObservableAlgebraEquiv
    {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    finiteKoopmanClosure update readout depth ≃⋆ₐ[ℂ]
      (Set.range (futureReadoutWord update readout depth) -> ℂ) :=
  (finiteObservableAlgebraEquiv update readout hreadout depth).trans
    (functionAlgebraEquiv (finiteWordRangeEquiv update readout depth))

/-- The bounded pullback algebra consists exactly of functions constant on
finite-word fibers. Its canonical word-function equivalence evaluates on every
realized word by choosing any representative, and its dimension is the number
of realized words. -/
theorem finite_word_observable_algebra
    {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    finiteKoopmanClosure update readout depth =
        fiberStarAlgebra (Setoid.ker (futureReadoutWord update readout depth)) /\
      (forall (f : finiteKoopmanClosure update readout depth) (y : Y),
        finiteWordObservableAlgebraEquiv update readout hreadout depth f
            ⟨futureReadoutWord update readout depth y, ⟨y, rfl⟩⟩ = f.1 y) /\
      Module.finrank ℂ (finiteKoopmanClosure update readout depth) =
        Nat.card (Set.range (futureReadoutWord update readout depth)) := by
  have halgebra : finiteKoopmanClosure update readout depth =
      fiberStarAlgebra (Setoid.ker (futureReadoutWord update readout depth)) := by
    apply le_antisymm
    · apply StarAlgebra.adjoin_le
      rintro f ⟨n, hn, g, ⟨source, rfl⟩, rfl⟩ first second hsame
      have hcoordinate := congrFun hsame
        (show Fin (depth + 1) from ⟨n, Nat.lt_succ_of_le hn⟩)
      exact congrArg source hcoordinate
    · intro f hf
      let target : PredictionState update readout depth -> ℂ :=
        Quotient.lift f (by
          intro first second hsame
          exact hf hsame)
      let lifted :=
        (finiteObservableAlgebraEquiv update readout hreadout depth).symm target
      have hlifted : lifted.1 = f := by
        funext y
        have heq := congrFun
          ((finiteObservableAlgebraEquiv update readout hreadout depth).apply_symm_apply target)
          (Quotient.mk _ y)
        calc
          lifted.1 y =
              (finiteObservableAlgebraEquiv update readout hreadout depth lifted)
                (Quotient.mk _ y) := rfl
          _ = target (Quotient.mk _ y) := heq
          _ = f y := rfl
      rw [← hlifted]
      exact lifted.property
  refine ⟨halgebra, ?_, ?_⟩
  · intro f y
    change
      (finiteObservableAlgebraEquiv update readout hreadout depth f)
          ((finiteWordRangeEquiv update readout depth).symm
            ⟨futureReadoutWord update readout depth y, ⟨y, rfl⟩⟩) = f.1 y
    have hrange :
        (finiteWordRangeEquiv update readout depth).symm
            ⟨futureReadoutWord update readout depth y, ⟨y, rfl⟩⟩ =
          (Quotient.mk _ y : PredictionState update readout depth) := by
      apply (finiteWordRangeEquiv update readout depth).injective
      rw [(finiteWordRangeEquiv update readout depth).apply_symm_apply]
      apply Subtype.ext
      rfl
    rw [hrange]
    rfl
  · letI : Fintype (Set.range (futureReadoutWord update readout depth)) :=
      Fintype.ofFinite _
    calc
      Module.finrank ℂ (finiteKoopmanClosure update readout depth) =
          Module.finrank ℂ
            (Set.range (futureReadoutWord update readout depth) -> ℂ) :=
        LinearEquiv.finrank_eq
          (finiteWordObservableAlgebraEquiv update readout hreadout depth).toAlgEquiv.toLinearEquiv
      _ = Fintype.card (Set.range (futureReadoutWord update readout depth)) := by
        simp
      _ = Nat.card (Set.range (futureReadoutWord update readout depth)) :=
        Nat.card_eq_fintype_card.symm

#print axioms finite_word_observable_algebra

end D5.S3.Quantum.Dynamics.FiniteWordObservableAlgebra
