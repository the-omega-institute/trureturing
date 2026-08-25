/- GID: D5/S3/Observer/WindowAlgebra/OperationalClassicalSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/WindowAlgebra/OperationalClassicalSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full operations and tomography do not yield a multiplicative classical state. -/

import D5.S3.Observer.WindowAlgebra.WindowGeneration
import D5.S3.Observer.WindowCharacter
import D5.S3.QuantumStates.GNSStateCone
import D5.S3.QuantumStates.GNSZeroPropagation

/- Library-search audit trail (2026-08-25):
   * Exact repository components `window_generators_adjoin_top`,
     `window_commutant_eq_scalars`, `window_algebra_has_no_character`,
     `stateFunctional`, and `state_cone_sections` are imported and applied.
   * Pinned Mathlib exact supporting hits `Subalgebra.centralizer_univ`,
     `Subalgebra.equivOfEq`, `Subalgebra.topEquiv`, `Matrix.center_eq_range`,
     `Matrix.ext_iff_trace_mul_right`, `Matrix.diagonal_single`, and the
     matrix-unit multiplication and trace lemmas are applied directly.
   * Repository and pinned-Mathlib searches found no declaration combining
     operational generation, scalar commutant, character emptiness, state
     tomography, positive normalized linearity, and explicit failure of
     multiplicativity on the finite cyclic carrier. -/

noncomputable section

open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.WindowAlgebra.OperationalClassicalSeparation

open D5.S3.Observer.WindowAlgebra.WindowGeneration
open D5.S3.Observer.WindowCharacter
open D5.S3.Observer.WindowRegister
open D5.S3.QuantumStates.GNSStateCone
open D5.S3.QuantumStates.GNSZeroPropagation

private theorem generated_centralizer_eq_scalars (M : ℕ) [NeZero M] :
    (Subalgebra.centralizer ℂ
        (windowGeneratedAlgebra M :
          Set (Matrix (ZMod M) (ZMod M) ℂ)) :
      Set (Matrix (ZMod M) (ZMod M) ℂ)) =
      Set.range (Matrix.scalar (ZMod M)) := by
  have hFullCentralizer :
      (Subalgebra.centralizer ℂ
          (Set.univ : Set (Matrix (ZMod M) (ZMod M) ℂ)) :
        Set (Matrix (ZMod M) (ZMod M) ℂ)) =
        Set.range (Matrix.scalar (ZMod M)) := by
    rw [Subalgebra.centralizer_univ]
    change Set.center (Matrix (ZMod M) (ZMod M) ℂ) = _
    exact Matrix.center_eq_range ℂ
  apply Set.Subset.antisymm
  · intro A hA
    change ∀ B ∈ windowGeneratedAlgebra M, B * A = A * B at hA
    have hCommute (B : Matrix (ZMod M) (ZMod M) ℂ)
        (hB : B ∈ windowGeneratedAlgebra M) : Commute A B :=
      (hA B hB).symm
    apply window_commutant_eq_scalars A
    · apply hCommute
      exact Algebra.subset_adjoin (by simp)
    · apply hCommute
      exact Algebra.subset_adjoin (by simp)
  · intro A hA
    have hAFull : A ∈ (Subalgebra.centralizer ℂ
        (Set.univ : Set (Matrix (ZMod M) (ZMod M) ℂ)) :
          Set (Matrix (ZMod M) (ZMod M) ℂ)) := by
      rw [hFullCentralizer]
      exact hA
    change ∀ B ∈ (Set.univ : Set (Matrix (ZMod M) (ZMod M) ℂ)),
      B * A = A * B at hAFull
    change ∀ B ∈ windowGeneratedAlgebra M, B * A = A * B
    intro B _
    exact hAFull B (Set.mem_univ B)

private theorem generated_algebra_has_no_character
    (M : ℕ) [NeZero M] (hM : 1 < M) :
    IsEmpty (windowGeneratedAlgebra M →ₐ[ℂ] ℂ) := by
  let equivalence :
      windowGeneratedAlgebra M ≃ₐ[ℂ]
        Matrix (ZMod M) (ZMod M) ℂ :=
    (Subalgebra.equivOfEq (windowGeneratedAlgebra M) ⊤
      (window_generators_adjoin_top M)).trans Subalgebra.topEquiv
  constructor
  intro character
  have hNoCharacter := window_algebra_has_no_character M hM
  exact hNoCharacter.false
    (character.comp equivalence.symm.toAlgHom :
      Matrix (ZMod M) (ZMod M) ℂ →ₐ[ℂ] ℂ)

private theorem trace_states_separate
    (M : ℕ) [NeZero M] :
    ∀ rho sigma : Matrix (ZMod M) (ZMod M) ℂ,
      rho.PosSemidef → Matrix.trace rho = 1 →
      sigma.PosSemidef → Matrix.trace sigma = 1 →
      (∀ A, stateFunctional rho A = stateFunctional sigma A) →
      rho = sigma := by
  intro rho sigma _ _ _ _ hExpectations
  rw [Matrix.ext_iff_trace_mul_right]
  intro A
  exact hExpectations A

private theorem density_state_sections
    (M : ℕ) [NeZero M] :
    ∀ rho : Matrix (ZMod M) (ZMod M) ℂ,
      rho.PosSemidef → Matrix.trace rho = 1 →
      stateFunctional rho 1 = 1 ∧
      (∀ A B, stateFunctional rho (A + B) =
        stateFunctional rho A + stateFunctional rho B) ∧
      (∀ c A, stateFunctional rho (c • A) =
        c * stateFunctional rho A) ∧
      ∀ X : Matrix (ZMod M) (ZMod M) ℂ,
        0 ≤ stateFunctional rho (Matrix.conjTranspose X * X) := by
  intro rho hRho hTrace
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [stateFunctional] using hTrace
  · intro A B
    simp [stateFunctional, Matrix.mul_add]
  · intro c A
    simp [stateFunctional]
  · intro X
    simpa [stateFunctional, Matrix.mul_assoc] using
      (state_cone_sections rho hRho hTrace).1 X |>.2

private theorem density_state_not_multiplicative
    (M : ℕ) [NeZero M] (hM : 1 < M) :
    ∃ rho A B : Matrix (ZMod M) (ZMod M) ℂ,
      rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
      stateFunctional rho A = 0 ∧
      stateFunctional rho B = 0 ∧
      stateFunctional rho (A * B) = 1 := by
  letI : Fact (1 < M) := ⟨hM⟩
  refine ⟨Matrix.single 0 0 1, Matrix.single 0 1 1,
    Matrix.single 1 0 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.diagonal_single]
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : i = 0
    · subst i
      simp
    · simp [hi]
  · simp
  · simp [stateFunctional]
  · simp [stateFunctional]
  · simp [stateFunctional]

/-- On every nontrivial finite cyclic window, the clock-shift operational
algebra is the full matrix algebra, its canonical centralizer consists exactly
of scalar matrices, and it has no complex character. Trace expectations
separate density matrices and every density matrix gives a normalized positive
linear state, yet explicit matrix units show that such a state need not be
multiplicative. -/
theorem operational_complete_not_classically_complete
    (M : ℕ) [NeZero M] (hM : 1 < M) :
    windowGeneratedAlgebra M = ⊤ ∧
      (Subalgebra.centralizer ℂ
          (windowGeneratedAlgebra M :
            Set (Matrix (ZMod M) (ZMod M) ℂ)) :
        Set (Matrix (ZMod M) (ZMod M) ℂ)) =
        Set.range (Matrix.scalar (ZMod M)) ∧
      IsEmpty (windowGeneratedAlgebra M →ₐ[ℂ] ℂ) ∧
      (∀ rho sigma : Matrix (ZMod M) (ZMod M) ℂ,
        rho.PosSemidef → Matrix.trace rho = 1 →
        sigma.PosSemidef → Matrix.trace sigma = 1 →
        (∀ A, stateFunctional rho A = stateFunctional sigma A) →
        rho = sigma) ∧
      (∀ rho : Matrix (ZMod M) (ZMod M) ℂ,
        rho.PosSemidef → Matrix.trace rho = 1 →
        stateFunctional rho 1 = 1 ∧
        (∀ A B, stateFunctional rho (A + B) =
          stateFunctional rho A + stateFunctional rho B) ∧
        (∀ c A, stateFunctional rho (c • A) =
          c * stateFunctional rho A) ∧
        ∀ X : Matrix (ZMod M) (ZMod M) ℂ,
          0 ≤ stateFunctional rho (Matrix.conjTranspose X * X)) ∧
      ∃ rho A B : Matrix (ZMod M) (ZMod M) ℂ,
        rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
        stateFunctional rho A = 0 ∧
        stateFunctional rho B = 0 ∧
        stateFunctional rho (A * B) = 1 := by
  exact ⟨window_generators_adjoin_top M,
    generated_centralizer_eq_scalars M,
    generated_algebra_has_no_character M hM,
    trace_states_separate M,
    density_state_sections M,
    density_state_not_multiplicative M hM⟩

#print axioms operational_complete_not_classically_complete

end D5.S3.Observer.WindowAlgebra.OperationalClassicalSeparation
