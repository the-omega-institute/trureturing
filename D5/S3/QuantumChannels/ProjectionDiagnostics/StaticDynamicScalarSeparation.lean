/- GID: D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Static coherence loss and dynamic residual return vary independently. -/

import D5.S3.QuantumChannels.PinchingProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumChannels.ProjectionDiagnostics.StaticDynamicScalarSeparation

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open D5.S3.QuantumChannels.Pinching
open D5.S3.QuantumChannels.PinchingProjection

/-- Standard-basis unread measurement as a complex-linear endomorphism. -/
def pinchingEnd : Module.End ℂ QubitMatrix where
  toFun := pinching
  map_add' A B := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  map_smul' c A := by
    ext i j
    by_cases hij : i = j <;> simp [hij]

/-- A generator that returns the upper off-diagonal residual to the first visible diagonal. -/
def residualReturnGenerator : Module.End ℂ QubitMatrix where
  toFun A := fun i j => if i = 0 ∧ j = 0 then A 0 1 else 0
  map_add' A B := by
    ext i j
    by_cases hij : i = 0 ∧ j = 0
    · rcases hij with ⟨rfl, rfl⟩
      change A 0 1 + B 0 1 =
        (if (0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0 then A 0 1 else 0) +
          (if (0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0 then B 0 1 else 0)
      simp
    · change (if i = 0 ∧ j = 0 then (A + B) 0 1 else 0) =
        (if i = 0 ∧ j = 0 then A 0 1 else 0) +
          (if i = 0 ∧ j = 0 then B 0 1 else 0)
      simp [hij, Matrix.add_apply]
  map_smul' c A := by
    ext i j
    by_cases hij : i = 0 ∧ j = 0
    · rcases hij with ⟨rfl, rfl⟩
      change c * A 0 1 = c • (if (0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0 then A 0 1 else 0)
      simp
    · change (if i = 0 ∧ j = 0 then (c • A) 0 1 else 0) =
        c • (if i = 0 ∧ j = 0 then A 0 1 else 0)
      simp [hij, Matrix.smul_apply]

/-- The static Hilbert--Schmidt loss and the dynamic residual-return block are independent:
static loss can exceed every prescribed bound while the identity generator has zero return,
and it can be arbitrarily small but positive while an explicit generator has nonzero return. -/
theorem static_loss_and_dynamic_return_are_independent :
    (∀ lower : ℝ, ∃ rho : QubitMatrix,
      lower <
          (hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho)).re ∧
        pinchingEnd ∘ₗ (1 : Module.End ℂ QubitMatrix) ∘ₗ (1 - pinchingEnd) = 0) ∧
      (∀ upper : ℝ, 0 < upper → ∃ rho : QubitMatrix,
        0 < (hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho)).re ∧
          (hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho)).re < upper ∧
          pinchingEnd ∘ₗ residualReturnGenerator ∘ₗ (1 - pinchingEnd) ≠ 0) := by
  constructor
  · intro lower
    let amplitude : ℝ := |lower| + 1
    let rho : QubitMatrix := !![0, (amplitude : ℂ); 0, 0]
    refine ⟨rho, ?_, ?_⟩
    · rw [pinching_discarded_coherence_mass]
      norm_num [rho, Complex.normSq]
      dsimp only [amplitude]
      nlinarith [le_abs_self lower]
    · ext A i j
      by_cases hij : i = j <;> simp [pinchingEnd, hij]
  · intro upper hUpper
    let amplitude : ℝ := upper / (upper + 1)
    let rho : QubitMatrix := !![0, (amplitude : ℂ); 0, 0]
    have hDenominator : 0 < upper + 1 := by linarith
    have hAmplitudePositive : 0 < amplitude := by
      exact div_pos hUpper hDenominator
    have hAmplitudeLtOne : amplitude < 1 := by
      dsimp only [amplitude]
      exact (div_lt_one hDenominator).2 (by linarith)
    have hAmplitudeLtUpper : amplitude < upper := by
      dsimp only [amplitude]
      rw [div_lt_iff₀ hDenominator]
      nlinarith [sq_pos_of_pos hUpper]
    have hAmplitudeSqLtUpper : amplitude ^ 2 < upper := by
      nlinarith
    refine ⟨rho, ?_, ?_, ?_⟩
    · rw [pinching_discarded_coherence_mass]
      norm_num [rho, Complex.normSq]
      positivity
    · rw [pinching_discarded_coherence_mass]
      norm_num [rho, Complex.normSq]
      simpa [pow_two] using hAmplitudeSqLtUpper
    · intro hZero
      have hAtWitness := LinearMap.congr_fun hZero qubitX
      have hFirstEntry := congrFun (congrFun hAtWitness 0) 0
      change (qubitX - pinching qubitX) 0 1 = 0 at hFirstEntry
      norm_num [pinching_apply, qubitX, Matrix.sub_apply] at hFirstEntry

#print axioms pinchingEnd
#print axioms residualReturnGenerator
#print axioms static_loss_and_dynamic_return_are_independent

end D5.S3.QuantumChannels.ProjectionDiagnostics.StaticDynamicScalarSeparation
