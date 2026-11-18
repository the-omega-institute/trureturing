/- GID: D5/S3/Quantum/Recovery/BKMSubalgebraDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMSubalgebraDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive BKM transposes force commutation with reduced-state projections. -/

import D5.S3.Quantum.Matrix.BKMProjectionRigidity
import D5.S3.Quantum.Algebra.OrderedGNSProjection
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

/-! # Faithful finite matrix subalgebras and the actual BKM transpose -/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Recovery.BKMSubalgebraDefect

open D5.S3.Quantum.Algebra.OrderedGNSProjection
open D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
open D5.S3.Quantum.Matrix.BKMProjectionRigidity
open D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction (omega)
open D5.S3.Divergence.LogDerivTrace (logDeriv)
open private projection_mem projection_left_comparison
  from D5.S3.Quantum.Algebra.OrderedGNSProjection

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

private abbrev Mat (n : Type*) := Matrix n n ℂ

private def tracialDensity (n : Type*) [Fintype n] [DecidableEq n] : Mat n :=
  (1 / (Fintype.card n : ℝ)) • 1

private theorem tracialDensity_posDef : (tracialDensity n).PosDef :=
  Matrix.PosDef.one.smul (one_div_pos.mpr (by exact_mod_cast Fintype.card_pos))

private theorem tracialDensity_trace : (tracialDensity n).trace = 1 := by
  have hd : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [tracialDensity, Matrix.trace_smul, Complex.real_smul, hd]

/-- The actual trace-orthogonal projection, with its codomain restricted to B. -/
def traceExpectation (B : StarSubalgebra ℂ (Mat n)) : Mat n →ₗ[ℂ] B :=
  LinearMap.codRestrict B.toSubmodule
    (projection (tracialDensity n) tracialDensity_posDef B)
    (projection_mem _ _ B)

private theorem traceExpectation_contract (B : StarSubalgebra ℂ (Mat n)) :
    Expectation (tracialDensity n) B (projection (tracialDensity n) tracialDensity_posDef B) := by
  let ρ := tracialDensity n
  let hρ : ρ.PosDef := tracialDensity_posDef
  have ht (X : Mat n) : state ρ X = (1 / (Fintype.card n : ℝ)) • X.trace := by
    simp [ρ, tracialDensity, state, Matrix.trace_smul]
  apply ((ordered_gns_characterization ρ hρ tracialDensity_trace B).2.2.2.2.2).mp
  intro X b hb
  have h := projection_left_comparison ρ hρ B X (star b) (B.star_mem' hb)
  simpa only [star_star, ht, Matrix.trace_mul_comm b] using h

private theorem traceExpectation_mono (B : StarSubalgebra ℂ (Mat n)) :
    Monotone (fun X => (traceExpectation B X : Mat n)) := by
  intro X Y h
  change projection _ _ B X ≤ projection _ _ B Y
  rw [← sub_nonneg, ← map_sub, Matrix.nonneg_iff_posSemidef]
  exact (traceExpectation_contract B).2.2.1.1 (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))

private theorem traceExpectation_smul_one (B : StarSubalgebra ℂ (Mat n)) (r : ℝ) :
    (traceExpectation B (r • (1 : Mat n)) : Mat n) = r • 1 := by
  change ((projection _ _ B).restrictScalars ℝ) (r • (1 : Mat n)) = _
  rw [map_smul]
  exact congrArg (r • ·) (traceExpectation_contract B).1

private theorem reduced_posDef (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) :
    (traceExpectation B a : Mat n).PosDef := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ ha.isHermitian.eigenvalues
    Finset.univ_nonempty
  let l := ha.isHermitian.eigenvalues i
  have hl : l • (1 : Mat n) ≤ a :=
    (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff ha.isHermitian l).mp
      (fun j => hi j (Finset.mem_univ j))
  have h := traceExpectation_mono B hl
  change (traceExpectation B (l • (1 : Mat n)) : Mat n) ≤ (traceExpectation B a : Mat n) at h
  rw [traceExpectation_smul_one] at h
  exact (Matrix.PosDef.one.smul (ha.eigenvalues_pos i)).isStrictlyPositive.of_le h |>.posDef

/-- The actual BKM transpose from B into the ambient complex matrix algebra. -/
def bkmTranspose (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) :
    B →ₗ[ℂ] Mat n :=
  (omegaEquiv a ha).toLinearMap.comp
    (B.toSubmodule.subtype.comp
      (omegaRestrict B (traceExpectation B a) (reduced_posDef B a ha)).symm.toLinearMap)

/-- The transpose applies the reduced resolvent derivative and the ambient power integral. -/
theorem bkmTranspose_apply (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef)
    (Y : B) :
    bkmTranspose B a ha Y = omega a (logDeriv (traceExpectation B a : Mat n) (Y : Mat n)) := by
  change omegaEquiv a ha
    (((omegaRestrict B (traceExpectation B a) (reduced_posDef B a ha)).symm Y : B) : Mat n) = _
  rw [omegaEquiv_apply, omegaRestrict_symm_apply]

/-- Positivity of the actual transpose forces every projection in B that
commutes with the reduced state to commute with the faithful ambient state. -/
theorem bkmTranspose_positive_commute (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef)
    (hpos : ∀ Y : B, (Y : Mat n).PosSemidef → (bkmTranspose B a ha Y).PosSemidef)
    (P : B) (hp : (P : Mat n).IsHermitian) (hp2 : (P : Mat n) * (P : Mat n) = P)
    (hc : Commute (traceExpectation B a : Mat n) (P : Mat n)) : Commute a (P : Mat n) := by
  let τ := traceExpectation B a
  let hτ := reduced_posDef B a ha
  let Y := omegaRestrict B τ hτ P
  have hY : (Y : Mat n).PosSemidef := by
    change (omegaRestrict B τ hτ P : Mat n).PosSemidef
    rw [omegaRestrict_apply, omega_of_commute _ _ hτ hc]
    have hcorner : (τ : Mat n) * (P : Mat n) = (P : Mat n) * (τ : Mat n) * (P : Mat n) := by
      calc
        (τ : Mat n) * (P : Mat n) = (τ : Mat n) * ((P : Mat n) * (P : Mat n)) := by rw [hp2]
        _ = _ := by rw [← mul_assoc, hc.eq]
    rw [hcorner]
    simpa only [hp.eq] using hτ.posSemidef.mul_mul_conjTranspose_same (P : Mat n)
  have h := hpos Y hY
  change (omegaEquiv a ha
    (((omegaRestrict B τ hτ).symm (omegaRestrict B τ hτ P) : B) : Mat n)).PosSemidef at h
  rw [LinearEquiv.symm_apply_apply, omegaEquiv_apply] at h
  exact (omega_projection_posSemidef_iff a P ha hp hp2).mp h

#print axioms bkmTranspose_positive_commute

end D5.S3.Quantum.Recovery.BKMSubalgebraDefect
