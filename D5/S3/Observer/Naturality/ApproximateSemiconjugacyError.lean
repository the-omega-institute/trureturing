/- GID: D5/S3/Observer/Naturality/ApproximateSemiconjugacyError
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/ApproximateSemiconjugacyError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A uniform semiconjugacy defect has geometric finite-time orbit bounds. -/

import D5.S3.Observer.MetricGeometry.OutputTrajectoryError
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

/- Library-search audit trail (2026-08-17):
   * Repository search found the exact finite-sum estimate
     `OutputTrajectoryError.output_trajectory_error`; the proof applies it below.
   * Repository search also found the nonuniform estimate
     `IteratedDefectAccumulation.iterated_naturality_defect_bound`; it is related but
     is not needed by this uniform-defect wrapper.
   * Pinned-mathlib search found the exact supporting declarations
     `NNReal.summable_geometric`, `NNReal.tsum_geometric`, and `Finset.one_geom_sum`.
   * Pinned-mathlib search found no declaration containing the complete conjunction
     of the finite-sum, contractive, and unit-Lipschitz conclusions. -/

namespace D5.S3.Observer.Naturality.ApproximateSemiconjugacyError

/-- A uniform one-step semiconjugacy defect controls every finite orbit, with the
geometric-series contraction bound and the linear unit-Lipschitz specialization. -/
theorem approximate_semiconjugacy_error
    {Y Z : Type*} [PseudoMetricSpace Z]
    (tau : Y -> Y) (sigma : Z -> Z) (pi : Y -> Z)
    (L delta : NNReal)
    (hsigma : LipschitzWith L sigma)
    (hdefect : forall y, nndist (pi (tau y)) (sigma (pi y)) <= delta) :
    (forall (k : Nat) (y : Y),
      nndist (pi ((tau^[k]) y)) ((sigma^[k]) (pi y)) <=
        delta * ∑ j ∈ Finset.range k, L ^ j) ∧
    (L < 1 -> forall (k : Nat) (y : Y),
      nndist (pi ((tau^[k]) y)) ((sigma^[k]) (pi y)) <= delta / (1 - L)) ∧
    (L = 1 -> forall (k : Nat) (y : Y),
      nndist (pi ((tau^[k]) y)) ((sigma^[k]) (pi y)) <= k * delta) := by
  have hmain : forall (k : Nat) (y : Y),
      nndist (pi ((tau^[k]) y)) ((sigma^[k]) (pi y)) <=
        delta * ∑ j ∈ Finset.range k, L ^ j := by
    intro k y
    have hbound :=
      D5.S3.Observer.MetricGeometry.OutputTrajectoryError.output_trajectory_error
        tau sigma pi pi id L 1 (delta : ENNReal) 0
        hsigma LipschitzWith.id
        (by
          intro state
          simpa only [edist_nndist, ENNReal.coe_le_coe] using hdefect state)
        (by intro state; simp)
        k y
    rw [← ENNReal.coe_le_coe]
    simpa only [id_eq, edist_nndist, ENNReal.coe_one, ENNReal.coe_mul,
      ENNReal.coe_pow, ENNReal.ofNNReal_finsetSum, zero_add, one_mul] using hbound
  refine ⟨hmain, ?_, ?_⟩
  · intro hL k y
    have hsum : ∑ j ∈ Finset.range k, L ^ j <= (1 - L)⁻¹ := by
      calc
        ∑ j ∈ Finset.range k, L ^ j <= ∑' j : Nat, L ^ j :=
          (NNReal.summable_geometric hL).sum_le_tsum
            (Finset.range k) (fun _ _ => zero_le)
        _ = (1 - L)⁻¹ := NNReal.tsum_geometric hL
    exact (hmain k y).trans
      (by simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_right hsum delta)
  · intro hL k y
    subst L
    simpa [one_geom_sum, mul_comm] using hmain k y

/-- Constant real observations on a two-state carrier witness the hypotheses. -/
example : True := by
  have _witness :=
    approximate_semiconjugacy_error
      (Y := Bool) (Z := Real)
      (fun b : Bool => b) id (fun _ : Bool => (0 : Real)) 1 0
      LipschitzWith.id (by intro; simp)
  exact True.intro

#print axioms approximate_semiconjugacy_error

end D5.S3.Observer.Naturality.ApproximateSemiconjugacyError
