/- GID: D5/S1/FixedPoints/AffineFeedbackThreshold
   generality: G
   mirror-B: D5/B/S1/FixedPoints/AffineFeedbackThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Affine feedback has a unit-gain stability threshold. -/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-08-16):
   * Exact pinned-Mathlib and Loogle hits
     `ContractingWith.fixedPoint_unique` and
     `ContractingWith.tendsto_iterate_fixedPoint` supply uniqueness and
     convergence for a contraction; both are imported and applied below.
   * Loogle's shaped power-limit query also returned
     `tendsto_pow_atTop_nhds_zero_of_lt_one`, but the contraction theorem
     already packages the required iterate convergence.
   * Repository and pinned-Mathlib searches for affine iteration, affine
     contraction, and affine fixed points found no theorem packaging all
     three gain regimes in the statement below.
   * LeanSearch's query endpoint returned HTTP 404. -/

namespace D5.S1.FixedPoints.AffineFeedbackThreshold

/-- The affine feedback map on an active local region. -/
def affineFeedback (a b x : Real) : Real :=
  a + b * x

/-- The fixed point of the affine feedback map away from unit gain. -/
noncomputable def affineEquilibrium (a b : Real) : Real :=
  a / (1 - b)

private theorem affine_equilibrium_is_fixed (a b : Real) (hb : b ≠ 1) :
    Function.IsFixedPt (affineFeedback a b) (affineEquilibrium a b) := by
  change a + b * (a / (1 - b)) = a / (1 - b)
  field_simp [sub_ne_zero.mpr hb.symm]
  ring

/-- For the affine local feedback model `x |-> a + b*x`, nonnegative gain below
one gives a contraction with the unique displayed equilibrium and convergent
iteration. Gain above one fixes the same equilibrium but strictly amplifies
every nonzero deviation, while unit gain preserves all pairwise distances. -/
theorem affine_feedback_threshold (a b : Real) :
    ((0 ≤ b ∧ b < 1) →
      ContractingWith b.toNNReal (affineFeedback a b) ∧
        (∀ x, Function.IsFixedPt (affineFeedback a b) x ↔
          x = affineEquilibrium a b) ∧
        (∀ x, Filter.Tendsto (fun n => (affineFeedback a b)^[n] x)
          Filter.atTop (nhds (affineEquilibrium a b)))) ∧
    (1 < b →
      Function.IsFixedPt (affineFeedback a b) (affineEquilibrium a b) ∧
        (∀ x, x ≠ affineEquilibrium a b →
          dist (affineFeedback a b x) (affineEquilibrium a b) =
              b * dist x (affineEquilibrium a b) ∧
            dist x (affineEquilibrium a b) <
              dist (affineFeedback a b x) (affineEquilibrium a b))) ∧
    (b = 1 → ∀ x y,
      dist (affineFeedback a b x) (affineFeedback a b y) = dist x y) := by
  constructor
  · intro hstable
    have hcontract : ContractingWith b.toNNReal (affineFeedback a b) := by
      constructor
      · exact NNReal.coe_lt_coe.mp (by
          simpa [Real.coe_toNNReal b hstable.1] using hstable.2)
      · apply LipschitzWith.of_dist_le_mul
        intro x y
        rw [Real.coe_toNNReal b hstable.1]
        apply le_of_eq
        rw [Real.dist_eq, Real.dist_eq]
        calc
          |affineFeedback a b x - affineFeedback a b y| =
              |b * (x - y)| := by
                congr 1
                simp only [affineFeedback]
                ring
          _ = b * |x - y| := by rw [abs_mul, abs_of_nonneg hstable.1]
    have hequilibrium :
        Function.IsFixedPt (affineFeedback a b) (affineEquilibrium a b) :=
      affine_equilibrium_is_fixed a b (ne_of_lt hstable.2)
    refine ⟨hcontract, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        exact (hcontract.fixedPoint_unique hx).trans
          (hcontract.fixedPoint_unique hequilibrium).symm
      · intro hx
        simpa only [hx] using hequilibrium
    · intro x
      have hlimit := hcontract.tendsto_iterate_fixedPoint x
      have hequilibrium_library := hcontract.fixedPoint_unique hequilibrium
      simpa only [← hequilibrium_library] using hlimit
  · constructor
    · intro hunstable
      have hequilibrium :
          Function.IsFixedPt (affineFeedback a b) (affineEquilibrium a b) :=
        affine_equilibrium_is_fixed a b (ne_of_gt hunstable)
      refine ⟨hequilibrium, ?_⟩
      intro x hx
      have hb0 : 0 ≤ b := le_trans zero_le_one hunstable.le
      have hdistance :
          dist (affineFeedback a b x) (affineEquilibrium a b) =
            b * dist x (affineEquilibrium a b) := by
        calc
          dist (affineFeedback a b x) (affineEquilibrium a b) =
              dist (affineFeedback a b x)
                (affineFeedback a b (affineEquilibrium a b)) := by
                  rw [hequilibrium]
          _ = b * dist x (affineEquilibrium a b) := by
            rw [Real.dist_eq, Real.dist_eq]
            calc
              |affineFeedback a b x -
                  affineFeedback a b (affineEquilibrium a b)| =
                    |b * (x - affineEquilibrium a b)| := by
                      congr 1
                      simp only [affineFeedback]
                      ring
              _ = b * |x - affineEquilibrium a b| := by
                rw [abs_mul, abs_of_nonneg hb0]
      refine ⟨hdistance, ?_⟩
      rw [hdistance]
      simpa only [one_mul] using
        mul_lt_mul_of_pos_right hunstable (dist_pos.mpr hx)
    · intro hcritical
      subst b
      intro x y
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      simp only [affineFeedback, one_mul]
      ring

end D5.S1.FixedPoints.AffineFeedbackThreshold

#print axioms D5.S1.FixedPoints.AffineFeedbackThreshold.affine_feedback_threshold
