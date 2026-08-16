/- GID: D5/S3/Observer/Naturality/IteratedDefectAccumulation
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/IteratedDefectAccumulation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local naturality defects accumulate with Lipschitz weights along every orbit. -/

import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Tactic

open scoped BigOperators

/- Library-search audit trail (2026-08-16):
   * Repository search found only `output_trajectory_error`, whose uniform one-step
     bound is strictly weaker than the orbitwise defect sum proved here.
   * `smart_search.sh` found no full accumulated nonuniform iterate-error theorem.
   * Pinned-Mathlib source search found the exact supporting declarations
     `LipschitzWith.edist_le_mul`, `Function.iterate_succ_apply'`, and
     `Finset.sum_range_succ`; they are imported and applied below. -/

namespace D5.S3.Observer.Naturality.IteratedDefectAccumulation

/-- Under an `L`-Lipschitz abstract update, the defect after `n` steps is at most
the sum of the one-step defects along the concrete orbit, weighted by the
remaining number of abstract updates. -/
theorem iterated_naturality_defect_bound
    {Y Z : Type*} [PseudoEMetricSpace Z]
    (tau : Y -> Y) (sigma : Z -> Z) (projection : Y -> Z)
    (L : NNReal) (hsigma : LipschitzWith L sigma) :
    forall (n : Nat) (y : Y),
      edist (projection ((tau^[n]) y)) ((sigma^[n]) (projection y)) <=
        ∑ k ∈ Finset.range n,
          (L : ENNReal) ^ (n - 1 - k) *
            edist (projection (tau ((tau^[k]) y)))
              (sigma (projection ((tau^[k]) y))) := by
  intro n
  induction n with
  | zero =>
      intro y
      simp
  | succ n ih =>
      intro y
      calc
        edist (projection ((tau^[Nat.succ n]) y))
            ((sigma^[Nat.succ n]) (projection y)) =
          edist (projection (tau ((tau^[n]) y)))
            (sigma ((sigma^[n]) (projection y))) := by
              rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        _ <= edist (projection (tau ((tau^[n]) y)))
              (sigma (projection ((tau^[n]) y))) +
            edist (sigma (projection ((tau^[n]) y)))
              (sigma ((sigma^[n]) (projection y))) := edist_triangle _ _ _
        _ <= edist (projection (tau ((tau^[n]) y)))
              (sigma (projection ((tau^[n]) y))) +
            (L : ENNReal) *
              edist (projection ((tau^[n]) y))
                ((sigma^[n]) (projection y)) :=
          add_le_add_right (hsigma.edist_le_mul _ _) _
        _ <= edist (projection (tau ((tau^[n]) y)))
              (sigma (projection ((tau^[n]) y))) +
            (L : ENNReal) *
              ∑ k ∈ Finset.range n,
                (L : ENNReal) ^ (n - 1 - k) *
                  edist (projection (tau ((tau^[k]) y)))
                    (sigma (projection ((tau^[k]) y))) := by
          exact add_le_add_right (mul_le_mul_right (ih y) (L : ENNReal)) _
        _ = ∑ k ∈ Finset.range (Nat.succ n),
              (L : ENNReal) ^ (Nat.succ n - 1 - k) *
                edist (projection (tau ((tau^[k]) y)))
                  (sigma (projection ((tau^[k]) y))) := by
          rw [Finset.sum_range_succ]
          simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, one_mul]
          rw [add_comm]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hklt : k < n := Finset.mem_range.mp hk
          have hexponent : n - k = (n - 1 - k) + 1 := by omega
          rw [hexponent, pow_succ']
          ac_rfl

/-- A flipping Boolean orbit observed in the reals instantiates the bound. -/
example : True := by
  have _witness :=
    iterated_naturality_defect_bound
      (Y := Bool) (Z := Real)
      (fun b => !b) id (fun b => if b then 1 else 0) 1 LipschitzWith.id
  exact True.intro

#print axioms iterated_naturality_defect_bound

end D5.S3.Observer.Naturality.IteratedDefectAccumulation
