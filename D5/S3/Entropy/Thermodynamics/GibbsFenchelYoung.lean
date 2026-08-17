/- GID: D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung
   generality: G
   mirror-B: D5/B/S3/Entropy/Thermodynamics/GibbsFenchelYoung
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Gibbs laws satisfy the exact Fenchel-Young entropy identity. -/

/- Library-search audit trail (2026-08-17):
   * Repository grep covered `Fenchel`, `Gibbs`, `log-sum-exp`, partition functions,
     free energy, KL divergence, and relative entropy. Existing D5 modules provide the
     finite `klDivergence` and `shannonEntropy` definitions, but not this Gibbs identity.
   * Pinned-mathlib grep and the Lean skill's `smart_search.sh` found no complete finite
     Gibbs Fenchel-Young identity. Mathlib does provide the exact scalar rewrites used here:
     `Real.log_div`, `Real.log_exp`, and `Real.negMulLog`.
   * A Loogle query for `Gibbs entropy partition function` returned `Unknown identifier Gibbs`;
     that endpoint result is recorded as a failed query, not as evidence of absence.
-/

import D5.S3.Entropy.MaxEntropy

namespace D5.S3.Entropy.Thermodynamics.GibbsFenchelYoung

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.MaxEntropy

/-- The partition function of a finite energy profile, using the sign convention `exp H`. -/
noncomputable def gibbsPartition {ι : Type*} [Fintype ι] (H : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (H i)

/-- The normalized Gibbs mass associated with a finite energy profile. -/
noncomputable def gibbsMass {ι : Type*} [Fintype ι] (H : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (H i) / gibbsPartition H

/-- Finite Gibbs Fenchel-Young identity: log partition equals expected energy plus entropy
and relative entropy from the Gibbs law. -/
theorem finite_gibbs_fenchel_young {ι : Type*} [Fintype ι] [Nonempty ι]
    (ρ H : ι → ℝ) (hρ : (∀ i, 0 < ρ i) ∧ ∑ i, ρ i = 1) :
    Real.log (gibbsPartition H) =
      (∑ i, ρ i * H i) + shannonEntropy ρ + klDivergence ρ (gibbsMass H) := by
  classical
  have hpartition_pos : 0 < gibbsPartition H := by
    rw [gibbsPartition]
    refine Finset.sum_pos' (fun i _ => (Real.exp_pos (H i)).le) ?_
    let i : ι := Classical.choice inferInstance
    exact ⟨i, Finset.mem_univ i, Real.exp_pos (H i)⟩
  have hpartition_ne : gibbsPartition H ≠ 0 := ne_of_gt hpartition_pos
  have hgibbs_pos (i : ι) : 0 < gibbsMass H i :=
    div_pos (Real.exp_pos (H i)) hpartition_pos
  have hterm (i : ι) :
      ρ i * H i + Real.negMulLog (ρ i) +
          ρ i * Real.log (ρ i / gibbsMass H i) =
        ρ i * Real.log (gibbsPartition H) := by
    rw [Real.log_div (ne_of_gt (hρ.1 i)) (ne_of_gt (hgibbs_pos i))]
    rw [gibbsMass, Real.log_div (Real.exp_ne_zero _) hpartition_ne, Real.log_exp]
    simp only [Real.negMulLog]
    ring
  rw [klDivergence, shannonEntropy]
  calc
    Real.log (gibbsPartition H) =
        (∑ i, ρ i) * Real.log (gibbsPartition H) := by rw [hρ.2, one_mul]
    _ = ∑ i, ρ i * Real.log (gibbsPartition H) := by rw [Finset.sum_mul]
    _ = ∑ i, (ρ i * H i + Real.negMulLog (ρ i) +
        ρ i * Real.log (ρ i / gibbsMass H i)) := by
          exact Finset.sum_congr rfl fun i _ => (hterm i).symm
    _ = (∑ i, ρ i * H i) + (∑ i, Real.negMulLog (ρ i)) +
        ∑ i, ρ i * Real.log (ρ i / gibbsMass H i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

#print axioms finite_gibbs_fenchel_young

end D5.S3.Entropy.Thermodynamics.GibbsFenchelYoung
