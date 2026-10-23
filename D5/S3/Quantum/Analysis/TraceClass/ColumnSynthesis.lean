/- GID: D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/ColumnSynthesis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-summable arbitrary Hilbert-basis columns synthesize a bounded Hilbert-Schmidt operator with a uniform norm estimate. -/

import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Hilbert-Schmidt column synthesis

The synthesis argument uses the attributed Physlib Cauchy-Schwarz and square-sum
suppliers in `TraceClass.HilbertSchmidt`, adopted from Tom Ole Diem's Physlib at
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142` under Apache-2.0.
The upstream notices in that module and
`docs/reports/quantum-hs-suppliers/physlib-LICENSE.txt` govern those suppliers.
The column synthesis proof is the repository's quadratic-reference construction.
-/

set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
noncomputable section
namespace HilbertSchmidt
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Square-summable columns on an arbitrary Hilbert basis determine a bounded
Hilbert-Schmidt operator, with the exact columns and square sum and a uniform
operator norm bound. -/
theorem exists_hilbertSchmidt_of_square_summable_columns
    {w : Set H} (e : HilbertBasis w ℂ H) (v : w → H)
    (hv : Summable (fun i : w => ‖v i‖ ^ 2)) :
    ∃ A : H →L[ℂ] H,
      (∀ i, A (e i) = v i) ∧ IsHilbertSchmidt A ∧
      (∑' i : w, ‖A (e i)‖ ^ 2) = ∑' i : w, ‖v i‖ ^ 2 ∧
      ‖A‖ ≤ Real.sqrt (∑' i : w, ‖v i‖ ^ 2) := by
  classical
  have hprod (x : H) : Summable (fun i : w => ‖⟪e i, x⟫_ℂ‖ * ‖v i‖) :=
    summable_norm_mul_of_square_sums _ _ (hasSum_norm_sq_inner_basis e x).summable hv
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hsum (x : H) : Summable (fun i : w => ⟪e i, x⟫_ℂ • v i) := by
    apply Summable.of_norm
    simpa only [norm_smul] using hprod x
  let L : H →ₗ[ℂ] H :=
    { toFun := fun x => ∑' i : w, ⟪e i, x⟫_ℂ • v i
      map_add' := by
        intro x y
        simp only [inner_add_right, add_smul]
        exact (hsum x).tsum_add (hsum y)
      map_smul' := by
        intro c x
        simp only [inner_smul_right, mul_smul]
        exact (hsum x).tsum_const_smul c }
  have hbound (x : H) : ‖L x‖ ≤ Real.sqrt (∑' i : w, ‖v i‖ ^ 2) * ‖x‖ := by
    calc
      ‖L x‖ ≤ ∑' i : w, ‖⟪e i, x⟫_ℂ • v i‖ := norm_tsum_le_tsum_norm (by simpa only [norm_smul] using hprod x)
      _ = ∑' i : w, ‖⟪e i, x⟫_ℂ‖ * ‖v i‖ := by simp only [norm_smul]
      _ ≤ Real.sqrt (∑' i : w, ‖⟪e i, x⟫_ℂ‖ ^ 2) *
          Real.sqrt (∑' i : w, ‖v i‖ ^ 2) :=
        tsum_mul_le_sqrt_mul_sqrt (hasSum_norm_sq_inner_basis e x).summable hv
          (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      _ = Real.sqrt (∑' i : w, ‖v i‖ ^ 2) * ‖x‖ := by
        rw [(hasSum_norm_sq_inner_basis e x).tsum_eq, Real.sqrt_sq (norm_nonneg x), mul_comm]
  let A := L.mkContinuous (Real.sqrt (∑' i : w, ‖v i‖ ^ 2)) hbound
  have hcol (i : w) : A (e i) = v i := by
    change (∑' j : w, ⟪e j, e i⟫_ℂ • v j) = v i
    simp only [orthonormal_iff_ite.mp e.orthonormal, ite_smul, one_smul, zero_smul]
    simp
  refine ⟨A, hcol, ⟨w, e, ?_⟩, ?_, ?_⟩
  · simpa only [hcol] using hv
  · simp only [hcol]
  · exact L.mkContinuous_norm_le (Real.sqrt_nonneg _) hbound

#print axioms exists_hilbertSchmidt_of_square_summable_columns
end HilbertSchmidt
