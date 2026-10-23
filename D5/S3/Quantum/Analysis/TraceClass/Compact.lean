/- GID: D5/S3/Quantum/Analysis/TraceClass/Compact
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/Compact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Hilbert-basis column approximations converge in operator norm and prove arbitrary-Hilbert-space HS and trace-class compactness. -/

import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
import D5.S3.Quantum.Analysis.TraceClass.GeneralIdeal
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder InnerProductSpace Classical
open Filter Topology
noncomputable section

namespace HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A square-summable Hilbert-basis column family bounds the operator norm. -/
theorem opNorm_le_sqrt_column_square_sum {w : Set H} (b : HilbertBasis w ℂ H)
    (T : H →L[ℂ] H) (hT : Summable (fun i : w => ‖T (b i)‖ ^ 2)) :
    ‖T‖ ≤ Real.sqrt (∑' i : w, ‖T (b i)‖ ^ 2) := by
  obtain ⟨A, hcol, _, _, hnorm⟩ :=
    exists_hilbertSchmidt_of_square_summable_columns b (fun i => T (b i)) hT
  have hdense : Dense (Submodule.span ℂ (Set.range b) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  have hAT : A = T := ContinuousLinearMap.ext_on hdense (by
    rintro _ ⟨i, rfl⟩
    exact hcol i)
  simpa only [hAT] using hnorm

/-- Uses Mathlib's existing arbitrary-index finite projection. -/
def finiteColumnApprox {w : Set H} (b : HilbertBasis w ℂ H)
    (S : H →L[ℂ] H) (F : Finset w) : H →L[ℂ] H :=
  S.comp (b.toUnconditionalSchauderBasis.proj F)

def tailColumnSquareSum {w : Set H} (b : HilbertBasis w ℂ H)
    (S : H →L[ℂ] H) (F : Finset w) : ℝ :=
  ∑' i : ↥((F : Set w)ᶜ), ‖S (b i.1)‖ ^ 2

theorem finiteColumnApprox_apply_basis {w : Set H} (b : HilbertBasis w ℂ H)
    (S : H →L[ℂ] H) (F : Finset w) (i : w) :
    finiteColumnApprox b S F (b i) = if i ∈ F then S (b i) else 0 := by
  classical
  change S (b.toUnconditionalSchauderBasis.proj F (b i)) = _
  have hp : b.toUnconditionalSchauderBasis.proj F (b i) =
      if i ∈ F then b i else 0 :=
    by simpa using GeneralSchauderBasis.proj_apply_basis_mem b.toUnconditionalSchauderBasis F i
  rw [hp]
  split_ifs <;> simp

/-- A finite column approximation is compact: the basis projection factors
through its finite-dimensional range. -/
theorem isCompactOperator_finiteColumnApprox {w : Set H} (b : HilbertBasis w ℂ H)
    (S : H →L[ℂ] H) (F : Finset w) : IsCompactOperator (finiteColumnApprox b S F) := by
  let P : H →L[ℂ] H := b.toUnconditionalSchauderBasis.proj F
  let V : Submodule ℂ H := P.toLinearMap.range
  letI : FiniteDimensional ℂ (Submodule.span ℂ (b '' (F : Set w))) :=
    FiniteDimensional.span_of_finite ℂ (F.finite_toSet.image b)
  have hr : V = Submodule.span ℂ (b '' (F : Set w)) :=
    GeneralSchauderBasis.range_proj_eq_span b.toUnconditionalSchauderBasis F
  letI : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective (Submodule.inclusion hr.le)
      (Submodule.inclusion_injective hr.le)
  letI : LocallyCompactSpace V :=
    LocallyCompactSpace.of_finiteDimensional_of_complete ℂ V
  have hPr : IsCompactOperator P.rangeRestrict :=
    isCompactOperator_of_locallyCompactSpace_dom P.rangeRestrict
  have hfactor : V.subtypeL.comp P.rangeRestrict = P :=
    ContinuousLinearMap.subtypeL_comp_codRestrict P V (LinearMap.mem_range_self _)
  have hP : IsCompactOperator P := by
    rw [← hfactor]
    simpa only [ContinuousLinearMap.coe_comp] using hPr.clm_comp V.subtypeL
  change IsCompactOperator (S.comp P)
  simpa only [ContinuousLinearMap.coe_comp] using hP.clm_comp S

theorem norm_sub_finiteColumnApprox_le {w : Set H} (b : HilbertBasis w ℂ H)
    (S : H →L[ℂ] H) (hS : Summable (fun i : w => ‖S (b i)‖ ^ 2)) (F : Finset w) :
    ‖S - finiteColumnApprox b S F‖ ≤ Real.sqrt (tailColumnSquareSum b S F) := by
  classical
  let R : H →L[ℂ] H := S - finiteColumnApprox b S F
  have hcol (i : w) : R (b i) = if i ∈ F then 0 else S (b i) := by
    change S (b i) - finiteColumnApprox b S F (b i) = _
    rw [finiteColumnApprox_apply_basis]
    split_ifs <;> simp
  have hsq (i : w) : ‖R (b i)‖ ^ 2 =
      ((F : Set w)ᶜ).indicator (fun i => ‖S (b i)‖ ^ 2) i := by
    by_cases hi : i ∈ F <;> simp [hcol, Set.indicator_apply, hi]
  have hR : Summable (fun i : w => ‖R (b i)‖ ^ 2) :=
    (hS.indicator ((F : Set w)ᶜ)).congr (fun i => (hsq i).symm)
  have hsum : (∑' i : w, ‖R (b i)‖ ^ 2) = tailColumnSquareSum b S F := by
    change (∑' i : w, ‖R (b i)‖ ^ 2) =
      ∑' i : ↥((F : Set w)ᶜ), ‖S (b i.1)‖ ^ 2
    have hind := tsum_subtype ((F : Set w)ᶜ) (fun i : w => ‖S (b i)‖ ^ 2)
    exact (tsum_congr hsq).trans hind.symm
  change ‖R‖ ≤ _
  calc
    ‖R‖ ≤ Real.sqrt (∑' i : w, ‖R (b i)‖ ^ 2) :=
      opNorm_le_sqrt_column_square_sum b R hR
    _ = Real.sqrt (tailColumnSquareSum b S F) := by rw [hsum]

theorem norm_sub_finiteColumnApprox_sq_le {w : Set H} (b : HilbertBasis w ℂ H)
    (S : H →L[ℂ] H) (hS : Summable (fun i : w => ‖S (b i)‖ ^ 2)) (F : Finset w) :
    ‖S - finiteColumnApprox b S F‖ ^ 2 ≤ tailColumnSquareSum b S F := by
  have ht : 0 ≤ tailColumnSquareSum b S F := tsum_nonneg (fun _ => sq_nonneg _)
  calc
    ‖S - finiteColumnApprox b S F‖ ^ 2 ≤ (Real.sqrt (tailColumnSquareSum b S F)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2
        (norm_sub_finiteColumnApprox_le b S hS F)
    _ = tailColumnSquareSum b S F := Real.sq_sqrt ht

/-- The directed set is ALL finite subsets of w, with inclusion order, even if w is uncountable.
No cofinal Nat sequence is selected or asserted. -/
theorem tendsto_finiteColumnApprox {w : Set H} (b : HilbertBasis w ℂ H)
    (S : H →L[ℂ] H) (hS : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    Tendsto (finiteColumnApprox b S) (atTop : Filter (Finset w)) (𝓝 S) := by
  have ht : Tendsto (tailColumnSquareSum b S) (atTop : Filter (Finset w)) (𝓝 0) := by
    convert (tendsto_tsum_compl_atTop_zero (f := fun i : w => ‖S (b i)‖ ^ 2)) using 1
    funext F
    apply tsum_congr
    intro i
    rfl
  have hsq : Tendsto (fun F => ‖finiteColumnApprox b S F - S‖ ^ 2)
      (atTop : Filter (Finset w)) (𝓝 0) := by
    apply squeeze_zero (fun F => sq_nonneg _) ?_ ht
    intro F
    rw [norm_sub_rev]
    exact norm_sub_finiteColumnApprox_sq_le b S hS F
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

/-- Every Hilbert-Schmidt operator on a complete complex Hilbert space is compact. -/
theorem isCompactOperator_of_isHilbertSchmidt {S : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) : IsCompactOperator S := by
  rcases hS with ⟨w, b, hb⟩
  exact isCompactOperator_of_tendsto (tendsto_finiteColumnApprox b S hb)
    (Filter.Eventually.of_forall (isCompactOperator_finiteColumnApprox b S))

end HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positive trace-class consumer, preserving arbitrary complete complex H. -/
theorem isCompactOperator_of_nonneg_isTraceClass {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hpos : 0 ≤ T) : IsCompactOperator T := by
  let R : H →L[ℂ] H := CFC.sqrt T
  have hRhs : HilbertSchmidt.IsHilbertSchmidt R := by
    simpa only [R, CFC.abs_of_nonneg T hpos] using
      isHilbertSchmidt_sqrt_abs_of_isTraceClass hT
  have hR := HilbertSchmidt.isCompactOperator_of_isHilbertSchmidt hRhs
  have hRR : IsCompactOperator (R * R : H →L[ℂ] H) := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp] using hR.comp_clm R
  simpa only [R, CFC.sqrt_mul_sqrt_self T hpos] using hRR

/-- Every trace-class operator is compact, by the positive absolute-value
operator and its bounded polar factor. -/
theorem isCompactOperator_of_isTraceClass {T : H →L[ℂ] H}
    (hT : IsTraceClass T) : IsCompactOperator T := by
  have habstc : IsTraceClass (CFC.abs T) := by
    rcases hT with ⟨w, b, hb⟩
    refine ⟨w, b, ?_⟩
    simpa only [CFC.abs_of_nonneg (CFC.abs T) (CFC.abs_nonneg T)] using hb
  have habs := isCompactOperator_of_nonneg_isTraceClass habstc (CFC.abs_nonneg T)
  have hfactor : (Polar.polarFactor T * CFC.abs T : H →L[ℂ] H) = T := by
    simpa only [Polar.absOperator] using Polar.polarFactor_mul_absOperator T
  rw [← hfactor]
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp] using
    habs.clm_comp (Polar.polarFactor T)

#print axioms HilbertSchmidt.isCompactOperator_of_isHilbertSchmidt
#print axioms isCompactOperator_of_nonneg_isTraceClass
#print axioms isCompactOperator_of_isTraceClass
