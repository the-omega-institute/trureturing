/- GID: D5/S3/Fourier/Asymptotics/FiniteRankProjectionError
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/FiniteRankProjectionError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-dimensional compression gives a square-summable error with a dimension bound. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace D5.S3.Fourier.Asymptotics.FiniteRankProjectionError

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The finite-rank projection error has a summable square norm in every Hilbert basis,
with a bound independent of the dimension of the ambient Hilbert space. -/
theorem result {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] E)
    (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] :
    let P : E →L[𝕜] E := K.subtypeL.comp K.orthogonalProjectionOnto
    let Q := ContinuousLinearMap.id 𝕜 E - P
    let D := T - Q.comp (T.comp Q)
    Summable (fun i => ‖D (b i)‖ ^ 2) ∧
      Real.sqrt (∑' i, ‖D (b i)‖ ^ 2) ≤
        2 * Real.sqrt (Module.finrank 𝕜 K) * ‖T‖ := by
  classical
  let P := K.starProjection
  let Q := ContinuousLinearMap.id 𝕜 E - P
  let D := T - Q.comp (T.comp Q)
  change Summable (fun i => ‖D (b i)‖ ^ 2) ∧
    Real.sqrt (∑' i, ‖D (b i)‖ ^ 2) ≤ 2 * Real.sqrt (Module.finrank 𝕜 K) * ‖T‖
  let e := stdOrthonormalBasis 𝕜 K
  -- The finite output expansion turns each projected column into coefficient squares.
  have hproj (A : E →L[𝕜] E) :
      Summable (fun i => ‖P (A (b i))‖ ^ 2) ∧
        (∑' i, ‖P (A (b i))‖ ^ 2) ≤ (Module.finrank 𝕜 K : ℝ) * ‖A‖ ^ 2 := by
    let c := fun j i => ‖inner 𝕜 (b i) (A.adjoint (e j : E))‖ ^ 2
    have hc (j) : Summable (c j) := b.orthonormal.inner_products_summable _
    have heq (i) : ‖P (A (b i))‖ ^ 2 = ∑ j, c j i := by
      change ‖K.orthogonalProjectionOnto (A (b i))‖ ^ 2 = _
      rw [← e.sum_sq_norm_inner_right]
      apply Finset.sum_congr rfl
      intro j _
      change ‖inner 𝕜 (e j) (K.orthogonalProjectionOnto (A (b i)))‖ ^ 2 =
        ‖inner 𝕜 (b i) (A.adjoint (e j : E))‖ ^ 2
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
        ← A.adjoint_inner_left, norm_inner_symm]
    have hs : Summable (fun i => ∑ j, c j i) := summable_sum fun j _ => hc j
    constructor
    · exact hs.congr fun i => (heq i).symm
    · simp_rw [heq]
      rw [Summable.tsum_finsetSum (fun j _ => hc j)]
      calc
        ∑ j, ∑' i, c j i ≤ ∑ j : Fin (Module.finrank 𝕜 K), ‖A.adjoint (e j : E)‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => b.orthonormal.tsum_inner_products_le _
        _ ≤ ∑ _j : Fin (Module.finrank 𝕜 K), ‖A‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          have hj : ‖(e j : E)‖ = 1 := e.orthonormal.1 j
          have h := A.adjoint.le_opNorm (e j : E)
          rw [hj, mul_one, ContinuousLinearMap.adjoint.norm_map] at h
          exact pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = (Module.finrank 𝕜 K : ℝ) * ‖A‖ ^ 2 := by simp
  obtain ⟨hPT, hPTbound⟩ := hproj T
  obtain ⟨hP, hPbound⟩ := hproj (ContinuousLinearMap.id 𝕜 E)
  simp only [ContinuousLinearMap.id_apply] at hP hPbound
  have hPbound' : (∑' i, ‖P (b i)‖ ^ 2) ≤ (Module.finrank 𝕜 K : ℝ) := by
    have hid := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
    have hid0 := norm_nonneg (ContinuousLinearMap.id 𝕜 E)
    have hid2 : ‖ContinuousLinearMap.id 𝕜 E‖ ^ 2 ≤ 1 := by nlinarith
    apply hPbound.trans
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hid2 (Nat.cast_nonneg (Module.finrank 𝕜 K) : (0 : ℝ) ≤ _))
  have hQ (x : E) : ‖Q x‖ ≤ ‖x‖ := by
    change ‖(ContinuousLinearMap.id 𝕜 E - K.starProjection) x‖ ≤ ‖x‖
    rw [← K.starProjection_orthogonal]
    exact Kᗮ.norm_starProjection_apply_le x
  have hD (x : E) : D x = P (T x) + Q (T (P x)) := by
    simp only [D, Q, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_sub]
    abel
  have hbound (i) : ‖D (b i)‖ ^ 2 ≤
      2 * (‖P (T (b i))‖ ^ 2 + ‖T‖ ^ 2 * ‖P (b i)‖ ^ 2) := by
    have htri := norm_add_le (P (T (b i))) (Q (T (P (b i))))
    have hcomp := (hQ (T (P (b i)))).trans (T.le_opNorm (P (b i)))
    have hnorm : ‖D (b i)‖ ≤ ‖P (T (b i))‖ + ‖T‖ * ‖P (b i)‖ := by
      rw [hD]
      linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖P (T (b i))‖ - ‖T‖ * ‖P (b i)‖)]
  have hmajor : Summable (fun i =>
      2 * (‖P (T (b i))‖ ^ 2 + ‖T‖ ^ 2 * ‖P (b i)‖ ^ 2)) :=
    (hPT.add (hP.mul_left (‖T‖ ^ 2))).mul_left 2
  have hsum : Summable (fun i => ‖D (b i)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) hbound hmajor
  refine ⟨hsum, ?_⟩
  have htotal : (∑' i, ‖D (b i)‖ ^ 2) ≤
      4 * (Module.finrank 𝕜 K : ℝ) * ‖T‖ ^ 2 := by
    have h := hsum.tsum_le_tsum hbound hmajor
    rw [tsum_mul_left, hPT.tsum_add (hP.mul_left _), tsum_mul_left] at h
    have hp := mul_le_mul_of_nonneg_left hPbound' (sq_nonneg ‖T‖)
    nlinarith
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
    exact htotal

end D5.S3.Fourier.Asymptotics.FiniteRankProjectionError
