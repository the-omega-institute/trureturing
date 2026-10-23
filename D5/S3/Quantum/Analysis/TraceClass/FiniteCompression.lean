/- GID: D5/S3/Quantum/Analysis/TraceClass/FiniteCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/FiniteCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite orthogonal compression and noncommuting trace-norm approximation. -/

import D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
open HilbertSchmidt

namespace TraceClassCompression
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Two-sided compression as a map on the genuine trace-norm carrier. -/
def compress (P : H →L[ℂ] H) : TraceClass H →L[ℂ] TraceClass H :=
  ({ toFun := fun rho => TraceClass.ofOperator (P * rho.1 * P)
       (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))
     map_add' := fun rho gamma => Subtype.ext (by
       change P * (rho.1 + gamma.1) * P = P * rho.1 * P + P * gamma.1 * P
       simp only [mul_add, add_mul])
     map_smul' := fun c rho => Subtype.ext (by
       change P * (c • rho.1) * P = c • (P * rho.1 * P)
       simp only [mul_smul_comm, smul_mul_assoc]) } :
    TraceClass H →ₗ[ℂ] TraceClass H).mkContinuous (‖P‖ * ‖P‖) (fun rho => by
      change traceNorm _ _ ≤ (‖P‖ * ‖P‖) * traceNorm _ _
      exact (traceNorm_mul_mul_le (TraceClass.isTraceClass_coe rho) _).trans_eq (by ring))

private theorem compress_norm_le (P : H →L[ℂ] H) (hP : ‖P‖ ≤ 1) (rho : TraceClass H) :
    ‖compress P rho‖ ≤ ‖rho‖ := by
  calc
    ‖compress P rho‖ ≤ (‖P‖ * ‖P‖) * ‖rho‖ := by
      change traceNorm (P * rho.1 * P) _ ≤ (‖P‖ * ‖P‖) * traceNorm rho.1 _
      exact (traceNorm_mul_mul_le (TraceClass.isTraceClass_coe rho) _).trans_eq (by ring)
    _ ≤ (1 * 1) * ‖rho‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul hP hP (norm_nonneg _) zero_le_one) (norm_nonneg _)
    _ = _ := by ring

private theorem range_left (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (x : LinearMap.range (compress U.starProjection).toLinearMap) :
    U.starProjection * x.1.1 = x.1.1 := by
  obtain ⟨rho, hrho⟩ := x.2
  have hx := congrArg (fun z : TraceClass H => z.1) hrho
  change U.starProjection * rho.1 * U.starProjection = x.1.1 at hx
  rw [← hx, ← mul_assoc, ← mul_assoc, U.isIdempotentElem_starProjection.eq]

private theorem range_right (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (x : LinearMap.range (compress U.starProjection).toLinearMap) :
    x.1.1 * U.starProjection = x.1.1 := by
  obtain ⟨rho, hrho⟩ := x.2
  have hx := congrArg (fun z : TraceClass H => z.1) hrho
  change U.starProjection * rho.1 * U.starProjection = x.1.1 at hx
  rw [← hx, mul_assoc, U.isIdempotentElem_starProjection.eq]

private def restrictRange (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    LinearMap.range (compress U.starProjection).toLinearMap →ₗ[ℂ] (U →ₗ[ℂ] U) where
  toFun x :=
    { toFun := fun u => ⟨x.1.1 (u : H), by
        rw [← Submodule.starProjection_eq_self_iff]
        exact DFunLike.congr_fun (range_left U x) (u : H)⟩
      map_add' := fun u v => Subtype.ext (map_add x.1.1 (u : H) v)
      map_smul' := fun c u => Subtype.ext (map_smul x.1.1 c (u : H)) }
  map_add' := fun x y => by ext u; rfl
  map_smul' := fun c x => by ext u; rfl

private theorem restrictRange_injective (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    Function.Injective (restrictRange U) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  ext z
  have hh := congrArg (fun f : U →ₗ[ℂ] U => (f ⟨U.starProjection z,
    U.starProjection_apply_mem z⟩ : H)) h
  change x.1.1 (U.starProjection z) = y.1.1 (U.starProjection z) at hh
  simpa only [← ContinuousLinearMap.mul_apply, range_right] using hh

/-- The compression range is finite dimensional with its inherited trace norm. -/
theorem finiteDimensional_range (U : Submodule ℂ H) [FiniteDimensional ℂ U] :
    FiniteDimensional ℂ (LinearMap.range (compress U.starProjection).toLinearMap) :=
  FiniteDimensional.of_injective (restrictRange U) (restrictRange_injective U)

/-- A single compact subset contains all compressions of the trace-norm unit ball. -/
theorem exists_compact_compressions (U : Submodule ℂ H) [FiniteDimensional ℂ U] :
    ∃ K : Set (TraceClass H), IsCompact K ∧
      ∀ rho : TraceClass H, ‖rho‖ ≤ 1 → compress U.starProjection rho ∈ K := by
  let V := LinearMap.range (compress U.starProjection).toLinearMap
  letI : FiniteDimensional ℂ V := finiteDimensional_range U
  refine ⟨Subtype.val '' Metric.closedBall (0 : V) 1,
    (isCompact_closedBall (0 : V) 1).image continuous_subtype_val, ?_⟩
  intro rho hrho
  refine ⟨⟨compress U.starProjection rho, ⟨rho, rfl⟩⟩, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖compress U.starProjection rho‖ ≤ 1
  exact
    (compress_norm_le _ U.starProjection_norm_le rho).trans hrho

/-- The span of finitely many members of a full Hilbert basis. -/
def finiteSpan {w : Set H} (b : HilbertBasis w ℂ H) (F : Finset w) : Submodule ℂ H :=
  Submodule.span ℂ (b '' (F : Set w))

instance finiteSpan_finiteDimensional {w : Set H} (b : HilbertBasis w ℂ H) (F : Finset w) :
    FiniteDimensional ℂ (finiteSpan b F) :=
  FiniteDimensional.span_of_finite ℂ (F.finite_toSet.image b)

private theorem finiteSpan_projection_basis {w : Set H} [DecidableEq w] (b : HilbertBasis w ℂ H)
    (F : Finset w) (i : w) :
    (finiteSpan b F).starProjection (b i) = if i ∈ F then b i else 0 := by
  classical
  split_ifs with hi
  · exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply (Submodule.starProjection_apply_eq_zero_iff (K := finiteSpan b F)).mpr
    rw [Submodule.mem_orthogonal']
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, hj, rfl⟩ := hx
        exact b.orthonormal.inner_eq_zero (by intro h; exact hi (h ▸ hj))
    | zero => simp
    | add x y hx hy hx' hy' => simp [inner_add_right, hx', hy']
    | smul c x hx hx' => simp [inner_smul_right, hx']

/-- Discarded diagonal mass; arbitrary zero fibers are retained in the index. -/
def tailMass {w : Set H} (b : HilbertBasis w ℂ H) (F : Finset w)
    (rho : TraceClass H) : ℝ := by
  classical
  exact ∑' i, if i ∈ F then 0 else QuantumLogEnergy.diagonal b rho i

private theorem sqrt_column {A : H →L[ℂ] H} (hA : 0 ≤ A) (v : H) :
    ‖CFC.sqrt A v‖ ^ 2 = (⟪v, A v⟫_ℂ).re := by
  let R := CFC.sqrt A
  have hR : IsSelfAdjoint R := .of_nonneg (CFC.sqrt_nonneg _)
  have hstar : ContinuousLinearMap.adjoint R = R :=
    (ContinuousLinearMap.star_eq_adjoint _).symm.trans hR
  have hinner : ⟪v, A v⟫_ℂ = ⟪R v, R v⟫_ℂ := by
    rw [← CFC.sqrt_mul_sqrt_self A hA]
    change ⟪v, R (R v)⟫_ℂ = _
    rw [← ContinuousLinearMap.adjoint_inner_left, hstar]
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- A noncommuting positive state differs from its finite compression by at most
twice the square root of the discarded diagonal mass. -/
theorem norm_sub_compress_le {w : Set H} (b : HilbertBasis w ℂ H) (F : Finset w)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1)
    (htrace : (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1) :
    ‖rho - compress (finiteSpan b F).starProjection rho‖ ≤ 2 * Real.sqrt (tailMass b F rho) := by
  classical
  let U := finiteSpan b F
  let P := U.starProjection
  let Q := Uᗮ.starProjection
  let R := CFC.sqrt rho.1
  have hRsa : IsSelfAdjoint R := .of_nonneg (CFC.sqrt_nonneg _)
  have hRstar : star R = R := hRsa.star_eq
  have hPstar : star P = P := (isSelfAdjoint_starProjection U).star_eq
  have hQstar : star Q = Q := (isSelfAdjoint_starProjection Uᗮ).star_eq
  have hQ : Q = 1 - P := U.starProjection_orthogonal'
  have hRR : R * R = rho.1 := CFC.sqrt_mul_sqrt_self _ hrho
  have hR : IsHilbertSchmidt R := by
    simpa only [CFC.abs_of_nonneg rho.1 hrho] using
      isHilbertSchmidt_sqrt_abs_of_isTraceClass (TraceClass.isTraceClass_coe rho)
  have hRQ : IsHilbertSchmidt (R * Q) := isHilbertSchmidt_mul_right hR
  have hQR : IsHilbertSchmidt (Q * R) := isHilbertSchmidt_mul_left hR
  have hPR : IsHilbertSchmidt (P * R) := isHilbertSchmidt_mul_left hR
  have htotal : (∑' i : w, ‖R (b i)‖ ^ 2) = 1 := by
    simpa only [CFC.abs_of_nonneg rho.1 hrho, QuantumLogEnergy.traceNorm_eq_re_trace _ hrho,
      htrace] using tsum_sqrt_abs_norm_sq_eq_traceNorm (TraceClass.isTraceClass_coe rho) b
  have htail : (∑' i : w, ‖(R * Q) (b i)‖ ^ 2) = tailMass b F rho := by
    apply tsum_congr
    intro i
    rw [ContinuousLinearMap.mul_apply, hQ, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, finiteSpan_projection_basis]
    split_ifs with hi
    · simp only [sub_self, map_zero, norm_zero]; norm_num
    · simpa only [sub_zero, R, QuantumLogEnergy.diagonal] using sqrt_column hrho (b i)
  have htail' : (∑' i : w, ‖(Q * R) (b i)‖ ^ 2) = tailMass b F rho := by
    have hh := (hasSum_norm_sq_apply_eq_adjoint b b
      (summable_norm_sq_apply_of_hilbertBasis w b hRQ)).tsum_eq
    have heq : ContinuousLinearMap.adjoint (R * Q) = Q * R := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, hRstar, hQstar]
    rwa [heq, htail] at hh
  have hPRsum : (∑' i : w, ‖(P * R) (b i)‖ ^ 2) ≤ 1 := by
    rw [← htotal]
    apply (summable_norm_sq_apply_of_hilbertBasis w b hPR).tsum_le_tsum _
      (summable_norm_sq_apply_of_hilbertBasis w b hR)
    intro i
    exact pow_le_pow_left₀ (norm_nonneg _) (U.norm_starProjection_apply_le (R (b i))) 2
  have hA := isTraceClass_mul_of_isHilbertSchmidt hQR hR
  have hB := isTraceClass_mul_of_isHilbertSchmidt hPR hRQ
  let A : TraceClass H := TraceClass.ofOperator ((Q * R) * R) hA
  let B : TraceClass H := TraceClass.ofOperator ((P * R) * (R * Q)) hB
  have hid : rho - compress P rho = A + B := by
    apply Subtype.ext
    change rho.1 - P * rho.1 * P = (Q * R) * R + (P * R) * (R * Q)
    rw [hQ, ← hRR]
    noncomm_ring
  rw [hid]
  calc
    ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    _ ≤ Real.sqrt (tailMass b F rho) * Real.sqrt 1 +
        Real.sqrt (∑' i : w, ‖(P * R) (b i)‖ ^ 2) * Real.sqrt (tailMass b F rho) := by
      exact add_le_add (by
        rw [TraceClass.norm_eq_traceNorm]
        simpa only [A, TraceClass.ofOperator_coe, htail', htotal] using
        traceNorm_mul_le_of_isHilbertSchmidt hQR hR hA b)
        (by
          rw [TraceClass.norm_eq_traceNorm]
          simpa only [B, TraceClass.ofOperator_coe, htail] using traceNorm_mul_le_of_isHilbertSchmidt hPR hRQ hB b)
    _ ≤ Real.sqrt (tailMass b F rho) * 1 + 1 * Real.sqrt (tailMass b F rho) := by
      rw [Real.sqrt_one]
      exact add_le_add_right (mul_le_mul_of_nonneg_right
        (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hPRsum) (Real.sqrt_nonneg _)) _
    _ = _ := by ring

end TraceClassCompression
