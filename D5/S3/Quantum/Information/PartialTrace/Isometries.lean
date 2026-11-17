/- GID: D5/S3/Quantum/Information/PartialTrace/Isometries
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/PartialTrace/Isometries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial trace covariance under finite product isometries. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation

/-! Partial trace covariance for product embeddings. -/

set_option autoImplicit false

noncomputable section

/- The declaration namespace preserves the AnticoherenceSpinCovariance API.
   proof_shape: bind-only; escape_witness: none; consumers: rotated_dilation,
   marginalRight_conjugate, partialTraceLeft_isometries,
   AnticoherenceTraceDistanceRefutation.dicke_split_partialTrace. -/
namespace D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance

open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
theorem partialTrace_isometries {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq j] (v : Matrix a i ℂ) (w : Matrix b j ℂ)
    (hw : wᴴ * w = 1) (z : Matrix (i × j) (i × j) ℂ) :
    partialTraceRight (Matrix.kronecker v w * z * (Matrix.kronecker v w)ᴴ) =
      v * partialTraceRight z * vᴴ := by
  have hb (k l : j) : (∑ d : b, w d k * star (w d l)) = if k = l then 1 else 0 := by
    have h := congrFun (congrFun hw l) k
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      mul_comm, eq_comm] using h
  ext x y
  dsimp only [Matrix.kronecker, Matrix.kroneckerMap]
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, star_mul]
  simp_rw [Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
    arg 2
    ext l
    rw [Finset.sum_comm]
    arg 2
    ext m
    rw [Finset.sum_comm]
  have he (k m : i) (l n : j) :
      (∑ d : b, v x m * w d n * z (m, n) (k, l) *
        (star (w d l) * star (v y k))) =
      v x m * z (m, l) (k, l) * star (v y k) * (if n = l then 1 else 0) := by
    calc
      _ = (v x m * z (m, n) (k, l) * star (v y k)) *
          (∑ d : b, w d n * star (w d l)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = _ := by rw [hb]; split_ifs with h <;> simp_all
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

end D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
