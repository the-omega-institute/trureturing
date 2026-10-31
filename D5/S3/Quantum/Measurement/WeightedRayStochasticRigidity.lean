/- GID: D5/S3/Quantum/Measurement/WeightedRayStochasticRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/WeightedRayStochasticRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stochastic unitary transport permutes pure rays and conserves grouped weights. -/

import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.QuantumStates.ZeroWeightSupportFace
import Mathlib.LinearAlgebra.Matrix.Stochastic

noncomputable section
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity

private theorem projection_psd {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) : P.PosSemidef := by
  simpa only [hP.eq, hPP] using Matrix.posSemidef_conjTranspose_mul_self P

private theorem pure_projection_eq {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hPt : trace P = 1) (hQt : trace Q = 1)
    (h : trace (P * (1 - Q)) = 0) : P = Q := by
  have hPQ : trace (P * Q) = 1 := by
    rw [mul_sub, mul_one, trace_sub, hPt] at h
    linear_combination -h
  have hQP : trace (Q * P) = 1 := (trace_mul_comm Q P).trans hPQ
  apply sub_eq_zero.mp
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rw [(hP.sub hQ).eq, sub_mul, mul_sub, mul_sub, trace_sub,
    trace_sub, trace_sub, hPP, hQQ, hPt, hQt, hPQ, hQP]
  ring

private theorem conjugate_projection {d : ℕ} (U : unitaryGroup (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (ht : trace P = 1) :
    (star (U : Matrix (Fin d) (Fin d) ℂ) * P * U).IsHermitian ∧
    (star (U : Matrix (Fin d) (Fin d) ℂ) * P * U) *
      (star (U : Matrix (Fin d) (Fin d) ℂ) * P * U) =
      star (U : Matrix (Fin d) (Fin d) ℂ) * P * U ∧
    trace (star (U : Matrix (Fin d) (Fin d) ℂ) * P * U) = 1 := by
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul _ hP, ?_, ?_⟩
  · calc
      _ = star (U : Matrix (Fin d) (Fin d) ℂ) * P *
          ((U : Matrix (Fin d) (Fin d) ℂ) * star U) * P * U := by noncomm_ring
      _ = _ := by rw [Unitary.coe_mul_star_self]; simp only [mul_one, mul_assoc, hPP]
  · rw [trace_mul_cycle, Unitary.coe_mul_star_self, one_mul, ht]

/-- A single unitary and a single column-stochastic matrix transporting a finite
weighted family of normalized pure projections induce one permutation of the
distinct rays. The total weight of each repeated-ray group is conserved. -/
theorem weighted_ray_transport {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {d : ℕ}
    (g : ι → κ) (hg : Function.Surjective g)
    (P : κ → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).IsHermitian) (hPP : ∀ k, P k * P k = P k)
    (ht : ∀ k, trace (P k) = 1) (hPinj : Function.Injective P)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (U : unitaryGroup (Fin d) ℂ) (T : Matrix ι ι ℝ)
    (hT : T ∈ colStochastic ℝ ι)
    (hE : ∀ i, star (U : Matrix (Fin d) (Fin d) ℂ) * (w i • P (g i)) * U =
      ∑ j, T i j • (w j • P (g j))) :
    ∃ π : Equiv.Perm κ,
      (∀ k, star (U : Matrix (Fin d) (Fin d) ℂ) * P k * U = P (π k)) ∧
      (∀ i j, T i j ≠ 0 → g j = π (g i)) ∧
      (∀ k, (∑ i with g i = k, w i) = ∑ j with g j = π k, w j) := by
  classical
  let Q (k : κ) := star (U : Matrix (Fin d) (Fin d) ℂ) * P k * U
  have hQ (k : κ) := conjugate_projection U (P k) (hP k) (hPP k) (ht k)
  have hm (i : ι) : w i = ∑ j, T i j * w j := by
    have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (trace A).re) (hE i)
    simpa only [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_sum, map_sum, hQ (g i) |>.2.2, ht, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.one_re, mul_one] using he
  have hs (i j : ι) (hij : T i j ≠ 0) : P (g j) = Q (g i) := by
    have hzero : ∑ j, (T i j * w j) * (trace (P (g j) * (1 - Q (g i)))).re = 0 := by
      have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ =>
        (trace (A * (1 - Q (g i)))).re) (hE i)
      have hqq : Q (g i) * (1 - Q (g i)) = 0 := by
        rw [mul_sub, mul_one, hQ (g i) |>.2.1, sub_self]
      have hel : star (U : Matrix (Fin d) (Fin d) ℂ) * (w i • P (g i)) * U =
          w i • Q (g i) := by simp [Q]
      rw [hel, smul_mul, hqq, smul_zero, trace_zero, Complex.zero_re] at he
      simpa only [sum_mul, trace_sum, map_sum, smul_mul, trace_smul,
        smul_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero] using he.symm
    have hn (j : ι) : 0 ≤ (trace (P (g j) * (1 - Q (g i)))).re :=
      RHLinalg.trace_mul_nonneg_of_posSemidef
        (projection_psd _ (hP _) (hPP _))
        (D5.S3.Quantum.Measurement.AntidistinguishabilityGram.hermitian_projection_complement_psd
          _ (hQ _).1 (hQ _).2.1)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (mul_nonneg (hT.1 _ _) (hw j).le) (hn j))).mp hzero j (mem_univ j)
    have hzre : (trace (P (g j) * (1 - Q (g i)))).re = 0 :=
      (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hij (hw j).ne')
    have hzcomplex : trace (P (g j) * (1 - Q (g i))) = 0 := by
      have he : star (trace (P (g j) * (1 - Q (g i)))) =
          trace (P (g j) * (1 - Q (g i))) := by
        rw [← trace_conjTranspose, conjTranspose_mul, (hP _).eq,
          (Matrix.isHermitian_one.sub (hQ _).1).eq, trace_mul_comm]
      have hi := congrArg Complex.im he
      simp only [Complex.star_def, Complex.conj_im] at hi
      exact Complex.ext hzre (by simp only [Complex.zero_im]; linarith)
    exact pure_projection_eq _ _ (hP _) (hQ _).1 (hPP _) (hQ _).2.1 (ht _) (hQ _).2.2 hzcomplex
  have hex (k : κ) : ∃ l, Q k = P l := by
    obtain ⟨i, rfl⟩ := hg k
    have hj : ∃ j, T i j ≠ 0 := by
      by_contra h
      push_neg at h
      have hz : w i = 0 := by simpa [h] using hm i
      exact (hw i).ne' hz
    obtain ⟨j, hj⟩ := hj
    exact ⟨g j, (hs i j hj).symm⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro k l hkl
    have he : Q k = Q l := (hf k).trans ((congrArg P hkl).trans (hf l).symm)
    apply hPinj
    have he' := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ =>
      (U : Matrix (Fin d) (Fin d) ℂ) * A * star U) he
    simpa only [Q, ← mul_assoc, Unitary.coe_mul_star_self, one_mul,
      mul_assoc, Unitary.coe_mul_star_self, mul_one] using he'
  let π : Equiv.Perm κ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hsupport (i j : ι) (hij : T i j ≠ 0) : g j = π (g i) :=
    hPinj ((hs i j hij).trans (hf (g i)))
  refine ⟨π, hf, hsupport, ?_⟩
  intro k
  calc
    (∑ i with g i = k, w i) = ∑ i with g i = k, ∑ j, T i j * w j := by
      apply sum_congr rfl; intro i _; exact hm i
    _ = ∑ j, (∑ i with g i = k, T i j) * w j := by
      rw [sum_comm]; apply sum_congr rfl; intro j _; rw [sum_mul]
    _ = ∑ j with g j = π k, w j := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      by_cases hj : g j = π k
      · rw [if_pos hj]
        have he : (∑ i with g i = k, T i j) = ∑ i, T i j := by
          symm
          apply sum_subset (filter_subset _ _) 
          intro i _ hi
          have hgi : g i ≠ k := by simpa only [mem_filter, mem_univ, true_and] using hi
          by_contra hn
          exact hgi (π.injective ((hsupport i j hn).symm.trans hj))
        rw [he, sum_col_of_mem_colStochastic hT, one_mul]
      · rw [if_neg hj]
        have he : (∑ i with g i = k, T i j) = 0 := by
          apply sum_eq_zero
          intro i hi
          have hi' : g i = k := (mem_filter.mp hi).2
          by_contra hn
          exact hj ((hsupport i j hn).trans (congrArg π hi'))
        rw [he, zero_mul]

end D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity
