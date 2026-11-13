/- GID: D5/S3/Quantum/GleasonComplexRepresentation
   generality: G
   mirror-B: D5/B/S3/Quantum/GleasonComplexRepresentation
   mirror-E: none(waiver:finite-dimensional-algebraic-proof)
   anchors: []
   utility: none -/

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/Quantum/blore2026gleason.md. Authors: Zayn Blore.
Adapted from zblore/csd-lean4 at 07e2273b0180e69b4cb8f84e9d2200faa19fe07d.
Imports, source grouping and exact-supplier applications use the receiving Mathlib pin.
Retire this transplant when the receiving pinned Mathlib supplies equivalent declarations.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Basic
import D5.S3.Quantum.GleasonFrameGeometry
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import D5.S3.Quantum.GleasonRealRepresentation
import D5.S3.QuadraticForms.ParallelogramConstruction
import Mathlib.Analysis.InnerProductSpace.LinearMap
open Matrix
open scoped ComplexConjugate
namespace Gleason
variable {N : ℕ}
structure IsQuadraticLike (q : EuclideanSpace ℂ (Fin N) → ℝ) : Prop where
  smul : ∀ (c : ℂ) (v : EuclideanSpace ℂ (Fin N)), q (c • v) = ‖c‖ ^ 2 * q v
  parallelogram : ∀ u v : EuclideanSpace ℂ (Fin N), q (u + v) + q (u - v) = 2 * q u + 2 * q v
  nonneg : ∀ v : EuclideanSpace ℂ (Fin N), 0 ≤ q v
  le_normSq : ∀ v : EuclideanSpace ℂ (Fin N), q v ≤ ‖v‖ ^ 2
def polar (q : EuclideanSpace ℂ (Fin N) → ℝ) (u v : EuclideanSpace ℂ (Fin N)) : ℝ :=
  q (u + v) - q (u - v)
noncomputable def sesq (q : EuclideanSpace ℂ (Fin N) → ℝ) (u v : EuclideanSpace ℂ (Fin N)) : ℂ :=
  ((polar q u v : ℝ) : ℂ) / 4 - Complex.I * ((polar q u (Complex.I • v) : ℝ) : ℂ) / 4
noncomputable def polarMatrix (q : EuclideanSpace ℂ (Fin N) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => sesq q (EuclideanSpace.single j (1:ℂ)) (EuclideanSpace.single k (1:ℂ))
namespace IsQuadraticLike
variable {q : EuclideanSpace ℂ (Fin N) → ℝ} (hq : IsQuadraticLike q)
include hq
theorem zero : q 0 = 0 := by
  have h := hq.smul 0 0
  simpa using h
theorem neg (v : EuclideanSpace ℂ (Fin N)) : q (-v) = q v := by
  have h := hq.smul (-1) v
  simpa using h
theorem polar_symm (u v : EuclideanSpace ℂ (Fin N)) : polar q u v = polar q v u := by
  have h : v - u = -(u - v) := by abel
  rw [polar, polar, h, hq.neg, add_comm]
theorem polar_zero_left (v : EuclideanSpace ℂ (Fin N)) : polar q 0 v = 0 := by
  rw [polar, zero_add, zero_sub, hq.neg, sub_self]
omit hq in
theorem polar_neg_right (u v : EuclideanSpace ℂ (Fin N)) :
    polar q u (-v) = - polar q u v := by
  rw [polar, polar, ← sub_eq_add_neg, sub_neg_eq_add]; ring
theorem polar_add_left (u w v : EuclideanSpace ℂ (Fin N)) :
    polar q (u + w) v = polar q u v + polar q w v := by
  let Q : QuadraticMap ℤ (EuclideanSpace ℂ (Fin N)) ℝ :=
    TauCeti.QuadraticMap.ofParallelogram (f := q)
      (smul_right_injective ℝ (by norm_num : (2 : ℕ) ≠ 0))
      (by intro x y; simpa only [two_nsmul, two_mul] using hq.parallelogram x y)
  have h := Q.polar_add_left u w v
  change q (u + w + v) - q (u + w) - q v =
    (q (u + v) - q u - q v) + (q (w + v) - q w - q v) at h
  have h₁ := hq.parallelogram (u + w) v
  have h₂ := hq.parallelogram u v
  have h₃ := hq.parallelogram w v
  simp only [polar]
  linarith
theorem polar_smul_real (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    polar q (((t : ℝ) : ℂ) • u) v = t * polar q u v := by
  have hadd : ∀ s r : ℝ, polar q ((((s + r : ℝ)) : ℂ) • u) v
      = polar q (((s : ℝ) : ℂ) • u) v + polar q (((r : ℝ) : ℂ) • u) v := by
    intro s r
    rw [show (((s + r : ℝ)) : ℂ) • u = ((s : ℝ) : ℂ) • u + ((r : ℝ) : ℂ) • u from by
      push_cast; rw [add_smul], hq.polar_add_left]
  have hbound : ∀ s : ℝ, |s| ≤ 1 → |polar q (((s : ℝ) : ℂ) • u) v| ≤ (‖u‖ + ‖v‖) ^ 2 := by
    intro s hs
    have hsn : ‖((s : ℝ) : ℂ) • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [norm_nonneg u, abs_nonneg s]
    have hp : ‖((s:ℝ):ℂ) • u + v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_add_le _ _) (by linarith)
    have hm : ‖((s:ℝ):ℂ) • u - v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_sub_le _ _) (by linarith)
    have h1 := hq.nonneg (((s:ℝ):ℂ) • u + v)
    have h2 := hq.nonneg (((s:ℝ):ℂ) • u - v)
    have h3 := hq.le_normSq (((s:ℝ):ℂ) • u + v)
    have h4 := hq.le_normSq (((s:ℝ):ℂ) • u - v)
    rw [abs_le, polar]
    constructor
    · nlinarith [norm_nonneg (((s:ℝ):ℂ) • u - v), norm_nonneg u, norm_nonneg v]
    · nlinarith [norm_nonneg (((s:ℝ):ℂ) • u + v), norm_nonneg u, norm_nonneg v]
  have hlin := additive_bounded_linear (fun s : ℝ => polar q (((s : ℝ) : ℂ) • u) v) hadd
    hbound t
  simpa using hlin
omit hq in
theorem sesq_zero_right (u : EuclideanSpace ℂ (Fin N)) : sesq q u 0 = 0 := by
  simp [sesq, polar]
theorem polar_add_right (u v w : EuclideanSpace ℂ (Fin N)) :
    polar q u (v + w) = polar q u v + polar q u w := by
  rw [hq.polar_symm u (v + w), hq.polar_add_left, hq.polar_symm v u, hq.polar_symm w u]
theorem polar_smul_real_right (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    polar q u (((t : ℝ) : ℂ) • v) = t * polar q u v := by
  rw [hq.polar_symm u (((t : ℝ) : ℂ) • v), hq.polar_smul_real, hq.polar_symm v u]
theorem sesq_add_right (u v w : EuclideanSpace ℂ (Fin N)) :
    sesq q u (v + w) = sesq q u v + sesq q u w := by
  simp only [sesq, smul_add, hq.polar_add_right]
  push_cast
  ring
theorem sesq_smul_real_right (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u (((t : ℝ) : ℂ) • v) = (t : ℂ) * sesq q u v := by
  have hcomm : Complex.I • (((t : ℝ) : ℂ) • v) = ((t : ℝ) : ℂ) • (Complex.I • v) :=
    smul_comm _ _ _
  simp only [sesq, hcomm, hq.polar_smul_real_right]
  push_cast
  ring
omit hq in
theorem sesq_smul_I_right (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u (Complex.I • v) = Complex.I * sesq q u v := by
  have hII : Complex.I • (Complex.I • v) = -v := by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  simp only [sesq, hII, polar_neg_right]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring
theorem sesq_smul_right (c : ℂ) (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u (c • v) = c * sesq q u v := by
  have hdecomp : c • v = ((c.re : ℝ) : ℂ) • v + ((c.im : ℝ) : ℂ) • (Complex.I • v) := by
    rw [smul_smul, ← add_smul]
    congr 1
    exact (Complex.re_add_im c).symm
  rw [hdecomp, hq.sesq_add_right, hq.sesq_smul_real_right, hq.sesq_smul_real_right,
    sesq_smul_I_right]
  have hc : ((c.re : ℝ) : ℂ) + ((c.im : ℝ) : ℂ) * Complex.I = c := Complex.re_add_im c
  linear_combination sesq q u v * hc
theorem sesq_conj_symm (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q v u = (starRingEnd ℂ) (sesq q u v) := by
  have h1 : q (v + Complex.I • u) = q (u - Complex.I • v) := by
    have hI : Complex.I • (u - Complex.I • v) = v + Complex.I • u := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add, add_comm]
    rw [← hI, hq.smul]
    simp
  have h2 : q (v - Complex.I • u) = q (u + Complex.I • v) := by
    have hI : (-Complex.I) • (u + Complex.I • v) = v - Complex.I • u := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        add_comm, ← sub_eq_add_neg]
    rw [← hI, hq.smul]
    simp
  have hpol : polar q v (Complex.I • u) = - polar q u (Complex.I • v) := by
    simp only [polar, h1, h2]
    ring
  simp only [sesq, hq.polar_symm v u, hpol]
  simp only [map_sub, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring
theorem sesq_self (v : EuclideanSpace ℂ (Fin N)) : sesq q v v = ((q v : ℝ) : ℂ) := by
  have hdiag : polar q v v = 4 * q v := by
    have h2 : v + v = ((2 : ℝ) : ℂ) • v := by push_cast; rw [two_smul]
    have hn2 : ‖((2 : ℝ) : ℂ)‖ ^ 2 = 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [polar, h2, hq.smul, hn2, sub_self, hq.zero, sub_zero]
  have hIv : polar q v (Complex.I • v) = 0 := by
    have hneg : (-Complex.I) • (v + Complex.I • v) = v - Complex.I • v := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        add_comm, ← sub_eq_add_neg]
    rw [polar, ← hneg, hq.smul]
    simp
  rw [sesq, hdiag, hIv]
  push_cast
  ring
theorem sesq_sum_right {ι : Type*} (u : EuclideanSpace ℂ (Fin N)) (s : Finset ι) (c : ι → ℂ)
    (e : ι → EuclideanSpace ℂ (Fin N)) :
    sesq q u (∑ i ∈ s, c i • e i) = ∑ i ∈ s, c i * sesq q u (e i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [sesq_zero_right]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hq.sesq_add_right, hq.sesq_smul_right, ih]
theorem sesq_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (e : ι → EuclideanSpace ℂ (Fin N)) (w : EuclideanSpace ℂ (Fin N)) :
    sesq q (∑ i ∈ s, c i • e i) w = ∑ i ∈ s, (starRingEnd ℂ) (c i) * sesq q (e i) w := by
  rw [hq.sesq_conj_symm w (∑ i ∈ s, c i • e i), hq.sesq_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  exact (hq.sesq_conj_symm w (e i)).symm
theorem polarMatrix_isHermitian : (polarMatrix q).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, polarMatrix, Matrix.of_apply, Complex.star_def]
  exact (hq.sesq_conj_symm (EuclideanSpace.single k (1:ℂ))
    (EuclideanSpace.single j (1:ℂ))).symm
omit hq in
theorem _root_.Gleason.euclidean_sum_single (v : EuclideanSpace ℂ (Fin N)) :
    ∑ i, (v i) • (EuclideanSpace.single i (1:ℂ)) = v := by
  ext j
  simp
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
theorem sesq_eq_dotProduct (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u v = star (⇑u) ⬝ᵥ (polarMatrix q *ᵥ (⇑v)) := by
  conv_lhs => rw [← euclidean_sum_single u, ← euclidean_sum_single v]
  rw [hq.sesq_sum_left]
  simp only [hq.sesq_sum_right, dotProduct, Pi.star_apply, Matrix.mulVec, polarMatrix,
    Matrix.of_apply, Finset.mul_sum, Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
theorem eq_dotProduct (v : EuclideanSpace ℂ (Fin N)) :
    ((q v : ℝ) : ℂ) = star (⇑v) ⬝ᵥ (polarMatrix q *ᵥ (⇑v)) := by
  rw [← hq.sesq_self v, hq.sesq_eq_dotProduct]
end IsQuadraticLike
theorem matrix_eq_zero_of_quadForm_zero {D : Matrix (Fin N) (Fin N) ℂ}
    (hQ : ∀ x : Fin N → ℂ, star x ⬝ᵥ (D *ᵥ x) = 0) : D = 0 := by
  have hlin : Matrix.toEuclideanLin D = 0 :=
    (LinearMap.inner_map_self_eq_zero (Matrix.toEuclideanLin D)).mp (fun x => by
      rw [inner_conj_symm]
      have hx : inner ℂ x (Matrix.toEuclideanLin D x) = 0 := by
        simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
          Matrix.toLpLin_apply, dotProduct_comm] using hQ (⇑x)
      rw [hx, map_zero])
  exact Matrix.toEuclideanLin.injective (by simpa using hlin)
theorem trace_mul_isHermitian_real {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (starRingEnd ℂ) ((A * B).trace) = (A * B).trace := by
  calc (starRingEnd ℂ) ((A * B).trace)
      = ((A * B)ᴴ).trace := by rw [starRingEnd_apply, ← Matrix.trace_conjTranspose]
    _ = (B * A).trace := by rw [Matrix.conjTranspose_mul, hA.eq, hB.eq]
    _ = (A * B).trace := Matrix.trace_mul_comm _ _
theorem trace_mul_vecMulVec (R : Matrix (Fin N) (Fin N) ℂ) (v : EuclideanSpace ℂ (Fin N)) :
    (R * Matrix.vecMulVec (⇑v) (star ⇑v)).trace = star (⇑v) ⬝ᵥ (R *ᵥ (⇑v)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Pi.star_apply, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
end Gleason
open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace
namespace Gleason
variable {N : ℕ}
lemma star_smul_dotProduct_mulVec_smul (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    star (c • x) ⬝ᵥ (A *ᵥ (c • x)) = (conj c * c) * (star x ⬝ᵥ (A *ᵥ x)) := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    Complex.star_def]
  ring
lemma conj_star_dotProduct_mulVec {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (x : Fin N → ℂ) : conj (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) := by
  rw [starRingEnd_apply, ← star_dotProduct, star_mulVec, ← dotProduct_mulVec, hA.eq]
lemma ofReal_re_star_dotProduct_mulVec {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (x : Fin N → ℂ) : (((star x ⬝ᵥ (A *ᵥ x)).re : ℝ) : ℂ) = star x ⬝ᵥ (A *ᵥ x) :=
  Complex.conj_eq_iff_re.mp (conj_star_dotProduct_mulVec hA x)
lemma exists_norm_one_smul_eq {x : Fin N → ℂ} (hx : x ≠ 0) :
    ∃ (r : ℝ) (v : EuclideanSpace ℂ (Fin N)), 0 < r ∧ ‖v‖ = 1 ∧ x = ((r : ℝ) : ℂ) • ⇑v := by
  set X : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 x with hX
  have hX0 : X ≠ 0 := by
    intro h
    apply hx
    have := congrArg (fun y : EuclideanSpace ℂ (Fin N) => (⇑y : Fin N → ℂ)) h
    simpa [hX] using this
  have hn : 0 < ‖X‖ := norm_pos_iff.mpr hX0
  refine ⟨‖X‖, ((‖X‖⁻¹ : ℝ) : ℂ) • X, hn, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  · change x = ((‖X‖ : ℝ) : ℂ) • (((‖X‖⁻¹ : ℝ) : ℂ) • x)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
theorem posSemidef_of_sphere_nonneg {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (h : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ = 1 → 0 ≤ (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re) :
    A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, (Complex.conj_eq_iff_im.mp (conj_star_dotProduct_mulVec hA x)).symm⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨r, v, hr, hv, rfl⟩ := exists_norm_one_smul_eq hx
  rw [star_smul_dotProduct_mulVec_smul, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (h v hv)
lemma star_single_dotProduct_mulVec_single (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    star (⇑(EuclideanSpace.single i (1 : ℂ))) ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℂ)))
      = A i i := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]
theorem trace_eq_sum_sphere (A : Matrix (Fin N) (Fin N) ℂ) :
    A.trace = ∑ i, star (⇑(EuclideanSpace.single i (1 : ℂ)))
      ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℂ))) := by
  simp only [star_single_dotProduct_mulVec_single, Matrix.trace, Matrix.diag_apply]
lemma ofReal_re_trace {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    (((A.trace).re : ℝ) : ℂ) = A.trace := by
  refine Complex.conj_eq_iff_re.mp ?_
  rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, hA.eq]
theorem eq_of_sphere_quadForm_eq {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    (h : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ = 1 →
      (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re = (star (⇑v) ⬝ᵥ (B *ᵥ ⇑v)).re) : A = B := by
  have hD : (A - B).IsHermitian := hA.sub hB
  have hsphere : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ = 1 →
      star (⇑v) ⬝ᵥ ((A - B) *ᵥ ⇑v) = 0 := by
    intro v hv
    rw [← ofReal_re_star_dotProduct_mulVec hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
      h v hv, sub_self, Complex.ofReal_zero]
  have hall : ∀ x : Fin N → ℂ, star x ⬝ᵥ ((A - B) *ᵥ x) = 0 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    obtain ⟨r, v, _, hv, rfl⟩ := exists_norm_one_smul_eq hx
    rw [star_smul_dotProduct_mulVec_smul, hsphere v hv, mul_zero]
  exact sub_eq_zero.mp (matrix_eq_zero_of_quadForm_zero hall)
theorem quadraticForm_on_sphere_to_density {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {f : EuclideanSpace ℂ (Fin N) → ℝ}
    (hf : ∀ v, ‖v‖ = 1 → f v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re)
    (h0 : ∀ v, ‖v‖ = 1 → 0 ≤ f v) (h1 : ∑ i, f (EuclideanSpace.single i (1 : ℂ)) = 1) :
    A.PosSemidef ∧ A.trace = 1 ∧ ∀ B : Matrix (Fin N) (Fin N) ℂ, B.IsHermitian →
      (∀ v, ‖v‖ = 1 → f v = (star (⇑v) ⬝ᵥ (B *ᵥ ⇑v)).re) → B = A := by
  have hsingle : ∀ i : Fin N, ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := fun i => by
    rw [PiLp.norm_single]; exact norm_one
  refine ⟨posSemidef_of_sphere_nonneg hA fun v hv => (hf v hv) ▸ h0 v hv, ?_, ?_⟩
  · have hs : ∑ i, (star (⇑(EuclideanSpace.single i (1 : ℂ)))
        ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℂ)))).re = 1 := by
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => (hf _ (hsingle i)).symm
    rw [← ofReal_re_trace hA, trace_eq_sum_sphere, Complex.re_sum, hs, Complex.ofReal_one]
  · intro B hB hfB
    exact eq_of_sphere_quadForm_eq hB hA fun v hv => by rw [← hfB v hv, hf v hv]
theorem _root_.Matrix.IsHermitian.eq_sum_eigenvalues_smul_rankOne {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) :
    A = ∑ i, hA.eigenvalues i • rankOne (hA.eigenvectorBasis i) := by
  calc A = A * ∑ i, rankOne (hA.eigenvectorBasis i) := by
        rw [sum_rankOne_orthonormalBasis, Matrix.mul_one]
    _ = ∑ i, hA.eigenvalues i • rankOne (hA.eigenvectorBasis i) := by
        rw [Matrix.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [rankOne, mul_vecMulVec, hA.mulVec_eigenvectorBasis, smul_vecMulVec]
theorem eigenvalues_eq_zero_or_one {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsStarProjection P)
    (hPh : P.IsHermitian) (i : Fin N) : hPh.eigenvalues i = 0 ∨ hPh.eigenvalues i = 1 := by
  set b := hPh.eigenvectorBasis with hb
  set l := hPh.eigenvalues i with hl
  have h1 : P *ᵥ (P *ᵥ ⇑(b i)) = (l * l) • ⇑(b i) := by
    rw [hPh.mulVec_eigenvectorBasis, Matrix.mulVec_smul, hPh.mulVec_eigenvectorBasis, smul_smul]
  have h2 : P *ᵥ (P *ᵥ ⇑(b i)) = l • ⇑(b i) := by
    rw [Matrix.mulVec_mulVec, hP.isIdempotentElem.eq, hPh.mulVec_eigenvectorBasis]
  have hne : (⇑(b i) : Fin N → ℂ) ≠ 0 := by
    intro h
    have := b.orthonormal.norm_eq_one i
    rw [show b i = 0 from by ext j; exact congrFun h j] at this
    simp at this
  have h3 : (l * l - l) • (⇑(b i) : Fin N → ℂ) = 0 := by
    rw [sub_smul, h1.symm.trans h2, sub_self]
  have h4 : l * l - l = 0 := (smul_eq_zero.mp h3).resolve_right hne
  have h5 : l * (l - 1) = 0 := by rw [← h4]; ring
  rcases mul_eq_zero.mp h5 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)
namespace ProjectionPackage
variable (OP : ProjectionPackage N)
lemma isStarProjection_smul_rankOne {l : ℝ} (hl : l = 0 ∨ l = 1)
    {b : EuclideanSpace ℂ (Fin N)} (hb : ‖b‖ = 1) : IsStarProjection (l • rankOne b) := by
  rcases hl with rfl | rfl
  · simp
  · simpa using isStarProjection_rankOne hb
lemma p_smul_rankOne {l : ℝ} (hl : l = 0 ∨ l = 1) (b : EuclideanSpace ℂ (Fin N)) :
    OP.p (l • rankOne b) = l * OP.frame b := by
  rcases hl with rfl | rfl
  · simp [OP.p_zero]
  · simp [frame]
theorem p_eq_re_trace {A : Matrix (Fin N) (Fin N) ℂ}
    (hf : ∀ v, ‖v‖ = 1 → OP.frame v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re)
    {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsStarProjection P) :
    OP.p P = ((A * P).trace).re := by
  have hPh : P.IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  set b := hPh.eigenvectorBasis with hb
  set l := hPh.eigenvalues with hl
  have hspec : P = ∑ i, l i • rankOne (b i) := hPh.eq_sum_eigenvalues_smul_rankOne
  have hl01 : ∀ i, l i = 0 ∨ l i = 1 := eigenvalues_eq_zero_or_one hP hPh
  have hunit : ∀ i, ‖b i‖ = 1 := b.orthonormal.norm_eq_one
  have hsum : OP.p P = ∑ i, l i * OP.frame (b i) := by
    rw [hspec, OP.p_sum _ (fun i => isStarProjection_smul_rankOne (hl01 i) (hunit i))
      (fun i j hij => by
        rw [smul_mul_smul_comm, rankOne_mul_rankOne_of_orthonormal b.orthonormal hij, smul_zero])]
    exact Finset.sum_congr rfl fun i _ => OP.p_smul_rankOne (hl01 i) (b i)
  rw [hsum]
  conv_rhs => rw [hspec, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf _ (hunit i), Matrix.mul_smul, Matrix.trace_smul, rankOne, trace_mul_vecMulVec,
    Complex.real_smul, Complex.re_ofReal_mul]
theorem existsUnique_density_of_frame_quadratic {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian)
    (hf : ∀ v, ‖v‖ = 1 → OP.frame v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re := by
  have hsingle : ∀ i : Fin N, ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := fun i => by
    rw [PiLp.norm_single]; exact norm_one
  obtain ⟨hpsd, htr, huniq⟩ := quadraticForm_on_sphere_to_density hA hf
    (fun v hv => OP.frame_nonneg hv)
    (by
      have h := OP.sum_frame_orthonormalBasis (EuclideanSpace.basisFun (Fin N) ℂ)
      simpa [EuclideanSpace.basisFun_apply] using h)
  refine ⟨A, ⟨hpsd, htr, fun P hP => OP.p_eq_re_trace hf hP⟩, ?_⟩
  rintro ρ ⟨hρ, -, hρp⟩
  refine huniq ρ hρ.isHermitian fun v hv => ?_
  rw [frame, hρp _ (isStarProjection_rankOne hv), rankOne, trace_mul_vecMulVec]
end ProjectionPackage
end Gleason
open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace
namespace Gleason
variable {N : ℕ}
noncomputable def invSqrtTwo : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
@[simp] lemma invSqrtTwo_re : invSqrtTwo.re = (Real.sqrt 2)⁻¹ := rfl
@[simp] lemma invSqrtTwo_im : invSqrtTwo.im = 0 := rfl
@[simp] lemma conj_invSqrtTwo : conj invSqrtTwo = invSqrtTwo := Complex.conj_ofReal _
lemma invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  rw [invSqrtTwo, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num
lemma norm_invSqrtTwo : ‖invSqrtTwo‖ = (Real.sqrt 2)⁻¹ := by
  rw [invSqrtTwo, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
noncomputable def crossTerm (f : EuclideanSpace ℂ (Fin N) → ℝ) (x y : EuclideanSpace ℂ (Fin N)) :
    ℝ :=
  f (invSqrtTwo • (x + y)) - (f x + f y) / 2
def IsRealPlaneRegular (f : EuclideanSpace ℂ (Fin N) → ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℂ (Fin N), Orthonormal ℂ ![x, y] → ∀ α β : ℝ, α ^ 2 + β ^ 2 = 1 →
    f ((α : ℂ) • x + (β : ℂ) • y) = f x * α ^ 2 + f y * β ^ 2 + 2 * α * β * crossTerm f x y
lemma norm_eq_one_of_inner_self {v : EuclideanSpace ℂ (Fin N)} (h : ⟪v, v⟫_ℂ = 1) : ‖v‖ = 1 := by
  have h1 : ‖v‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]
    simp
  nlinarith [norm_nonneg v]
lemma orthonormal_pair_iff {x y : EuclideanSpace ℂ (Fin N)} :
    Orthonormal ℂ ![x, y] ↔ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ⟪x, y⟫_ℂ = 0 := by
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0 0
      simp only [Matrix.cons_val_zero, ite_true] at this
      exact norm_eq_one_of_inner_self this
    · have := h 1 1
      simp only [Matrix.cons_val_one, ite_true] at this
      exact norm_eq_one_of_inner_self this
    · have := h 0 1
      simpa using this
  · rintro ⟨hx, hy, hxy⟩ i j
    fin_cases i <;> fin_cases j
    · simp [inner_self_eq_norm_sq_to_K, hx]
    · simpa using hxy
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Fin.zero_eta,
        Matrix.cons_val_zero, one_ne_zero, ite_false]
      rw [← inner_conj_symm, hxy, map_zero]
    · simp [inner_self_eq_norm_sq_to_K, hy]
lemma orthonormal_pair_smul {x y : EuclideanSpace ℂ (Fin N)} (h : Orthonormal ℂ ![x, y])
    {e : ℂ} (he : ‖e‖ = 1) : Orthonormal ℂ ![x, e • y] := by
  rw [orthonormal_pair_iff] at h ⊢
  refine ⟨h.1, ?_, ?_⟩
  · rw [norm_smul, he, one_mul, h.2.1]
  · rw [inner_smul_right, h.2.2, mul_zero]
lemma orthonormal_equator {x y : EuclideanSpace ℂ (Fin N)} (h : Orthonormal ℂ ![x, y]) :
    Orthonormal ℂ ![invSqrtTwo • (x + y),
      invSqrtTwo • (Complex.I • (x - y))] := by
  rw [orthonormal_pair_iff] at h ⊢
  obtain ⟨hx, hy, hxy⟩ := h
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have hs : invSqrtTwo * invSqrtTwo = 1 / 2 := invSqrtTwo_mul_self
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; simp
  have hyy : ⟪y, y⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hy]; simp
  refine ⟨norm_eq_one_of_inner_self ?_, norm_eq_one_of_inner_self ?_, ?_⟩
  · simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hxx, hyy, hxy,
      hyx, conj_invSqrtTwo]
    linear_combination (2 : ℂ) * hs
  · simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hxx, hyy, hxy,
      hyx, conj_invSqrtTwo, Complex.conj_I]
    linear_combination (2 : ℂ) * hs - (2 * invSqrtTwo * invSqrtTwo) * hI
  · simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right, hxx, hyy, hxy,
      hyx, conj_invSqrtTwo]
    ring
lemma rankOne_add_add_rankOne_sub (u v : EuclideanSpace ℂ (Fin N)) :
    rankOne (u + v) + rankOne (u - v) = (2 : ℂ) • rankOne u + (2 : ℂ) • rankOne v := by
  ext a c
  simp only [rankOne, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    PiLp.add_apply, PiLp.sub_apply, star_add, star_sub, smul_eq_mul]
  ring
lemma rankOne_real_smul (r : ℝ) (v : EuclideanSpace ℂ (Fin N)) :
    rankOne ((r : ℂ) • v) = ((r ^ 2 : ℝ) : ℂ) • rankOne v := by
  ext a c
  simp only [rankOne, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, PiLp.smul_apply,
    smul_eq_mul, Complex.star_def, map_mul, Complex.conj_ofReal]
  push_cast
  ring
lemma rankOne_equator (x y : EuclideanSpace ℂ (Fin N)) :
    rankOne (invSqrtTwo • (x + y))
        + rankOne (invSqrtTwo • (Complex.I • (x - y)))
      = rankOne x + rankOne y := by
  have hI : rankOne (invSqrtTwo • (Complex.I • (x - y)))
      = rankOne (invSqrtTwo • (x - y)) := by
    rw [smul_comm, rankOne_smul_of_norm_one (by simp)]
  have hs : ((((Real.sqrt 2)⁻¹ : ℝ) ^ 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring
  rw [hI, invSqrtTwo, rankOne_real_smul, rankOne_real_smul, ← smul_add,
    rankOne_add_add_rankOne_sub, hs, smul_add, smul_smul, smul_smul]
  norm_num
namespace ProjectionPackage
variable (OP : ProjectionPackage N)
lemma p_rankOne_add_rankOne {x y : EuclideanSpace ℂ (Fin N)} (h : Orthonormal ℂ ![x, y]) :
    OP.p (rankOne x + rankOne y) = OP.frame x + OP.frame y := by
  obtain ⟨hx, hy, hxy⟩ := orthonormal_pair_iff.mp h
  exact OP.additive _ _ (isStarProjection_rankOne hx) (isStarProjection_rankOne hy)
    (rankOne_mul_rankOne_of_inner_eq_zero hxy)
lemma frame_add_frame_eq {x y w w' : EuclideanSpace ℂ (Fin N)} (hxy : Orthonormal ℂ ![x, y])
    (hww : Orthonormal ℂ ![w, w']) (h : rankOne w + rankOne w' = rankOne x + rankOne y) :
    OP.frame w + OP.frame w' = OP.frame x + OP.frame y := by
  rw [← OP.p_rankOne_add_rankOne hxy, ← OP.p_rankOne_add_rankOne hww, h]
lemma exists_sq_eq_of_norm_one {e : ℂ} (he : ‖e‖ = 1) : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 = e := by
  refine ⟨e ^ ((2 : ℕ)⁻¹ : ℂ), ?_, Complex.cpow_nat_inv_pow e two_ne_zero⟩
  have h2 : ‖e ^ ((2 : ℕ)⁻¹ : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, Complex.cpow_nat_inv_pow e two_ne_zero, he]
  have := norm_nonneg (e ^ ((2 : ℕ)⁻¹ : ℂ))
  nlinarith
lemma equator_combination (x y : EuclideanSpace ℂ (Fin N)) {z : ℂ} (hz : ‖z‖ = 1) :
    ((z.re : ℝ) : ℂ) • (invSqrtTwo • (x + y))
        + ((z.im : ℝ) : ℂ) • (invSqrtTwo • (Complex.I • (x - y)))
      = z • (invSqrtTwo • (x + (conj z ^ 2) • y)) := by
  have hzz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      invSqrtTwo_re, invSqrtTwo_im, Complex.conj_re, Complex.conj_im, sq]
    linear_combination (-(Real.sqrt 2)⁻¹ * (z.re * (y i).re + z.im * (y i).im)) * hzz
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      invSqrtTwo_re, invSqrtTwo_im, Complex.conj_re, Complex.conj_im, sq]
    linear_combination (-(Real.sqrt 2)⁻¹ * (z.re * (y i).im - z.im * (y i).re)) * hzz
theorem crossTerm_phase (hreg : IsRealPlaneRegular OP.frame) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) {e : ℂ} (he : ‖e‖ = 1) :
    crossTerm OP.frame x (e • y)
      = (OP.frame (invSqrtTwo • (x + y))
          - OP.frame (invSqrtTwo • (Complex.I • (x - y)))) / 2 * e.re
        - crossTerm OP.frame (invSqrtTwo • (x + y))
          (invSqrtTwo • (Complex.I • (x - y))) * e.im := by
  set w := invSqrtTwo • (x + y) with hw
  set w' := invSqrtTwo • (Complex.I • (x - y)) with hw'
  obtain ⟨z, hz, hz2⟩ := exists_sq_eq_of_norm_one (e := conj e) (by simpa using he)
  have hzconj : conj z ^ 2 = e := by
    rw [← Complex.conj_conj e, ← hz2, map_pow]
  have hzz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  have hcomb := equator_combination x y hz
  rw [hzconj] at hcomb
  have hval : OP.frame (invSqrtTwo • (x + e • y))
      = OP.frame w * z.re ^ 2 + OP.frame w' * z.im ^ 2
        + 2 * z.re * z.im * crossTerm OP.frame w w' := by
    rw [← OP.frame_smul hz, ← hcomb]
    exact hreg w w' (orthonormal_equator hxy) z.re z.im hzz
  have hweight := OP.frame_add_frame_eq hxy (orthonormal_equator hxy) (rankOne_equator x y)
  have hey : OP.frame (e • y) = OP.frame y := OP.frame_smul he y
  have hre : e.re = z.re ^ 2 - z.im ^ 2 := by
    rw [← hzconj]; simp [sq, Complex.mul_re]
  have him : e.im = -(2 * z.re * z.im) := by
    rw [← hzconj]; simp [sq, Complex.mul_im]; ring
  rw [crossTerm, hval, hey, hre, him]
  have hw2 : OP.frame w' = OP.frame x + OP.frame y - OP.frame w := by linarith
  rw [hw2]
  linear_combination (OP.frame x + OP.frame y) / 2 * hzz
noncomputable def planeCoeff (x y : EuclideanSpace ℂ (Fin N)) : ℂ :=
  (((OP.frame (invSqrtTwo • (x + y))
      - OP.frame (invSqrtTwo • (Complex.I • (x - y)))) / 2 : ℝ) : ℂ)
    + Complex.I * ((crossTerm OP.frame (invSqrtTwo • (x + y))
      (invSqrtTwo • (Complex.I • (x - y))) : ℝ) : ℂ)
theorem frame_plane_unit (hreg : IsRealPlaneRegular OP.frame) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) {a b : ℂ} (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    OP.frame (a • x + b • y)
      = OP.frame x * ‖a‖ ^ 2 + OP.frame y * ‖b‖ ^ 2 + 2 * (conj a * b * OP.planeCoeff x y).re := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : ‖b‖ = 1 := by
      have : ‖b‖ ^ 2 = 1 := by simpa using hab
      nlinarith [norm_nonneg b]
    simp [OP.frame_smul hb, hb]
  rcases eq_or_ne b 0 with rfl | hb
  · have ha1 : ‖a‖ = 1 := by
      have : ‖a‖ ^ 2 = 1 := by simpa using hab
      nlinarith [norm_nonneg a]
    simp [OP.frame_smul ha1, ha1]
  set c : ℂ := conj a / (‖a‖ : ℂ) with hc
  set e : ℂ := (conj a * b) / ((‖a‖ : ℂ) * (‖b‖ : ℂ)) with he
  have ha0 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hb0 : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  have hca : c * a = (‖a‖ : ℂ) := by
    rw [hc, div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff ha0]
    ring
  have hcb : c * b = (‖b‖ : ℂ) * e := by
    rw [hc, he]
    field_simp
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr ha)]
  have hen : ‖e‖ = 1 := by
    rw [he, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_norm,
      div_self (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))]
  have hvec : c • (a • x + b • y) = ((‖a‖ : ℝ) : ℂ) • x + ((‖b‖ : ℝ) : ℂ) • (e • y) := by
    rw [smul_add, smul_smul, smul_smul, hca, hcb, ← smul_smul]
  have hmer := hreg x (e • y) (orthonormal_pair_smul hxy hen) ‖a‖ ‖b‖ hab
  rw [← OP.frame_smul hcn, hvec, hmer, OP.frame_smul hen, OP.crossTerm_phase hreg hxy hen]
  set q : ℂ := conj a * b with hq
  have hab' : ((‖a‖ : ℝ) : ℂ) * ((‖b‖ : ℝ) : ℂ) * e = q := by
    rw [he]; field_simp
  have hqre : q.re = ‖a‖ * ‖b‖ * e.re := by
    rw [← hab']; simp [Complex.mul_re]
  have hqim : q.im = ‖a‖ * ‖b‖ * e.im := by
    rw [← hab']; simp [Complex.mul_im]
  rw [planeCoeff]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_im]
  rw [hqre, hqim]
  ring
noncomputable def ext (v : EuclideanSpace ℂ (Fin N)) : ℝ :=
  ‖v‖ ^ 2 * OP.frame (((‖v‖⁻¹ : ℝ) : ℂ) • v)
lemma ext_of_norm_one {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) : OP.ext v = OP.frame v := by
  simp [ext, hv]
@[simp] lemma ext_zero : OP.ext 0 = 0 := by simp [ext]
lemma norm_inv_smul_self {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
    inv_mul_cancel₀ hn.ne']
lemma ext_smul (c : ℂ) (v : EuclideanSpace ℂ (Fin N)) : OP.ext (c • v) = ‖c‖ ^ 2 * OP.ext v := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hphase : ‖c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hcn.ne']
  have hvec : ((‖c • v‖⁻¹ : ℝ) : ℂ) • (c • v) = (c / (‖c‖ : ℂ)) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) := by
    rw [smul_smul, smul_smul, norm_smul, mul_inv]
    congr 1
    push_cast
    field_simp
  rw [ext, ext, hvec, OP.frame_smul hphase, norm_smul, mul_pow]
  ring
lemma ext_nonneg (v : EuclideanSpace ℂ (Fin N)) : 0 ≤ OP.ext v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  exact mul_nonneg (by positivity) (OP.frame_nonneg (norm_inv_smul_self hv))
lemma ext_le_normSq (v : EuclideanSpace ℂ (Fin N)) : OP.ext v ≤ ‖v‖ ^ 2 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  calc OP.ext v ≤ ‖v‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (OP.frame_le_one (norm_inv_smul_self hv)) (by positivity)
    _ = ‖v‖ ^ 2 := mul_one _
lemma norm_sq_smul_add_smul {x y : EuclideanSpace ℂ (Fin N)} (hxy : Orthonormal ℂ ![x, y])
    (a b : ℂ) : ‖a • x + b • y‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  obtain ⟨hx, hy, hxy'⟩ := orthonormal_pair_iff.mp hxy
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy', map_zero]
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; simp
  have hyy : ⟪y, y⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hy]; simp
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (a • x + b • y)
  rw [← h]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hxx, hyy, hxy',
    hyx, mul_zero, zero_add, add_zero, mul_one, Complex.sq_norm]
  simp [Complex.normSq_apply]
theorem ext_plane (hreg : IsRealPlaneRegular OP.frame) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) (a b : ℂ) :
    OP.ext (a • x + b • y)
      = OP.frame x * ‖a‖ ^ 2 + OP.frame y * ‖b‖ ^ 2 + 2 * (conj a * b * OP.planeCoeff x y).re := by
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp
  have hr2 : 0 < ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rcases not_and_or.mp h0 with ha | hb
    · have := norm_pos_iff.mpr ha; positivity
    · have := norm_pos_iff.mpr hb; positivity
  set r : ℝ := Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hr2
  have hrsq : r ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := Real.sq_sqrt hr2.le
  have hnorm : ‖a • x + b • y‖ = r := by
    rw [hr, ← norm_sq_smul_add_smul hxy a b, Real.sqrt_sq (norm_nonneg _)]
  have hunit : ‖a / (r : ℂ)‖ ^ 2 + ‖b / (r : ℂ)‖ ^ 2 = 1 := by
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_pow,
      div_pow, ← add_div, ← hrsq, div_self (pow_pos hrpos 2).ne']
  have hvec : ((‖a • x + b • y‖⁻¹ : ℝ) : ℂ) • (a • x + b • y)
      = (a / (r : ℂ)) • x + (b / (r : ℂ)) • y := by
    rw [hnorm, smul_add, smul_smul, smul_smul]
    push_cast
    congr 1 <;> congr 1 <;> ring
  have hpl := OP.frame_plane_unit hreg hxy hunit
  rw [ext, hvec, hpl, hnorm]
  have hra : ‖a / (r : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / r ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_pow]
  have hrb : ‖b / (r : ℂ)‖ ^ 2 = ‖b‖ ^ 2 / r ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_pow]
  have hq : (conj (a / (r : ℂ)) * (b / (r : ℂ)) * OP.planeCoeff x y).re
      = (conj a * b * OP.planeCoeff x y).re / r ^ 2 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, div_mul_eq_mul_div, ← sq,
      ← Complex.ofReal_pow, Complex.div_ofReal_re]
  rw [hra, hrb, hq]
  field_simp
lemma ext_parallelogram_plane (hreg : IsRealPlaneRegular OP.frame)
    {x y : EuclideanSpace ℂ (Fin N)} (hxy : Orthonormal ℂ ![x, y]) (a b a' b' : ℂ) :
    OP.ext ((a + a') • x + (b + b') • y) + OP.ext ((a - a') • x + (b - b') • y)
      = 2 * OP.ext (a • x + b • y) + 2 * OP.ext (a' • x + b' • y) := by
  simp only [OP.ext_plane hreg hxy, Complex.sq_norm, Complex.normSq_apply, map_add, map_sub,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring
theorem ext_parallelogram (hreg : IsRealPlaneRegular OP.frame) (u v : EuclideanSpace ℂ (Fin N)) :
    OP.ext (u + v) + OP.ext (u - v) = 2 * OP.ext u + 2 * OP.ext v := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hneg : OP.ext (-v) = OP.ext v := by
      have := OP.ext_smul (-1) v
      simpa using this
    simp [hneg]
    ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖u‖ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : EuclideanSpace ℂ (Fin N), x = ((r⁻¹ : ℝ) : ℂ) • u := ⟨_, rfl⟩
  have hun : 0 < r := hr ▸ norm_pos_iff.mpr hu
  have hxn : ‖x‖ = 1 := by rw [hx, hr]; exact norm_inv_smul_self hu
  have hux : u = ((r : ℝ) : ℂ) • x := by
    rw [hx, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hun.ne', Complex.ofReal_one,
      one_smul]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ⟪x, v⟫_ℂ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ (Fin N), w = v - c • x := ⟨_, rfl⟩
  have hxw : ⟪x, w⟫_ℂ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hxn, hc]
    simp
  rcases eq_or_ne w 0 with hw0 | hw0
  ·
    have hv : v = c • x := by
      rw [hw] at hw0
      exact sub_eq_zero.mp hw0
    have e1 : u + v = (((r : ℝ) : ℂ) + c) • x := by rw [hv, hux, add_smul]
    have e2 : u - v = (((r : ℝ) : ℂ) - c) • x := by rw [hv, hux, sub_smul]
    rw [e1, e2, hv, hux, OP.ext_smul, OP.ext_smul, OP.ext_smul, OP.ext_smul]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · obtain ⟨s', hs'⟩ : ∃ s' : ℝ, s' = ‖w‖ := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℂ (Fin N), y = ((s'⁻¹ : ℝ) : ℂ) • w := ⟨_, rfl⟩
    have hwn : 0 < s' := hs' ▸ norm_pos_iff.mpr hw0
    have hyn : ‖y‖ = 1 := by rw [hy, hs']; exact norm_inv_smul_self hw0
    have hxy : Orthonormal ℂ ![x, y] := by
      rw [orthonormal_pair_iff]
      refine ⟨hxn, hyn, ?_⟩
      rw [hy, inner_smul_right, hxw, mul_zero]
    have hwy : w = ((s' : ℝ) : ℂ) • y := by
      rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hwn.ne', Complex.ofReal_one,
        one_smul]
    have hv : v = c • x + ((s' : ℝ) : ℂ) • y := by
      rw [← hwy, hw]; abel
    have e1 : u + v = (((r : ℝ) : ℂ) + c) • x + ((s' : ℝ) : ℂ) • y := by
      rw [hux, hv, add_smul]; abel
    have e2 : u - v = (((r : ℝ) : ℂ) - c) • x + (-((s' : ℝ) : ℂ)) • y := by
      rw [hux, hv, sub_smul, neg_smul]; abel
    have key := OP.ext_parallelogram_plane hreg hxy ((r : ℝ) : ℂ) 0 c ((s' : ℝ) : ℂ)
    rw [zero_add, zero_sub, zero_smul, add_zero] at key
    rw [e1, e2, key]
    conv_rhs => rw [hux, hv]
theorem isQuadraticLike_ext (hreg : IsRealPlaneRegular OP.frame) : IsQuadraticLike OP.ext :=
  ⟨OP.ext_smul, OP.ext_parallelogram hreg, OP.ext_nonneg, OP.ext_le_normSq⟩
theorem exists_isHermitian_of_isRealPlaneRegular (hreg : IsRealPlaneRegular OP.frame) :
    ∃ A : Matrix (Fin N) (Fin N) ℂ, A.IsHermitian ∧
      ∀ v, ‖v‖ = 1 → OP.frame v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re := by
  have hq := OP.isQuadraticLike_ext hreg
  refine ⟨polarMatrix OP.ext, hq.polarMatrix_isHermitian, fun v hv => ?_⟩
  rw [← OP.ext_of_norm_one hv, ← Complex.ofReal_re (OP.ext v), hq.eq_dotProduct v]
lemma exists_orthonormal_triple (hN : 3 ≤ N) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) :
    ∃ z : EuclideanSpace ℂ (Fin N), Orthonormal ℂ ![x, y, z] := by
  classical
  obtain ⟨hx, hy, hxy'⟩ := orthonormal_pair_iff.mp hxy
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy', map_zero]
  have hne : x ≠ y := by
    intro h
    rw [h, inner_self_eq_norm_sq_to_K, hy] at hxy'
    simp at hxy'
  have hset : Orthonormal ℂ ((↑) : ({x, y} : Set (EuclideanSpace ℂ (Fin N))) →
      EuclideanSpace ℂ (Fin N)) := by
    rw [orthonormal_subtype_iff_ite]
    intro v hv w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · simp [inner_self_eq_norm_sq_to_K, hx]
    · simp [hxy', hne]
    · simp [hyx, hne.symm]
    · simp [inner_self_eq_norm_sq_to_K, hy]
  obtain ⟨u, b, hsub, hb⟩ := hset.exists_orthonormalBasis_extension
  have hcard : u.card = N := by
    have := Module.finrank_eq_card_basis b.toBasis
    rw [finrank_euclideanSpace_fin, Fintype.card_coe] at this
    exact this.symm
  have hxu : x ∈ u := hsub (by simp)
  have hyu : y ∈ u := hsub (by simp)
  have hrest : (u \ {x, y}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption)]
    have : ({x, y} : Finset (EuclideanSpace ℂ (Fin N))).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨z, hz⟩ := hrest
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hzu, hzx, hzy⟩ := hz
  have hbo := b.orthonormal
  rw [hb, orthonormal_subtype_iff_ite] at hbo
  refine ⟨z, ?_⟩
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.mk_one, Fin.zero_eta, Fin.isValue, Fin.reduceFinMk]
  · simp [inner_self_eq_norm_sq_to_K, hx]
  · simpa using hxy'
  · have := hbo x hxu z hzu
    simpa [Ne.symm hzx] using this
  · simpa [hne.symm] using hyx
  · simp [inner_self_eq_norm_sq_to_K, hy]
  · have := hbo y hyu z hzu
    simpa [Ne.symm hzy] using this
  · have := hbo z hzu x hxu
    simpa [hzx] using this
  · have := hbo z hzu y hyu
    simpa [hzy] using this
  · have := hbo z hzu z hzu
    simpa using this
lemma realCombination_two (e : Fin 3 → EuclideanSpace ℂ (Fin N)) (α β : ℝ) :
    realCombination e (WithLp.toLp 2 ![α, β, 0]) = (α : ℂ) • e 0 + (β : ℂ) • e 1 := by
  simp [realCombination, Fin.sum_univ_three]
theorem isRealPlaneRegular_of_triples (hN : 3 ≤ N)
    (h : ∀ e : Fin 3 → EuclideanSpace ℂ (Fin N), Orthonormal ℂ e →
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → OP.realRestrict e x = ⇑x ⬝ᵥ (A *ᵥ ⇑x)) :
    IsRealPlaneRegular OP.frame := by
  intro x y hxy α β hαβ
  obtain ⟨z, hxyz⟩ := exists_orthonormal_triple hN hxy
  obtain ⟨A, hA, hAf⟩ := h ![x, y, z] hxyz
  have hval : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      OP.frame ((a : ℂ) • x + (b : ℂ) • y)
        = A 0 0 * a ^ 2 + 2 * A 0 1 * a * b + A 1 1 * b ^ 2 := by
    intro a b hab
    have hn : ‖(WithLp.toLp 2 ![a, b, 0] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hab]
    have := hAf _ hn
    rw [realRestrict, realCombination_two] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, hA.apply 0 1]
    ring
  have h10 : OP.frame x = A 0 0 := by
    have := hval 1 0 (by norm_num)
    simpa using this
  have h01 : OP.frame y = A 1 1 := by
    have := hval 0 1 (by norm_num)
    simpa using this
  have hcross : crossTerm OP.frame x y = A 0 1 := by
    have hs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 + ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have := hval ((Real.sqrt 2)⁻¹) ((Real.sqrt 2)⁻¹) hs
    rw [crossTerm, invSqrtTwo, smul_add, this, h10, h01]
    linear_combination (A 0 0 + A 1 1 + 2 * A 0 1) / 2 * hs
  rw [hval α β hαβ, h10, h01, hcross]
  ring
end ProjectionPackage
end Gleason
open Matrix
open scoped ComplexOrder
namespace Gleason
def CoreLemma : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ) (W : ℝ), IsFrameFunction ℝ f W →
    (∀ x, ‖x‖ = 1 → 0 ≤ f x) →
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧ ∀ x, ‖x‖ = 1 → f x = ⇑x ⬝ᵥ (A *ᵥ ⇑x)
variable {N : ℕ}
theorem ProjectionPackage.gleason_representation_of_core (hcore : CoreLemma) (hN : 3 ≤ N)
    (OP : ProjectionPackage N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re := by
  have hreg : IsRealPlaneRegular OP.frame :=
    OP.isRealPlaneRegular_of_triples hN fun e he =>
      hcore (OP.realRestrict e) _ (OP.isFrameFunction_realRestrict he)
        fun x hx => OP.realRestrict_nonneg he hx
  obtain ⟨A, hA, hf⟩ := OP.exists_isHermitian_of_isRealPlaneRegular hreg
  exact OP.existsUnique_density_of_frame_quadratic hA hf
end Gleason
open Matrix
open scoped ComplexOrder
namespace Gleason
theorem coreLemma : CoreLemma := fun f _ hf h0 => frameFunction_regular_sphere f hf h0
variable {N : ℕ}
theorem ProjectionPackage.gleason_representation (OP : ProjectionPackage N) (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re :=
  OP.gleason_representation_of_core coreLemma hN
end Gleason
