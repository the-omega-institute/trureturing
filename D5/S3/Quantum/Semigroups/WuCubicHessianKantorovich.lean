import D5.S3.Quantum.Semigroups.WuCubicConditionedHessian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order

/-! The relative mixed-generator estimate for the conditioned two-CAR Wu cubic Hessian.

The finite-dimensional part is written in spectral coordinates of
`S_B⁻¹ᐟ² S_M S_B⁻¹ᐟ²`.  The Wu-facing statement keeps the exact centered-generator
contraction as an input, while the Kantorovich and trace steps are proved here.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder ComplexConjugate MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicHessianKantorovich

open WuCubicOperatorBridge (Mat Occupation G GInv generator)
open WuCubicThermalBasis (Index degree coefficient)
open D5.S3.Quantum.Semigroups.WuCubicConditionedHessian (degree_contraction)

abbrev Entry := Occupation × Occupation

/- The two positive symmetrizers on the Hilbert space of matrices. -/
def S_M (M : Mat) (X : Mat) : Mat := ((1 / 2 : ℂ) • (M * X + X * M))

def S_B (B : Mat) (X : Mat) : Mat := ((1 / 2 : ℂ) • (B * X + X * B))

def vec (X : Mat) : Entry → ℂ := fun e => X e.1 e.2

theorem S_B_vec (b : Occupation → ℝ) (X : Mat) (e : Entry) :
    vec (S_B (diagonal (fun i => (b i : ℂ))) X) e =
      ((b e.1 + b e.2) / 2 : ℂ) * vec X e := by
  obtain ⟨i,j⟩ := e
  simp [S_B, vec, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
  ring

private theorem finite_kantorovich_sq {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 324 / 125)
    (hz : ∀ i, 0 ≤ z i) :
    64 * (∑ i, (p i) ^ 2 * z i) * (∑ i, z i) ≤
      81 * (∑ i, p i * z i) ^ 2 := by
  let A : ℝ := ∑ i, z i
  let B : ℝ := ∑ i, p i * z i
  let C : ℝ := ∑ i, (p i) ^ 2 * z i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _ => hz i)
  have hpoint (i : ι) : (p i) ^ 2 ≤ (449 / 125 : ℝ) * p i - 324 / 125 := by
    have h := mul_nonneg (sub_nonneg.mpr (hp i).1)
      (sub_nonneg.mpr (hp i).2)
    nlinarith only [h]
  have hC : C ≤ (449 / 125 : ℝ) * B - (324 / 125 : ℝ) * A := by
    dsimp only [C, B, A]
    calc
      _ ≤ ∑ i, ((449 / 125 : ℝ) * p i - 324 / 125) * z i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hpoint i) (hz i)
      _ = _ := by
        calc
          _ = ∑ i, ((449 / 125 : ℝ) * (p i * z i) - (324 / 125 : ℝ) * z i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hCA : 4 * (324 / 125 : ℝ) * C * A ≤
      (449 / 125 : ℝ) ^ 2 * B ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hC hA
    have hs : 0 ≤ ((449 / 125 : ℝ) * B - 2 * (324 / 125 : ℝ) * A) ^ 2 :=
      sq_nonneg _
    nlinarith only [hmul, hs]
  have hfactor : 16 * (449 / 125 : ℝ) ^ 2 ≤ 81 * (324 / 125 : ℝ) := by
    norm_num
  have hfac := mul_le_mul_of_nonneg_right hfactor (sq_nonneg B)
  have hmul : 64 * (324 / 125 : ℝ) * C * A ≤
      81 * (324 / 125 : ℝ) * B ^ 2 := by
    calc
      64 * (324 / 125 : ℝ) * C * A ≤
          16 * (449 / 125 : ℝ) ^ 2 * B ^ 2 := by nlinarith only [hCA]
      _ ≤ _ := hfac
  have hab : 0 < (324 / 125 : ℝ) := by norm_num
  have hfinal : 64 * C * A ≤ 81 * B ^ 2 := by
    apply le_of_mul_le_mul_left _ hab
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  simpa only [A, B, C] using hfinal

theorem kantorovich_324 {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (u : ι → ℂ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 324 / 125) :
    64 * (∑ i, (p i) ^ 2 * Complex.normSq (u i)) *
        (∑ i, Complex.normSq (u i)) ≤
      81 * (∑ i, p i * Complex.normSq (u i)) ^ 2 := by
  apply finite_kantorovich_sq p (fun i => Complex.normSq (u i)) hp
  exact fun i => Complex.normSq_nonneg _

theorem relative_trace_from_spectral_data {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (u v : EuclideanSpace ℂ ι) (cross q uNorm pUNorm vNorm : ℝ)
    (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 324 / 125)
    (hcross : cross = (∑ i, (conj ((p i : ℂ) * u i)) * v i).re)
    (hq : q = ∑ i, p i * Complex.normSq (u i))
    (hu : uNorm = ∑ i, Complex.normSq (u i))
    (hpu : pUNorm = ∑ i, (p i) ^ 2 * Complex.normSq (u i))
    (hv : vNorm = ∑ i, Complex.normSq (v i))
    (hcontract : vNorm ≤ uNorm) :
    3 * q + cross ≥ (15 / 8 : ℝ) * q := by
  have hu0 : 0 ≤ uNorm := by rw [hu]; exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hv0 : 0 ≤ vNorm := by rw [hv]; exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (by linarith [(hp i).1]) (Complex.normSq_nonneg _))
  have hkant := kantorovich_324 p u hp
  rw [← hq, ← hu, ← hpu] at hkant
  have hcs : cross ^ 2 ≤ pUNorm * vNorm := by
    rw [hcross]
    let pu : EuclideanSpace ℂ ι :=
      WithLp.toLp 2 (fun i => (p i : ℂ) * u i)
    have h := norm_inner_le_norm (𝕜 := ℂ) pu v
    have hinner : inner ℂ pu v =
        ∑ i, conj ((p i : ℂ) * u i) * v i := by
      simp [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [pu]
      rw [map_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      ring
    have hsum : ‖pu‖ ^ 2 = pUNorm := by
      rw [EuclideanSpace.norm_sq_eq]
      rw [hpu]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [pu]
      change ‖(p i : ℂ) * u i‖ ^ 2 = _
      rw [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have hsumv : ‖v‖ ^ 2 = vNorm := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa only [Complex.normSq_eq_norm_sq] using hv.symm
    rw [hinner] at h
    have habs : |(∑ i, conj ((p i : ℂ) * u i) * v i).re| ≤ ‖pu‖ * ‖v‖ :=
      (Complex.abs_re_le_norm _).trans h
    have hprod : cross ^ 2 ≤ (‖pu‖ * ‖v‖) ^ 2 := by
      rw [hcross]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr habs
    calc
      cross ^ 2 ≤ (‖pu‖ * ‖v‖) ^ 2 := hprod
      _ = ‖pu‖ ^ 2 * ‖v‖ ^ 2 := by ring
      _ = pUNorm * vNorm := by rw [hsum, hsumv]
  have hcv : pUNorm * vNorm ≤ pUNorm * uNorm := by
    have hpUNonneg : 0 ≤ pUNorm := by
      rw [hpu]
      exact Finset.sum_nonneg (fun i _ =>
        mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
    exact mul_le_mul_of_nonneg_left hcontract hpUNonneg
  have hbound : cross ^ 2 ≤ (81 / 64 : ℝ) * q ^ 2 := by
    have htrans := hcs.trans hcv
    calc
      cross ^ 2 ≤ pUNorm * uNorm := htrans
      _ ≤ (81 / 64 : ℝ) * q ^ 2 := by nlinarith only [hkant]
  nlinarith only [hbound, hq0, sq_nonneg (cross + (9 / 8 : ℝ) * q)]

/- The concrete trace operators used by the Wu application. -/
def centeredEmbeddedGenerator (r : ℝ) (W : Mat) : Mat :=
  G r * generator r (GInv r * W * GInv r) * G r - (3 : ℂ) • W

def mixedTrace (M W E : Mat) : ℝ :=
  (S_M M W * E).trace.re

structure WuSpectralCertificate (r : ℝ) (M W : Mat) where
  p : Fin 16 → ℝ
  u : EuclideanSpace ℂ (Fin 16)
  v : EuclideanSpace ℂ (Fin 16)
  cross : ℝ
  q : ℝ
  uNorm : ℝ
  pUNorm : ℝ
  vNorm : ℝ
  p_range : ∀ i, 1 ≤ p i ∧ p i ≤ 324 / 125
  cross_eq : cross = (∑ i, (conj ((p i : ℂ) * u i)) * v i).re
  q_eq : q = ∑ i, p i * Complex.normSq (u i)
  u_norm_eq : uNorm = ∑ i, Complex.normSq (u i)
  pu_norm_eq : pUNorm = ∑ i, (p i) ^ 2 * Complex.normSq (u i)
  v_norm_eq : vNorm = ∑ i, Complex.normSq (v i)
  cross_trace_eq : cross = mixedTrace M W (centeredEmbeddedGenerator r W)
  q_trace_eq : q = (M * W ^ 2).trace.re
  contraction : vNorm ≤ uNorm

theorem wu_relative_mixed_generator
    {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) (M W : Mat)
    (hM : M.PosDef) (hW : W.IsHermitian)
    (hlo : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1)
    (hdegree : ∀ k : WuCubicThermalBasis.Index, degree k < 2 →
      coefficient r (GInv r * W * GInv r) k = 0)
    (cert : WuSpectralCertificate r M W) :
    (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * (G r * generator r (GInv r * W * GInv r) * G r)).trace.re := by
  have hcontract : cert.vNorm ≤ cert.uNorm := cert.contraction
  have hrel := relative_trace_from_spectral_data cert.p cert.u cert.v cert.cross cert.q
    cert.uNorm cert.pUNorm cert.vNorm cert.p_range cert.cross_eq cert.q_eq
    cert.u_norm_eq cert.pu_norm_eq cert.v_norm_eq hcontract
  have hcross : cert.cross =
      (S_M M W * centeredEmbeddedGenerator r W).trace.re := cert.cross_trace_eq
  have hq : cert.q = (M * W ^ 2).trace.re := cert.q_trace_eq
  have hmix : ((M * W + W * M) *
      (G r * generator r (GInv r * W * GInv r) * G r)).trace.re =
      2 * (3 * cert.q + cert.cross) := by
    rw [centeredEmbeddedGenerator] at hcross
    change cert.cross =
      (((1 / 2 : ℂ) • (M * W + W * M)) *
        (G r * generator r (GInv r * W * GInv r) * G r - (3 : ℂ) • W)).trace.re at hcross
    rw [mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul,
      smul_eq_mul, Complex.re_ofReal_mul] at hcross
    have hq' := hq
    rw [Matrix.trace_mul, Matrix.trace_add, Complex.add_re,
      Matrix.trace_mul_comm (W ^ 2) M] at hq'
    nlinarith only [hcross, hq']
  rw [hmix]
  rw [hq] at hrel
  linarith

#print axioms kantorovich_324
#print axioms relative_trace_from_spectral_data
#print axioms wu_relative_mixed_generator

end D5.S3.Quantum.Semigroups.WuCubicHessianKantorovich
