/- GID: D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-flavor strong CP vacua, chiral susceptibility and axion couplings. -/

import OmegaBuild.Commands
import OmegaMath.Analysis.AffineLattice
import OmegaMath.Analysis.SquareRootCosine
import Mathlib.Analysis.Calculus.TangentCone.Real
import D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D
import D5.S3.Quantum.Gauge.YangMillsBPSSelfDual4D

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Matrix Set
open scoped Matrix ComplexConjugate Topology

namespace D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D

open ChiralSymmetrySkyrme4D (SU2 CMat2 ChiralSphere chiralPotential su2SphereCoordinates)
private def massPhase (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
private theorem massPhase_add (α β : ℝ) : massPhase (α + β) = massPhase α * massPhase β := by
  simp [massPhase, add_mul, Complex.exp_add]

/-- The leading two-flavor chiral potential, with the theta angle shared by the two masses. -/
def thetaChiralPotential (B₀ fπ mᵤ m_d θ : ℝ) (U : CMat2) : ℝ :=
  -B₀ * fπ ^ 2 *
    (((Complex.exp ((θ / 2 : ℝ) * Complex.I) • Matrix.diagonal ![(mᵤ : ℂ), (m_d : ℂ)]) *
      U).trace).re
private def thetaRadicand (mᵤ m_d θ : ℝ) : ℝ :=
  mᵤ ^ 2 + m_d ^ 2 + 2 * mᵤ * m_d * Real.cos θ

/-- The vacuum energy obtained by minimizing the leading chiral potential over SU(2). -/
def qcdThetaEnergy (B₀ fπ mᵤ m_d θ : ℝ) : ℝ :=
  -B₀ * fπ ^ 2 * Real.sqrt (thetaRadicand mᵤ m_d θ)

theorem thetaChiralPotential_zero_eq_chiralPotential (B₀ fπ mᵤ m_d : ℝ) (U : CMat2) :
    thetaChiralPotential B₀ fπ mᵤ m_d 0 U = chiralPotential B₀ fπ mᵤ m_d U := by
  simp [thetaChiralPotential, chiralPotential]

/-- The sum uses a real lift of the determinant phase. -/
def thetaBar (θ argDetM : ℝ) : ℝ := θ + argDetM

/-- Opposite diagonal phases have unit determinant. A common phase shifts the
determinant phase by twice its angle, as obtained from the two mass factors. -/
theorem thetaBar_chiral_rotation_invariant (θ argDetM αᵤ α_d φ α : ℝ)
    (M U : CMat2) :
    thetaBar (θ - (αᵤ + α_d)) (argDetM + (αᵤ + α_d)) = thetaBar θ argDetM ∧
      (Matrix.diagonal ![massPhase αᵤ, massPhase α_d] * M).det =
        massPhase (αᵤ + α_d) * M.det ∧
      (Matrix.diagonal ![massPhase φ, massPhase (-φ)] * U).det = U.det ∧
      ((massPhase α • (1 : CMat2)) * U).det = massPhase (2 * α) * U.det ∧
      thetaBar (θ - 2 * α) (argDetM + 2 * α) = thetaBar θ argDetM := by
  have hdet (a b : ℝ) (A : CMat2) :
      (Matrix.diagonal ![massPhase a, massPhase b] * A).det =
        massPhase (a + b) * A.det := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two, massPhase_add]
    rfl
  have hscalar : massPhase α • (1 : CMat2) =
      Matrix.diagonal ![massPhase α, massPhase α] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨by unfold thetaBar; ring, hdet _ _ _, ?_, ?_, by unfold thetaBar; ring⟩
  · rw [hdet, add_neg_cancel]
    simp [massPhase]
  · rw [hscalar, hdet, two_mul]
private def thetaReal (mᵤ m_d θ : ℝ) : ℝ := (mᵤ + m_d) * Real.cos (θ / 2)
private def thetaImag (mᵤ m_d θ : ℝ) : ℝ := (m_d - mᵤ) * Real.sin (θ / 2)
private theorem thetaRadicand_eq_squares (mᵤ m_d θ : ℝ) :
    thetaRadicand mᵤ m_d θ = thetaReal mᵤ m_d θ ^ 2 + thetaImag mᵤ m_d θ ^ 2 := by
  unfold thetaRadicand thetaReal thetaImag
  conv_lhs =>
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
  linear_combination -((m_d - mᵤ) ^ 2) * Real.sin_sq_add_cos_sq (θ / 2)
private theorem thetaRadicand_nonneg (mᵤ m_d θ : ℝ) : 0 ≤ thetaRadicand mᵤ m_d θ := by
  rw [thetaRadicand_eq_squares]
  positivity
private theorem thetaChiralPotential_coordinates (B₀ fπ mᵤ m_d θ : ℝ) (U : SU2) :
    let q := (su2SphereCoordinates U).val
    thetaChiralPotential B₀ fπ mᵤ m_d θ U =
      -B₀ * fπ ^ 2 * (thetaReal mᵤ m_d θ * q 0 + thetaImag mᵤ m_d θ * q 3) := by
  let q := su2SphereCoordinates U
  have h := su2SphereCoordinates.symm_apply_apply U
  rw [← h]
  rw [su2SphereCoordinates.apply_symm_apply]
  change -B₀ * fπ ^ 2 *
    (((massPhase (θ / 2) • Matrix.diagonal ![(mᵤ : ℂ), (m_d : ℂ)]) *
      (!![⟨q.val 0, q.val 3⟩, ⟨q.val 2, q.val 1⟩;
          ⟨-q.val 2, q.val 1⟩, ⟨q.val 0, -q.val 3⟩] : CMat2)).trace).re = _
  simp only [Matrix.smul_mul, Matrix.diagonal_mul, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply,
    Complex.ofReal_re, Complex.ofReal_im, massPhase, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, thetaReal, thetaImag]
  ring
private def diagonalSphere (a z : ℝ) (h : a ^ 2 + z ^ 2 = 1) : ChiralSphere :=
  ⟨![a, 0, 0, z], by simpa using h⟩
private theorem diagonalSphere_matrix (a z : ℝ) (h : a ^ 2 + z ^ 2 = 1) :
    (su2SphereCoordinates.symm (diagonalSphere a z h) : CMat2) =
      Matrix.diagonal ![(⟨a, z⟩ : ℂ), ⟨a, -z⟩] := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · change (⟨-(0 : ℝ), (0 : ℝ)⟩ : ℂ) = 0
    apply Complex.ext <;> simp
  · rfl
private theorem direction_sq {a z R : ℝ} (hR : R ≠ 0) (hs : R ^ 2 = a ^ 2 + z ^ 2) :
    (a / R) ^ 2 + (z / R) ^ 2 = 1 := by
  rw [div_pow, div_pow, ← add_div, ← hs, div_self (pow_ne_zero _ hR)]
private theorem sphere_projection (q : ChiralSphere) {a z R : ℝ}
    (hR : 0 < R) (hs : R ^ 2 = a ^ 2 + z ^ 2) :
    a * q.val 0 + z * q.val 3 ≤ R ∧
      (a * q.val 0 + z * q.val 3 = R ↔
        q = diagonalSphere (a / R) (z / R) (direction_sq hR.ne' hs)) := by
  have hunit := q.property
  have hd := direction_sq hR.ne' hs
  have hadd :
      (q.val 0 - a / R) ^ 2 + q.val 1 ^ 2 + q.val 2 ^ 2 + (q.val 3 - z / R) ^ 2 =
        2 - 2 * ((a * q.val 0 + z * q.val 3) / R) := by
    rw [add_div, mul_comm a, mul_div_assoc, mul_comm z, mul_div_assoc]
    linear_combination hunit + hd
  have hsum : 0 ≤ (q.val 0 - a / R) ^ 2 + q.val 1 ^ 2 + q.val 2 ^ 2 + (q.val 3 - z / R) ^ 2 :=
    by positivity
  have hproj : (a * q.val 0 + z * q.val 3) / R ≤ 1 := by linarith
  refine ⟨by simpa using (div_le_iff₀ hR).mp hproj, ?_⟩
  constructor
  · intro he
    rw [he, div_self hR.ne'] at hadd
    have ha : (q.val 0 - a / R) ^ 2 = 0 := by
      nlinarith [sq_nonneg (q.val 1), sq_nonneg (q.val 2), sq_nonneg (q.val 3 - z / R)]
    have hx : q.val 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (q.val 0 - a / R), sq_nonneg (q.val 2), sq_nonneg (q.val 3 - z / R)]
    have hy : q.val 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (q.val 0 - a / R), sq_nonneg (q.val 1), sq_nonneg (q.val 3 - z / R)]
    have hz : (q.val 3 - z / R) ^ 2 = 0 := by
      nlinarith [sq_nonneg (q.val 0 - a / R), sq_nonneg (q.val 1), sq_nonneg (q.val 2)]
    apply Subtype.ext
    funext i
    fin_cases i
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp ha)
    · exact sq_eq_zero_iff.mp hx
    · exact sq_eq_zero_iff.mp hy
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro rfl
    change a * (a / R) + z * (z / R) = R
    field_simp
    nlinarith

theorem thetaChiralPotential_ge_qcdThetaEnergy {B₀ fπ mᵤ m_d θ : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (U : SU2) :
    qcdThetaEnergy B₀ fπ mᵤ m_d θ ≤ thetaChiralPotential B₀ fπ mᵤ m_d θ U := by
  rw [thetaChiralPotential_coordinates]
  let R := Real.sqrt (thetaRadicand mᵤ m_d θ)
  have hs : R ^ 2 = thetaReal mᵤ m_d θ ^ 2 + thetaImag mᵤ m_d θ ^ 2 :=
    (Real.sq_sqrt (thetaRadicand_nonneg _ _ _)).trans (thetaRadicand_eq_squares _ _ _)
  change -B₀ * fπ ^ 2 * R ≤ _
  apply mul_le_mul_of_nonpos_left _ ((mul_neg_of_neg_of_pos (neg_neg_of_pos hB) (pow_pos hf 2)).le)
  rcases (Real.sqrt_nonneg (thetaRadicand mᵤ m_d θ)).eq_or_lt with h | h
  · change 0 = R at h
    rw [← h] at hs ⊢
    have ha : thetaReal mᵤ m_d θ ^ 2 = 0 := by nlinarith [sq_nonneg (thetaImag mᵤ m_d θ)]
    have hz : thetaImag mᵤ m_d θ ^ 2 = 0 := by nlinarith [sq_nonneg (thetaReal mᵤ m_d θ)]
    simp [sq_eq_zero_iff.mp ha, sq_eq_zero_iff.mp hz]
  · exact (sphere_projection (su2SphereCoordinates U) h hs).1

theorem qcdThetaEnergy_attained_on_diagonal_su2 {B₀ fπ mᵤ m_d θ : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ)
    (h : 0 < mᵤ ^ 2 + m_d ^ 2 + 2 * mᵤ * m_d * Real.cos θ) :
    let R := Real.sqrt (thetaRadicand mᵤ m_d θ)
    let a := (mᵤ + m_d) * Real.cos (θ / 2) / R
    let z := (m_d - mᵤ) * Real.sin (θ / 2) / R
    ∃ U₀ : SU2, (U₀ : CMat2) = Matrix.diagonal ![(⟨a, z⟩ : ℂ), ⟨a, -z⟩] ∧
      ∀ U : SU2, thetaChiralPotential B₀ fπ mᵤ m_d θ U = qcdThetaEnergy B₀ fπ mᵤ m_d θ ↔ U = U₀ := by
  let R := Real.sqrt (thetaRadicand mᵤ m_d θ)
  have hR : 0 < R := Real.sqrt_pos.2 h
  have hs : R ^ 2 = thetaReal mᵤ m_d θ ^ 2 + thetaImag mᵤ m_d θ ^ 2 :=
    (Real.sq_sqrt h.le).trans (thetaRadicand_eq_squares _ _ _)
  let q₀ := diagonalSphere (thetaReal mᵤ m_d θ / R) (thetaImag mᵤ m_d θ / R)
    (direction_sq hR.ne' hs)
  refine ⟨su2SphereCoordinates.symm q₀, diagonalSphere_matrix _ _ _, fun U => ?_⟩
  rw [thetaChiralPotential_coordinates]
  unfold qcdThetaEnergy
  rw [mul_right_inj' (mul_ne_zero (neg_ne_zero.mpr hB.ne') (pow_ne_zero 2 hf.ne'))]
  rw [(sphere_projection (su2SphereCoordinates U) hR hs).2]
  exact su2SphereCoordinates.toEquiv.eq_symm_apply.symm

theorem massless_quark_theta_unobservable {B₀ fπ m_d : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hd : 0 < m_d) (θ : ℝ) :
    qcdThetaEnergy B₀ fπ 0 m_d θ = -B₀ * fπ ^ 2 * m_d ∧
      ∃ U₀ : SU2, (U₀ : CMat2) = Matrix.diagonal ![massPhase (θ / 2), massPhase (-(θ / 2))] ∧
        thetaChiralPotential B₀ fπ 0 m_d θ U₀ = -B₀ * fπ ^ 2 * m_d := by
  have h : 0 < (0 : ℝ) ^ 2 + m_d ^ 2 + 2 * 0 * m_d * Real.cos θ := by
    simpa using pow_pos hd 2
  have hR : Real.sqrt (thetaRadicand 0 m_d θ) = m_d := by
    simp [thetaRadicand, Real.sqrt_sq hd.le]
  obtain ⟨U₀, hU, hmin⟩ := qcdThetaEnergy_attained_on_diagonal_su2 hB hf h
  refine ⟨by simp [qcdThetaEnergy, hR], U₀, hU.trans ?_, ?_⟩
  · have hphase (φ : ℝ) : (⟨Real.cos φ, Real.sin φ⟩ : ℂ) = massPhase φ := by
      apply Complex.ext <;> simp [massPhase, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp [hR, hd.ne', mul_div_cancel_left₀, ← hphase, Real.cos_neg, Real.sin_neg]
  · rw [(hmin U₀).2 rfl, qcdThetaEnergy, hR]

theorem vafa_witten_cp_conserving_minimum {B₀ fπ mᵤ m_d : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hu : 0 < mᵤ) (hd : 0 < m_d) (θ : ℝ) :
    qcdThetaEnergy B₀ fπ mᵤ m_d 0 ≤ qcdThetaEnergy B₀ fπ mᵤ m_d θ ∧
      (qcdThetaEnergy B₀ fπ mᵤ m_d 0 = qcdThetaEnergy B₀ fπ mᵤ m_d θ ↔ Real.cos θ = 1) := by
  have hp : 0 < 2 * mᵤ * m_d := by positivity
  have hle : thetaRadicand mᵤ m_d θ ≤ thetaRadicand mᵤ m_d 0 := by
    unfold thetaRadicand
    rw [Real.cos_zero]
    gcongr
    exact Real.cos_le_one θ
  refine ⟨mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hle)
    ((mul_neg_of_neg_of_pos (neg_neg_of_pos hB) (pow_pos hf 2)).le), ?_⟩
  unfold qcdThetaEnergy
  rw [mul_right_inj' (mul_ne_zero (neg_ne_zero.mpr hB.ne') (pow_ne_zero 2 hf.ne'))]
  constructor
  · intro hs
    have he := congrArg (fun x : ℝ => x ^ 2) hs
    rw [Real.sq_sqrt (thetaRadicand_nonneg _ _ _), Real.sq_sqrt (thetaRadicand_nonneg _ _ _)] at he
    unfold thetaRadicand at he
    rw [Real.cos_zero, ← sub_eq_zero] at he
    rw [show mᵤ ^ 2 + m_d ^ 2 + 2 * mᵤ * m_d * 1 -
      (mᵤ ^ 2 + m_d ^ 2 + 2 * mᵤ * m_d * Real.cos θ) =
        (2 * mᵤ * m_d) * (1 - Real.cos θ) by ring] at he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hp.ne')).symm
  · intro hc
    simp [thetaRadicand, hc]

theorem qcdThetaEnergy_periodic_and_even {B₀ fπ mᵤ m_d : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hu : 0 < mᵤ) (hd : 0 < m_d) :
    Function.Periodic (qcdThetaEnergy B₀ fπ mᵤ m_d) (2 * Real.pi) ∧
      (∀ θ, qcdThetaEnergy B₀ fπ mᵤ m_d (-θ) = qcdThetaEnergy B₀ fπ mᵤ m_d θ) ∧
      (∀ θ, qcdThetaEnergy B₀ fπ mᵤ m_d θ ≤ qcdThetaEnergy B₀ fπ mᵤ m_d Real.pi) ∧
      qcdThetaEnergy B₀ fπ mᵤ m_d Real.pi = -B₀ * fπ ^ 2 * |mᵤ - m_d| := by
  refine ⟨fun θ => by simp [qcdThetaEnergy, thetaRadicand, Real.cos_add_two_pi],
    fun θ => by simp [qcdThetaEnergy, thetaRadicand], ?_, ?_⟩
  · intro θ
    apply mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt _)
      ((mul_neg_of_neg_of_pos (neg_neg_of_pos hB) (pow_pos hf 2)).le)
    unfold thetaRadicand
    rw [Real.cos_pi]
    gcongr
    exact Real.neg_one_le_cos θ
  · unfold qcdThetaEnergy thetaRadicand
    rw [Real.cos_pi, show mᵤ ^ 2 + m_d ^ 2 + 2 * mᵤ * m_d * (-1) = (mᵤ - m_d) ^ 2 by ring,
      Real.sqrt_sq_eq_abs]
private theorem equalMassEnergy {m : ℝ} (hm : 0 < m) (B₀ fπ θ : ℝ) :
    qcdThetaEnergy B₀ fπ m m θ = -2 * B₀ * fπ ^ 2 * m * |Real.cos (θ / 2)| := by
  unfold qcdThetaEnergy
  rw [thetaRadicand_eq_squares]
  simp only [thetaReal, thetaImag, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (add_pos hm hm)]
  ring
private theorem equalMassCusp {B₀ fπ m : ℝ} (hm : 0 < m) :
    HasDerivWithinAt (qcdThetaEnergy B₀ fπ m m) (-B₀ * fπ ^ 2 * m) (Ici Real.pi) Real.pi ∧
      HasDerivWithinAt (qcdThetaEnergy B₀ fπ m m) (B₀ * fπ ^ 2 * m) (Iic Real.pi) Real.pi := by
  let C := -2 * B₀ * fπ ^ 2 * m
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (t / 2)) (-1 / 2) Real.pi := by
    convert ((hasDerivAt_id' Real.pi).div_const 2).cos using 1
    rw [Real.sin_pi_div_two]
    ring
  have hright : ∀ᶠ t in 𝓝[Ici Real.pi] Real.pi, t < 2 * Real.pi :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hleft : ∀ᶠ t in 𝓝[Iic Real.pi] Real.pi, 0 < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds Real.pi_pos)
  constructor
  · have h := (hcos.const_mul (-C)).hasDerivWithinAt (s := Ici Real.pi)
    have he : qcdThetaEnergy B₀ fπ m m =ᶠ[𝓝[Ici Real.pi] Real.pi]
        fun t => (-C) * Real.cos (t / 2) := by
      filter_upwards [self_mem_nhdsWithin, hright] with t ht ht'
      have hnonpos : Real.cos (t / 2) ≤ 0 := by
        rcases eq_or_lt_of_le (show Real.pi ≤ t from ht) with rfl | hlt
        · rw [Real.cos_pi_div_two]
        · exact (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])).le
      rw [equalMassEnergy hm, abs_of_nonpos hnonpos]
      dsimp [C]
      ring
    convert h.congr_of_eventuallyEq_of_mem he (by simp) using 1
    dsimp [C]
    ring
  · have h := (hcos.const_mul C).hasDerivWithinAt (s := Iic Real.pi)
    have he : qcdThetaEnergy B₀ fπ m m =ᶠ[𝓝[Iic Real.pi] Real.pi]
        fun t => C * Real.cos (t / 2) := by
      filter_upwards [self_mem_nhdsWithin, hleft] with t ht ht'
      have hnonneg := Real.cos_nonneg_of_mem_Icc
        (show t / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
          ⟨by linarith [Real.pi_pos], by linarith [show t ≤ Real.pi from ht]⟩)
      rw [equalMassEnergy hm, abs_of_nonneg hnonneg]
    convert h.congr_of_eventuallyEq_of_mem he (by simp) using 1
    dsimp [C]
    ring

theorem dashen_degenerate_cusp_and_spontaneous_cp_breaking {B₀ fπ m : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hm : 0 < m) :
    (∀ θ, qcdThetaEnergy B₀ fπ m m θ = -2 * B₀ * fπ ^ 2 * m * |Real.cos (θ / 2)|) ∧
      (∀ U : SU2, thetaChiralPotential B₀ fπ m m Real.pi U = 0) ∧
      HasDerivWithinAt (qcdThetaEnergy B₀ fπ m m) (-B₀ * fπ ^ 2 * m) (Ici Real.pi) Real.pi ∧
      HasDerivWithinAt (qcdThetaEnergy B₀ fπ m m) (B₀ * fπ ^ 2 * m) (Iic Real.pi) Real.pi ∧
      (¬ DifferentiableAt ℝ (qcdThetaEnergy B₀ fπ m m) Real.pi) ∧
      ∃ U₁ U₂ : SU2, (U₁ : CMat2) = Matrix.diagonal ![Complex.I, -Complex.I] ∧
        (U₂ : CMat2) = Matrix.diagonal ![-Complex.I, Complex.I] ∧ (U₁ : CMat2)ᴴ = U₂ := by
  obtain ⟨hR, hL⟩ := equalMassCusp (B₀ := B₀) (fπ := fπ) hm
  refine ⟨equalMassEnergy hm B₀ fπ, fun U => ?_, hR, hL, ?_, ?_⟩
  · rw [thetaChiralPotential_coordinates]
    simp [thetaReal, thetaImag, Real.cos_pi_div_two]
  · intro hd
    have hr := hR.derivWithin (uniqueDiffWithinAt_Ici _)
    have hl := hL.derivWithin (uniqueDiffWithinAt_Iic _)
    rw [hd.derivWithin (uniqueDiffWithinAt_Ici _)] at hr
    rw [hd.derivWithin (uniqueDiffWithinAt_Iic _)] at hl
    have hp : 0 < B₀ * fπ ^ 2 * m := by positivity
    linarith
  · let q₁ := diagonalSphere 0 1 (by norm_num)
    let q₂ := diagonalSphere 0 (-1) (by norm_num)
    have h₁ : (su2SphereCoordinates.symm q₁ : CMat2) =
        Matrix.diagonal ![Complex.I, -Complex.I] := by
      rw [diagonalSphere_matrix]
      congr 1
      ext i <;> fin_cases i <;> apply Complex.ext <;> simp
    have h₂ : (su2SphereCoordinates.symm q₂ : CMat2) =
        Matrix.diagonal ![-Complex.I, Complex.I] := by
      rw [diagonalSphere_matrix]
      congr 1
      ext i <;> fin_cases i <;> apply Complex.ext <;> simp
    refine ⟨_, _, h₁, h₂, ?_⟩
    rw [h₁, h₂, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    fin_cases i <;> simp
private theorem thetaRadicand_pos_of_ne {mᵤ m_d : ℝ} (hu : 0 < mᵤ) (hd : 0 < m_d)
    (hne : mᵤ ≠ m_d) (θ : ℝ) : 0 < thetaRadicand mᵤ m_d θ := by
  have h : 0 ≤ (2 * mᵤ * m_d) * (Real.cos θ + 1) :=
    mul_nonneg (by positivity) (by linarith [Real.neg_one_le_cos θ])
  unfold thetaRadicand
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]

theorem nondegenerate_smooth_at_pi {B₀ fπ mᵤ m_d : ℝ}
    (hu : 0 < mᵤ) (hd : 0 < m_d) (hne : mᵤ ≠ m_d) :
    Differentiable ℝ (qcdThetaEnergy B₀ fπ mᵤ m_d) ∧
      deriv (qcdThetaEnergy B₀ fπ mᵤ m_d) Real.pi = 0 := by
  have hderiv (θ : ℝ) : HasDerivAt (qcdThetaEnergy B₀ fπ mᵤ m_d)
      (-B₀ * fπ ^ 2 * (2 * mᵤ * m_d * -Real.sin θ / (2 * Real.sqrt (thetaRadicand mᵤ m_d θ)))) θ := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.sqrt _ (thetaRadicand_pos_of_ne hu hd hne θ).ne'
    exact ((Real.hasDerivAt_cos θ).const_mul (2 * mᵤ * m_d)).const_add (mᵤ ^ 2 + m_d ^ 2)
  exact ⟨fun θ => (hderiv θ).differentiableAt, by simp [(hderiv _).deriv, Real.sin_pi]⟩

/-- The canonically normalized field enters the angle with slope one over its decay constant. -/
def axionPotential (B₀ fπ mᵤ m_d θ₀ fₐ a : ℝ) : ℝ :=
  qcdThetaEnergy B₀ fπ mᵤ m_d (θ₀ + a / fₐ)

private theorem thetaProfile (B₀ fπ mᵤ m_d w : ℝ) :
    (fun x => qcdThetaEnergy B₀ fπ mᵤ m_d (w * x)) =
      fun x => (-B₀ * fπ ^ 2) * OmegaMath.SquareRootCosine.profile (mᵤ + m_d) (mᵤ * m_d) w x := by
  funext x
  unfold qcdThetaEnergy thetaRadicand OmegaMath.SquareRootCosine.profile
  congr 2
  ring

private theorem thetaProfile_derivatives {mᵤ m_d : ℝ} (hs : 0 < mᵤ + m_d) (B₀ fπ w : ℝ) :
    let V := fun x => qcdThetaEnergy B₀ fπ mᵤ m_d (w * x)
    HasDerivAt V 0 0 ∧
    HasDerivAt (deriv V) (B₀ * fπ ^ 2 * (mᵤ * m_d * w ^ 2 / (mᵤ + m_d))) 0 ∧
    iteratedDeriv 4 V 0 =
      (-B₀ * fπ ^ 2) * (mᵤ * m_d * w ^ 4 / (mᵤ + m_d) -
        3 * (mᵤ * m_d) ^ 2 * w ^ 4 / (mᵤ + m_d) ^ 3) := by
  dsimp only
  rw [thetaProfile]
  obtain ⟨h₁, h₂, h₄⟩ := OmegaMath.SquareRootCosine.profile_derivatives hs (mᵤ * m_d) w
  refine ⟨by simpa only [mul_zero] using h₁.const_mul (-B₀ * fπ ^ 2), ?_, ?_⟩
  · rw [deriv_const_mul_field']
    convert h₂.const_mul (-B₀ * fπ ^ 2) using 1
    ring
  · rw [iteratedDeriv_const_mul_field, h₄]

theorem qcd_topological_susceptibility_exact {fπ mᵤ m_d : ℝ} (hf : 0 < fπ)
    (hs : 0 < mᵤ + m_d) (B₀ : ℝ) :
    let V := qcdThetaEnergy B₀ fπ mᵤ m_d
    let mPiSq := B₀ * (mᵤ + m_d)
    HasDerivAt V 0 0 ∧
    HasDerivAt (deriv V) (B₀ * fπ ^ 2 * (mᵤ * m_d / (mᵤ + m_d))) 0 ∧
    deriv V 0 = 0 ∧
    deriv (deriv V) 0 = B₀ * fπ ^ 2 * (mᵤ * m_d / (mᵤ + m_d)) ∧
    deriv (deriv V) 0 = (mᵤ * m_d / (mᵤ + m_d) ^ 2) * (mPiSq * fπ ^ 2) := by
  obtain ⟨h₁, h₂, _⟩ := thetaProfile_derivatives hs B₀ fπ 1
  simp only [one_mul, one_pow, mul_one] at h₁ h₂
  refine ⟨h₁, h₂, h₁.deriv, h₂.deriv, ?_⟩
  rw [h₂.deriv, (ChiralSymmetrySkyrme4D.gmor_pion_mass_relation hf B₀ mᵤ m_d).1]
  field_simp [hs.ne']

private theorem axion_centered {fₐ : ℝ} (ha : fₐ ≠ 0) (B₀ fπ mᵤ m_d θ₀ : ℝ) :
    axionPotential B₀ fπ mᵤ m_d θ₀ fₐ =
      fun x => qcdThetaEnergy B₀ fπ mᵤ m_d (fₐ⁻¹ * (x - (-fₐ * θ₀))) := by
  funext x
  unfold axionPotential
  congr 1
  field_simp [ha]
  ring

private theorem axion_second_derivative {fₐ mᵤ m_d : ℝ} (ha : 0 < fₐ)
    (hs : 0 < mᵤ + m_d) (B₀ fπ θ₀ : ℝ) :
    deriv (deriv (axionPotential B₀ fπ mᵤ m_d θ₀ fₐ)) (-fₐ * θ₀) =
      B₀ * fπ ^ 2 * (mᵤ * m_d / (mᵤ + m_d)) / fₐ ^ 2 := by
  have he (V : ℝ → ℝ) : iteratedDeriv 2 V = deriv (deriv V) := by
    rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one]
  rw [← he, axion_centered ha.ne', iteratedDeriv_comp_sub_const 2
    (fun x : ℝ => qcdThetaEnergy B₀ fπ mᵤ m_d (fₐ⁻¹ * x))]
  simp only [sub_self]
  rw [he,
    (thetaProfile_derivatives hs B₀ fπ fₐ⁻¹).2.1.deriv]
  field_simp [ha.ne', hs.ne']

theorem peccei_quinn_relaxation_and_axion_mass {B₀ fπ mᵤ m_d fₐ : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hu : 0 < mᵤ) (hd : 0 < m_d) (ha : 0 < fₐ) (θ₀ : ℝ) :
    let V := axionPotential B₀ fπ mᵤ m_d θ₀ fₐ
    let mₐSq := deriv (deriv V) (-fₐ * θ₀)
    let mPiSq := B₀ * (mᵤ + m_d)
    θ₀ + (-fₐ * θ₀) / fₐ = 0 ∧
    (∀ a, (∀ b, V a ≤ V b) ↔ ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = θ₀ + a / fₐ) ∧
    mₐSq * fₐ ^ 2 = (mᵤ * m_d / (mᵤ + m_d) ^ 2) * (mPiSq * fπ ^ 2) ∧
    Real.sqrt mₐSq * fₐ =
      (Real.sqrt (mᵤ * m_d) / (mᵤ + m_d)) * Real.sqrt mPiSq * fπ ∧
    mₐSq * fₐ ^ 2 ≤ (1 / 4) * mPiSq * fπ ^ 2 ∧
    (mₐSq * fₐ ^ 2 = (1 / 4) * mPiSq * fπ ^ 2 ↔ mᵤ = m_d) := by
  have hs := add_pos hu hd
  have hshift : θ₀ + (-fₐ * θ₀) / fₐ = 0 := by field_simp [ha.ne']; ring
  have hgmor := (ChiralSymmetrySkyrme4D.gmor_pion_mass_relation hf B₀ mᵤ m_d).1
  let mass := B₀ * fπ ^ 2 * (mᵤ * m_d / (mᵤ + m_d)) / fₐ ^ 2
  have hmass : 0 ≤ mass := by dsimp [mass]; positivity
  have hpi : 0 < B₀ * (mᵤ + m_d) := mul_pos hB hs
  have hprod : 0 < B₀ * (mᵤ + m_d) * fπ ^ 2 := by positivity
  dsimp only
  rw [axion_second_derivative ha hs B₀ fπ θ₀]
  change _ ∧ _ ∧ mass * fₐ ^ 2 = _ ∧ _ ∧ _ ∧ (_ ↔ _)
  have hscaled : mass * fₐ ^ 2 =
      (mᵤ * m_d / (mᵤ + m_d) ^ 2) * (B₀ * (mᵤ + m_d) * fπ ^ 2) := by
    rw [hgmor]
    dsimp [mass]
    field_simp [ha.ne', hs.ne']
  refine ⟨hshift, ?_, hscaled, ?_, ?_, ?_⟩
  · intro a
    simp only [← Real.cos_eq_one_iff]
    have hmin := vafa_witten_cp_conserving_minimum hB hf hu hd (θ₀ + a / fₐ)
    constructor
    · intro h
      apply hmin.2.mp
      apply le_antisymm hmin.1
      simpa only [axionPotential, hshift] using h (-fₐ * θ₀)
    · intro h b
      unfold axionPotential
      rw [← hmin.2.mpr h]
      exact (vafa_witten_cp_conserving_minimum hB hf hu hd _).1
  · apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hmass, hscaled]
    simp only [mul_pow, div_pow, Real.sq_sqrt (mul_nonneg hu.le hd.le), Real.sq_sqrt hpi.le]
    ring
  · rw [hscaled]
    have hratio : mᵤ * m_d / (mᵤ + m_d) ^ 2 ≤ 1 / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
      nlinarith [sq_nonneg (mᵤ - m_d)]
    nlinarith [mul_le_mul_of_nonneg_right hratio hprod.le]
  · rw [hscaled, show (1 / 4 : ℝ) * (B₀ * (mᵤ + m_d)) * fπ ^ 2 =
      (1 / 4 : ℝ) * (B₀ * (mᵤ + m_d) * fπ ^ 2) by ring, mul_left_inj' hprod.ne']
    rw [div_eq_iff (sq_pos_of_pos hs).ne']
    constructor
    · intro h
      have hz : (mᵤ - m_d) ^ 2 = 0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · intro h
      rw [h]
      ring

theorem axion_quartic_self_coupling_exact_and_attractive {B₀ fπ mᵤ m_d fₐ : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hu : 0 < mᵤ) (hd : 0 < m_d) (ha : 0 < fₐ) (θ₀ : ℝ) :
    let V := axionPotential B₀ fπ mᵤ m_d θ₀ fₐ
    let mₐSq := deriv (deriv V) (-fₐ * θ₀)
    let quartic := iteratedDeriv 4 V (-fₐ * θ₀)
    quartic = -(mₐSq / fₐ ^ 2) * ((mᵤ ^ 2 - mᵤ * m_d + m_d ^ 2) / (mᵤ + m_d) ^ 2) ∧
    quartic < 0 ∧ -(mₐSq / fₐ ^ 2) < quartic ∧ quartic ≤ -(1 / 4) * (mₐSq / fₐ ^ 2) ∧
    (quartic = -(1 / 4) * (mₐSq / fₐ ^ 2) ↔ mᵤ = m_d) := by
  have hs := add_pos hu hd
  let mₐSq := deriv (deriv (axionPotential B₀ fπ mᵤ m_d θ₀ fₐ)) (-fₐ * θ₀)
  let quartic := iteratedDeriv 4 (axionPotential B₀ fπ mᵤ m_d θ₀ fₐ) (-fₐ * θ₀)
  let ratio := (mᵤ ^ 2 - mᵤ * m_d + m_d ^ 2) / (mᵤ + m_d) ^ 2
  have hmass : 0 < mₐSq / fₐ ^ 2 := by
    dsimp [mₐSq]
    rw [axion_second_derivative ha hs B₀ fπ θ₀]
    positivity
  have he : quartic = -(mₐSq / fₐ ^ 2) * ratio := by
    dsimp [quartic, mₐSq, ratio]
    rw [axion_second_derivative ha hs B₀ fπ θ₀, axion_centered ha.ne',
      iteratedDeriv_comp_sub_const 4 (fun x : ℝ => qcdThetaEnergy B₀ fπ mᵤ m_d (fₐ⁻¹ * x))]
    simp only [sub_self]
    rw [(thetaProfile_derivatives hs B₀ fπ fₐ⁻¹).2.2]
    field_simp [ha.ne', hs.ne']
    <;> ring
  have hlow : (1 / 4 : ℝ) ≤ ratio := by
    dsimp [ratio]
    rw [le_div_iff₀ (sq_pos_of_pos hs)]
    nlinarith [sq_nonneg (mᵤ - m_d)]
  have hhigh : ratio < 1 := by
    dsimp [ratio]
    rw [div_lt_iff₀ (sq_pos_of_pos hs)]
    nlinarith [mul_pos hu hd]
  change _ ∧ quartic < 0 ∧ -(mₐSq / fₐ ^ 2) < quartic ∧
    quartic ≤ -(1 / 4) * (mₐSq / fₐ ^ 2) ∧ (_ ↔ _)
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hmass) (by linarith)
  · rw [he]
    simpa only [mul_one] using mul_lt_mul_of_neg_left hhigh (neg_neg_of_pos hmass)
  · rw [he]
    nlinarith [mul_le_mul_of_nonpos_left hlow (neg_nonpos.mpr hmass.le)]
  · change quartic = _ ↔ _
    rw [he, show -(1 / 4 : ℝ) * (mₐSq / fₐ ^ 2) =
      -(mₐSq / fₐ ^ 2) * (1 / 4) by ring, mul_right_inj' (neg_ne_zero.mpr hmass.ne')]
    dsimp [ratio]
    rw [div_eq_iff (sq_pos_of_pos hs).ne']
    constructor
    · intro h
      have hz : (mᵤ - m_d) ^ 2 = 0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · intro h
      rw [h]
      ring

/-- Single-instanton and single-anti-instanton terms with common weight. -/
def instantonPotential (K g ρ θ : ℝ) : ℝ :=
  -2 * K * Real.exp (-YangMillsBPSSelfDual4D.bpstAction ρ / g ^ 2) *
    Real.cos (YangMillsBPSSelfDual4D.bpstCharge ρ * θ)

theorem instanton_dilute_gas_bridge {K g ρ : ℝ} (hK : 0 < K) (hg : 0 < g) (hρ : 0 < ρ) :
    let V := instantonPotential K g ρ
    (∀ θ, V θ = -2 * K * Real.exp (-(8 * Real.pi ^ 2) / g ^ 2) * Real.cos θ) ∧
    Function.Periodic V (2 * Real.pi) ∧
    Real.exp (-(8 * Real.pi ^ 2) / g ^ 2) < 1 ∧
    ∀ θ, V 0 ≤ V θ ∧ (V 0 = V θ ↔ ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = θ) := by
  have he (θ : ℝ) : instantonPotential K g ρ θ =
      -2 * K * Real.exp (-(8 * Real.pi ^ 2) / g ^ 2) * Real.cos θ := by
    simp only [instantonPotential, YangMillsBPSSelfDual4D.bpst_instanton_exact_action hρ,
      YangMillsBPSSelfDual4D.bpst_instanton_exact_charge_one hρ, one_mul]
  have hweight : Real.exp (-(8 * Real.pi ^ 2) / g ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith [sq_pos_of_pos Real.pi_pos]) (sq_pos_of_pos hg)
  refine ⟨he, fun θ => by rw [he, he, Real.cos_periodic], hweight, fun θ => ?_⟩
  rw [he, he, Real.cos_zero, ← Real.cos_eq_one_iff]
  have hcoef : -2 * K * Real.exp (-(8 * Real.pi ^ 2) / g ^ 2) < 0 := by
    have h := mul_pos hK (Real.exp_pos (-(8 * Real.pi ^ 2) / g ^ 2))
    linarith only [h]
  exact ⟨mul_le_mul_of_nonpos_left (Real.cos_le_one θ) hcoef.le,
    by rw [mul_right_inj' hcoef.ne, eq_comm]⟩

/-- The PQ field has winding number `d` in the strong CP angle. -/
def pqPotential (B₀ fπ mᵤ m_d θ₀ fPQ : ℝ) (d : ℕ) (a : ℝ) : ℝ :=
  qcdThetaEnergy B₀ fπ mᵤ m_d (θ₀ + (d : ℝ) * a / fPQ)

theorem domain_wall_vacuum_count_and_fa_invariance {B₀ fπ mᵤ m_d fPQ : ℝ} {d : ℕ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hu : 0 < mᵤ) (hd : 0 < m_d)
    (hPQ : 0 < fPQ) (hD : 0 < d) (θ₀ : ℝ) :
    let V := pqPotential B₀ fπ mᵤ m_d θ₀ fPQ d
    let fₐ := fPQ / (d : ℝ)
    let step := 2 * Real.pi * fₐ
    let offset := -θ₀ * fₐ
    V = axionPotential B₀ fπ mᵤ m_d θ₀ fₐ ∧
    (∀ t, Function.Periodic V t ↔ ∃ k : ℤ, t = step * k) ∧
    (∀ left,
      let reps := OmegaMath.AffineLattice.representative offset step left (n := d)
      Function.Injective reps ∧ Set.range reps =
        {a ∈ Set.Ico left (left + 2 * Real.pi * fPQ) | ∀ b, V a ≤ V b}) ∧
    (∀ k : Fin d, OmegaMath.AffineLattice.representative offset step offset k =
      (2 * k.val * Real.pi - θ₀) * fPQ / d) ∧
    Real.sqrt (deriv (deriv V) offset) * fₐ =
      (Real.sqrt (mᵤ * m_d) / (mᵤ + m_d)) * Real.sqrt (B₀ * (mᵤ + m_d)) * fπ := by
  have hD' : (0 : ℝ) < d := by exact_mod_cast hD
  let fₐ := fPQ / (d : ℝ)
  have ha : 0 < fₐ := div_pos hPQ hD'
  let step := 2 * Real.pi * fₐ
  have hstep : 0 < step := by dsimp [step]; positivity
  let offset := -θ₀ * fₐ
  let V := pqPotential B₀ fπ mᵤ m_d θ₀ fPQ d
  have he : V = axionPotential B₀ fπ mᵤ m_d θ₀ fₐ := by
    funext a
    dsimp [V, pqPotential, axionPotential, fₐ]
    congr 2
    field_simp [hPQ.ne', hD'.ne']
  have hw := peccei_quinn_relaxation_and_axion_mass hB hf hu hd ha θ₀
  have hmin (a : ℝ) : (∀ b, V a ≤ V b) ↔ ∃ k : ℤ, a = offset + step * k := by
    rw [he, hw.2.1 a]
    apply exists_congr
    intro k
    dsimp [offset, step]
    constructor <;> intro h
    · have ht := (div_eq_iff ha.ne').mp (show a / fₐ =
          (k : ℝ) * (2 * Real.pi) - θ₀ by linarith)
      linarith
    · rw [h]
      field_simp [ha.ne']
      ring
  have hbase : ∀ b, V offset ≤ V b := (hmin offset).mpr ⟨0, by simp⟩
  have hperiod : Function.Periodic V step := by
    intro a
    rw [he]
    unfold axionPotential qcdThetaEnergy thetaRadicand
    rw [show θ₀ + (a + step) / fₐ = θ₀ + a / fₐ + 2 * Real.pi by
      dsimp [step]
      field_simp [ha.ne']
      ring, Real.cos_periodic]
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · intro t
    constructor
    · intro ht
      change Function.Periodic V t at ht
      have hm := (hmin (offset + t)).mp (fun b => by rw [ht offset]; exact hbase b)
      rcases hm with ⟨k, hk⟩
      exact ⟨k, add_left_cancel hk⟩
    · rintro ⟨k, rfl⟩
      rw [mul_comm]
      exact hperiod.int_mul k
  · intro left
    obtain ⟨hinj, hrange⟩ := OmegaMath.AffineLattice.representatives_Ico offset hstep left d
    refine ⟨hinj, hrange.trans ?_⟩
    have hlen : (d : ℝ) * step = 2 * Real.pi * fPQ := by
      dsimp [step, fₐ]
      field_simp [hD'.ne']
    rw [hlen]
    ext a
    change (_ ∧ (∃ k : ℤ, offset + step * k = a)) ↔ (_ ∧ ∀ b, V a ≤ V b)
    simp only [hmin, eq_comm (a := a)]
  · intro k
    simp [OmegaMath.AffineLattice.representative]
    ring
  · change Real.sqrt (deriv (deriv V) offset) * fₐ = _
    rw [he, show offset = -fₐ * θ₀ by dsimp [offset]; ring]
    exact hw.2.2.2.1

end D5.S3.Quantum.Gauge.StrongCPAxionThetaVacuum4D
