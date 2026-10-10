/- GID: D5/S3/Quantum/Petz/SymmetricKernel
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dittmann's symmetric curvature kernel from logarithmic resolvents and an exponential second difference. -/

import D5.S3.Quantum.PositiveResolvent.LogMeanResolvents
import D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference

namespace D5.S3.Quantum.Petz.SymmetricKernel

open D5.S3.Quantum.PositiveResolvent.LogMeanResolvents
open D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference

noncomputable def P (x y z : ℝ) : ℝ := (m x y z) ^ 2 / (L x y * L x z * L y z)

noncomputable def hs (x y z : ℝ) : ℝ := (P x y z - 2 * Q x y z) / 6

noncomputable def closedForm (x y z : ℝ) : ℝ :=
  let a := Real.log x - Real.log y
  let b := Real.log x - Real.log z
  let c := Real.log y - Real.log z
  ((y - z) ^ 2 * a * b - (x - z) ^ 2 * a * c + (x - y) ^ 2 * b * c) /
      (6 * (x - y) * (x - z) * (y - z) * a * b * c)
    + (-x * y * a + x * z * b - y * z * c) / (3 * x * y * z * a * b * c)

private theorem P_eq_resolvent_sum {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    P x y z = 1 / ((x - y) * (x - z) * L y z) -
      1 / ((x - y) * (y - z) * L x z) + 1 / ((x - z) * (y - z) * L x y) := by
  have hB : L x z = L x y + (y - z) * m x y z := by
    linarith [L_sub_L_eq_m hx hy hz]
  have hC : L y z = L x y + (x - z) * m x y z := by
    have h := L_sub_L_eq_m hy hx hz
    rw [L_symm y x, ← m_symm x y z] at h
    linarith
  have hA0 := (L_pos hx hy).ne'
  have hB0 := (L_pos hx hz).ne'
  have hC0 := (L_pos hy hz).ne'
  unfold P
  field_simp [hA0, hB0, hC0, sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz, sub_ne_zero.mpr hyz]
  rw [hB, hC]
  ring

theorem hs_eq_closedForm {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : hs x y z = closedForm x y z := by
  have ha : Real.log x - Real.log y ≠ 0 :=
    sub_ne_zero.mpr (fun h => hxy (Real.log_injOn_pos hx hy h))
  have hb : Real.log x - Real.log z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hxz (Real.log_injOn_pos hx hz h))
  have hc : Real.log y - Real.log z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hyz (Real.log_injOn_pos hy hz h))
  rw [hs, P_eq_resolvent_sum hx hy hz hxy hxz hyz,
    L_eq_of_ne hy hz hyz, L_eq_of_ne hx hz hxz, L_eq_of_ne hx hy hxy,
    Q_eq_of_ne hx hy hz hxy hxz hyz]
  dsimp [closedForm]
  field_simp [hx.ne', hy.ne', hz.ne', ha, hb, hc,
    sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz, sub_ne_zero.mpr hyz]
  ring

private theorem P_symm (x y z : ℝ) : P x y z = P y x z := by
  unfold P
  rw [← m_symm x y z, ← L_symm x y]
  congr 1
  ring

private theorem P_symm_right (x y z : ℝ) : P x y z = P x z y := by
  unfold P
  rw [← m_symm_right x y z, ← L_symm y z]
  congr 1
  ring

theorem hs_symm {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    hs x y z = hs y x z := by
  rw [hs, hs, P_symm x y z, Q_symm x y z]

theorem hs_symm_right {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    hs x y z = hs x z y := by
  rw [hs, hs, P_symm_right x y z, Q_symm_right x y z]

theorem hs_homog {c x y z : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) : hs (c * x) (c * y) (c * z) = c⁻¹ * hs x y z := by
  rw [hs, hs, P, P, m_homog c x y z hc, L_homog c x y hc,
    L_homog c x z hc, L_homog c y z hc, Q_homog hc hx hy hz]
  field_simp
  <;> ring

theorem hs_self {r : ℝ} (hr : 0 < r) : hs r r r = -1 / (8 * r) := by
  rw [hs, P, m_self hr, L_self, Q_self hr]
  field_simp
  <;> ring

/-- Invariance under every permutation, including coincident positive nodes. -/
theorem hs_perm {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (σ : Equiv.Perm (Fin 3)) :
    hs (![x, y, z] (σ 0)) (![x, y, z] (σ 1)) (![x, y, z] (σ 2)) = hs x y z := by
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  generalize h0 : σ 0 = i0 at *
  generalize h1 : σ 1 = i1 at *
  generalize h2 : σ 2 = i2 at *
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp_all
  all_goals first
    | exact (hs_symm hx hy hz).symm
    | exact (hs_symm_right hx hy hz).symm
    | exact (hs_symm_right hy hz hx).trans (hs_symm hx hy hz).symm
    | exact (hs_symm hz hx hy).trans (hs_symm_right hx hy hz).symm
    | exact (hs_symm hz hy hx).trans
        ((hs_symm_right hy hz hx).trans (hs_symm hx hy hz).symm)

/-- Joint continuity on the positive orthant includes every coincidence. -/
theorem hs_continuousAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) (x, y, z) := by
  have hid : ContinuousAt (fun p : ℝ × ℝ × ℝ => p) (x, y, z) := continuousAt_id
  have hxy : ContinuousAt (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1) (x, y, z) :=
    (L_continuousAt hx hy).comp_of_eq (hid.fst.prodMk hid.snd.fst) rfl
  have hxz : ContinuousAt (fun p : ℝ × ℝ × ℝ => L p.1 p.2.2) (x, y, z) :=
    (L_continuousAt hx hz).comp_of_eq (hid.fst.prodMk hid.snd.snd) rfl
  have hyz : ContinuousAt (fun p : ℝ × ℝ × ℝ => L p.2.1 p.2.2) (x, y, z) :=
    (L_continuousAt hy hz).comp_of_eq (hid.snd.fst.prodMk hid.snd.snd) rfl
  have hP : ContinuousAt (fun p : ℝ × ℝ × ℝ => P p.1 p.2.1 p.2.2) (x, y, z) :=
    ((m_continuousAt hx hy hz).pow 2).div ((hxy.mul hxz).mul hyz)
      (mul_ne_zero (mul_ne_zero (L_pos hx hy).ne' (L_pos hx hz).ne') (L_pos hy hz).ne')
  exact (hP.sub ((Q_continuousAt hx hy hz).const_mul 2)).div_const 6

theorem hs_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2)
      {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2} := by
  intro p hp
  exact (hs_continuousAt hp.1 hp.2.1 hp.2.2).continuousWithinAt

end D5.S3.Quantum.Petz.SymmetricKernel
