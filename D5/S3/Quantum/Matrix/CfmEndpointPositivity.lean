/- GID: D5/S3/Quantum/Matrix/CfmEndpointPositivity
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CfmEndpointPositivity
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Three-node resolvent control makes both endpoint sandwich derivatives positive. -/

import D5.S3.Quantum.Matrix.CfmResolventInterpolation
import D5.S3.Quantum.Matrix.CfmRadialDerivative
import Mathlib.Tactic

/-! Quadratic-form estimates at both endpoints of a Loewner interval. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.CfmEndpointPositivity

open CayleyResolvent CfmRadialDerivative CfmResolventInterpolation

private def quadratic (z : Fin 3 → ℂ) : Mat 3 →ₗ[ℝ] ℝ where
  toFun X := (star z ⬝ᵥ (X *ᵥ z)).re
  map_add' X Y := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' r X := by simp [Matrix.smul_mulVec, dotProduct_smul]

private theorem quadratic_nonneg {H : Mat 3} (hH : 0 ≤ H) (z : Fin 3 → ℂ) :
    0 ≤ quadratic z H := (hH.posSemidef.dotProduct_mulVec_nonneg z).1

private theorem quadratic_mono {H K : Mat 3} (h : H ≤ K) (z : Fin 3 → ℂ) :
    quadratic z H ≤ quadratic z K := by
  have ht := quadratic_nonneg (sub_nonneg.mpr h) z
  simpa only [map_sub, sub_nonneg] using ht

private theorem quadratic_sandwich (R H : Mat 3) (hR : R.IsHermitian) (z : Fin 3 → ℂ) :
    quadratic z (R * H * R) = quadratic (R *ᵥ z) H := by
  simp only [quadratic, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, hR.eq, Matrix.mul_assoc]

private theorem quadratic_conjugate (R H : Mat 3) (z : Fin 3 → ℂ) :
    quadratic z (Rᴴ * H * R) = quadratic (R *ᵥ z) H := by
  simp only [quadratic, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, Matrix.mul_assoc]

private theorem quadratic_gram (Q X : Mat 3) (z : Fin 3 → ℂ) :
    quadratic z (Xᴴ * (Qᴴ * Q) * X) =
      ‖(WithLp.toLp 2 ((Q * X) *ᵥ z) : EuclideanSpace ℂ (Fin 3))‖^2 := by
  have he : Xᴴ * (Qᴴ * Q) * X = (Q*X)ᴴ * 1 * (Q*X) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [he, quadratic_conjugate]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  simp only [quadratic, LinearMap.coe_mk, AddHom.coe_mk, Matrix.one_mulVec, WithLp.ofLp_toLp]
  rw [dotProduct_comm]
  rfl

private def observe (Q : Mat 3) (z : Fin 3 → ℂ) :
    Mat 3 →ₗ[ℝ] EuclideanSpace ℂ (Fin 3) where
  toFun X := WithLp.toLp 2 ((Q * X) *ᵥ z)
  map_add' X Y := by
    apply WithLp.ofLp_injective
    simp [Matrix.mul_add, Matrix.add_mulVec]
  map_smul' r X := by
    apply WithLp.ofLp_injective
    simp [Matrix.mul_smul, Matrix.smul_mulVec]

private theorem mixed_quadratic_control (C H : Mat 3) (hC : C.IsHermitian)
    (hspec : ∀ i, hC.eigenvalues i < 1) (hH : 0 ≤ H) (z : Fin 3 → ℂ) :
    let P := resolvent 2 C
    let Q := resolvent 3 C
    let R := resolvent 4 C
    quadratic z ((P*R)ᴴ*H*(P*R)) + quadratic z ((Q*R)ᴴ*H*(Q*R)) ≤
      54 * (quadratic z ((P*P)ᴴ*H*(P*P)) +
        quadratic z ((P*Q)ᴴ*H*(P*Q)) + quadratic z ((Q*Q)ᴴ*H*(Q*Q))) := by
  let S := CFC.sqrt H
  have hS : Sᴴ = S := (CFC.sqrt_nonneg H).posSemidef.isHermitian.eq
  have hSS : Sᴴ*S = H := by rw [hS]; exact CFC.sqrt_mul_sqrt_self H hH
  have ht := mixed_resolvent_control C hC hspec (observe S z)
  simpa only [CayleyResolvent.resolvent, observe, LinearMap.coe_mk, AddHom.coe_mk,
    ← quadratic_gram, hSS] using ht

private theorem resolvents_commute (C : Mat 3) (s t : ℝ) :
    Commute (resolvent s C) (resolvent t C) := by
  have h : Commute (s • (1 : Mat 3) - C) (t • (1 : Mat 3) - C) := by
    change _ * _ = _ * _
    simp [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    module
  simpa only [CayleyResolvent.resolvent, Matrix.nonsing_inv_eq_ringInverse] using h.ringInverse_ringInverse

private theorem resolvent_hermitian (C : Mat 3) (hC : C.IsHermitian) (s : ℝ) :
    (resolvent s C).IsHermitian := by
  exact ((Matrix.isHermitian_one.smul (show IsSelfAdjoint s from isSelfAdjoint_iff.mpr (star_trivial _))).sub hC).inv

private theorem endpoint_algebra (C H Z₂ Z₃ Z₄ : Mat 3)
    (hC : C.IsHermitian) (hspec : ∀ i, hC.eigenvalues i < 1) (hH : 0 ≤ H)
    (h₂l : (1/3 : ℝ) • H ≤ Z₂) (h₂u : Z₂ ≤ (3 : ℝ) • H)
    (h₃l : (1/3 : ℝ) • H ≤ Z₃) (h₃u : Z₃ ≤ (3 : ℝ) • H)
    (h₄l : (1/3 : ℝ) • H ≤ Z₄) (h₄u : Z₄ ≤ (3 : ℝ) • H) :
    let G := resolvent 2 C * Z₂ * resolvent 2 C +
      resolvent 3 C * Z₃ * resolvent 3 C -
      (1/20000 : ℝ) • (resolvent 4 C * Z₄ * resolvent 4 C)
    (resolventSumDerivative (1/20000 : ℝ) C G).PosSemidef := by
  let P := resolvent 2 C
  let Q := resolvent 3 C
  let R := resolvent 4 C
  let G := P*Z₂*P + Q*Z₃*Q - (1/20000 : ℝ) • (R*Z₄*R)
  have hP : P.IsHermitian := resolvent_hermitian C hC 2
  have hQ : Q.IsHermitian := resolvent_hermitian C hC 3
  have hR : R.IsHermitian := resolvent_hermitian C hC 4
  have hZ₂ : Z₂.IsHermitian :=
    ((smul_nonneg (by norm_num : (0:ℝ) ≤ 1/3) hH).trans h₂l).posSemidef.isHermitian
  have hZ₃ : Z₃.IsHermitian :=
    ((smul_nonneg (by norm_num : (0:ℝ) ≤ 1/3) hH).trans h₃l).posSemidef.isHermitian
  have hZ₄ : Z₄.IsHermitian :=
    ((smul_nonneg (by norm_num : (0:ℝ) ≤ 1/3) hH).trans h₄l).posSemidef.isHermitian
  have hG : G.IsHermitian := by
    have hp := Matrix.isHermitian_conjTranspose_mul_mul P hZ₂
    have hq := Matrix.isHermitian_conjTranspose_mul_mul Q hZ₃
    have hr := Matrix.isHermitian_conjTranspose_mul_mul R hZ₄
    rw [hP.eq] at hp
    rw [hQ.eq] at hq
    rw [hR.eq] at hr
    exact (hp.add hq).sub (hr.smul (show IsSelfAdjoint (1/20000 : ℝ) from isSelfAdjoint_iff.mpr (star_trivial _)))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hp := Matrix.isHermitian_conjTranspose_mul_mul P hG
    have hq := Matrix.isHermitian_conjTranspose_mul_mul Q hG
    have hr := Matrix.isHermitian_conjTranspose_mul_mul R hG
    rw [hP.eq] at hp
    rw [hQ.eq] at hq
    rw [hR.eq] at hr
    exact (hp.add hq).sub (hr.smul (show IsSelfAdjoint (1/20000 : ℝ) from isSelfAdjoint_iff.mpr (star_trivial _)))
  · intro z
    have hPQ : P*Q = Q*P := (resolvents_commute C 2 3).eq
    have hPR : P*R = R*P := (resolvents_commute C 2 4).eq
    have hQR : Q*R = R*Q := (resolvents_commute C 3 4).eq
    change 0 ≤ star z ⬝ᵥ (resolventSumDerivative (1/20000 : ℝ) C G *ᵥ z)
    apply Complex.nonneg_iff.mpr
    constructor
    · change 0 ≤ quadratic z (resolventSumDerivative (1/20000 : ℝ) C G)
      have hl (Z : Mat 3) (hZ : (1/3 : ℝ) • H ≤ Z) (X : Mat 3) :
          (1/3 : ℝ) * quadratic (X *ᵥ z) H ≤ quadratic (X *ᵥ z) Z := by
        simpa only [map_smul, smul_eq_mul] using quadratic_mono hZ (X *ᵥ z)
      have hu (Z : Mat 3) (hZ : Z ≤ (3 : ℝ) • H) (X : Mat 3) :
          quadratic (X *ᵥ z) Z ≤ 3 * quadratic (X *ᵥ z) H := by
        simpa only [map_smul, smul_eq_mul] using quadratic_mono hZ (X *ᵥ z)
      have hn (X : Mat 3) := quadratic_nonneg hH (X *ᵥ z)
      have h54 := mixed_quadratic_control C H hC hspec hH z
      simp only [quadratic_conjugate] at h54
      have he : quadratic z (resolventSumDerivative (1/20000 : ℝ) C G) =
          quadratic ((P*P) *ᵥ z) Z₂ + quadratic ((P*Q) *ᵥ z) Z₃ +
          quadratic ((P*Q) *ᵥ z) Z₂ + quadratic ((Q*Q) *ᵥ z) Z₃ +
          (1/20000 : ℝ)^2 * quadratic ((R*R) *ᵥ z) Z₄ -
          (1/20000 : ℝ) * (quadratic ((P*R) *ᵥ z) Z₄ +
            quadratic ((Q*R) *ᵥ z) Z₄ + quadratic ((P*R) *ᵥ z) Z₂ +
            quadratic ((Q*R) *ᵥ z) Z₃) := by
        change quadratic z (P*G*P + Q*G*Q - (1/20000 : ℝ) • (R*G*R)) = _
        simp only [map_sub, map_add, map_smul, smul_eq_mul,
          quadratic_sandwich P _ hP, quadratic_sandwich Q _ hQ,
          quadratic_sandwich R _ hR, G]
        simp only [map_sub, map_add, map_smul, smul_eq_mul,
          quadratic_sandwich P _ hP, quadratic_sandwich Q _ hQ,
          quadratic_sandwich R _ hR, Matrix.mulVec_mulVec,
          ← hPQ, ← hPR, ← hQR]
        ring
      rw [he]
      have hl11 := hl Z₂ h₂l (P*P)
      have hl12 := hl Z₃ h₃l (P*Q)
      have hl21 := hl Z₂ h₂l (P*Q)
      have hl22 := hl Z₃ h₃l (Q*Q)
      have hl33 := hl Z₄ h₄l (R*R)
      have hu13 := hu Z₄ h₄u (P*R)
      have hu23 := hu Z₄ h₄u (Q*R)
      have hu31 := hu Z₂ h₂u (P*R)
      have hu32 := hu Z₃ h₃u (Q*R)
      change quadratic ((P*R) *ᵥ z) H + quadratic ((Q*R) *ᵥ z) H ≤
        54 * (quadratic ((P*P) *ᵥ z) H + quadratic ((P*Q) *ᵥ z) H +
          quadratic ((Q*Q) *ᵥ z) H) at h54
      linarith [hn (P*P), hn (P*Q), hn (Q*Q), hn (R*R)]
    · have hm : (resolventSumDerivative (1/20000 : ℝ) C G).IsHermitian := by
        have hp := Matrix.isHermitian_conjTranspose_mul_mul P hG
        have hq := Matrix.isHermitian_conjTranspose_mul_mul Q hG
        have hr := Matrix.isHermitian_conjTranspose_mul_mul R hG
        rw [hP.eq] at hp
        rw [hQ.eq] at hq
        rw [hR.eq] at hr
        exact (hp.add hq).sub (hr.smul (show IsSelfAdjoint (1/20000 : ℝ) from isSelfAdjoint_iff.mpr (star_trivial _)))
      exact ((Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
        (hm.star_dotProduct_mulVec_comm z z)).symm

private theorem domain_spectrum {C : Mat 3} (hC : C ∈ cayleyDomain 3) :
    ∃ h : C.IsHermitian, ∀ i, h.eigenvalues i < 1 := by
  have h : C.IsHermitian := by
    have ht := hC.1.isHermitian.sub Matrix.isHermitian_one
    simpa using ht
  refine ⟨h, ?_⟩
  have he : cfc (fun x : ℝ => 1-x) C = 1-C := by
    rw [cfc_sub _ _ C, cfc_const_one ℝ C, cfc_id' (p := IsSelfAdjoint) ℝ C h]
  have hp := (cfc_isStrictlyPositive_iff (p := IsSelfAdjoint) (fun x : ℝ => 1-x) C
    (by fun_prop) h).mp (by rw [he]; exact hC.2.isStrictlyPositive)
  intro i
  linarith [hp (h.eigenvalues i) (h.eigenvalues_mem_spectrum_real i)]

/-- The derivative applied to the full increment is positive semidefinite at
both endpoints, including singular interval increments and repeated eigenvalues. -/
theorem endpoint_derivatives_positive (U V : Mat 3)
    (hU : U ∈ cayleyDomain 3) (hV : V ∈ cayleyDomain 3) (hUV : U ≤ V) :
    (resolventSumDerivative (1/20000 : ℝ) U
      (resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U)).PosSemidef ∧
    (resolventSumDerivative (1/20000 : ℝ) V
      (resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U)).PosSemidef := by
  have hf (s : ℝ) (hs : 2 ≤ s) := endpoint_resolvent_factors s hs U V hU.1 hU.2 hV.2 hUV
  have hH : 0 ≤ V-U := sub_nonneg.mpr hUV
  have hH13 : (1/3 : ℝ) • (V-U) ≤ V-U := by
    have ht : 0 ≤ (2/3 : ℝ) • (V-U) := smul_nonneg (by norm_num) hH
    apply sub_nonneg.mp
    convert ht using 1 <;> module
  have hH3 : V-U ≤ (3 : ℝ) • (V-U) := by
    have ht : 0 ≤ (2 : ℝ) • (V-U) := smul_nonneg (by norm_num) hH
    apply sub_nonneg.mp
    convert ht using 1 <;> module
  constructor
  · obtain ⟨Z₂,h₂,hl₂,hu₂⟩ := (hf 2 (by norm_num)).1
    obtain ⟨Z₃,h₃,hl₃,hu₃⟩ := (hf 3 (by norm_num)).1
    obtain ⟨Z₄,h₄,hl₄,hu₄⟩ := (hf 4 (by norm_num)).1
    obtain ⟨h,hspec⟩ := domain_spectrum hU
    have ht := endpoint_algebra U (V-U) Z₂ Z₃ Z₄ h hspec hH
      (hH13.trans hl₂) hu₂ (hH13.trans hl₃) hu₃ (hH13.trans hl₄) hu₄
    have he : resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U =
        resolvent 2 U*Z₂*resolvent 2 U + resolvent 3 U*Z₃*resolvent 3 U -
          (1/20000 : ℝ) • (resolvent 4 U*Z₄*resolvent 4 U) := by
      rw [← h₂, ← h₃, ← h₄]
      dsimp [resolventSum]
      module
    rwa [he]
  · obtain ⟨Z₂,h₂,hl₂,hu₂⟩ := (hf 2 (by norm_num)).2
    obtain ⟨Z₃,h₃,hl₃,hu₃⟩ := (hf 3 (by norm_num)).2
    obtain ⟨Z₄,h₄,hl₄,hu₄⟩ := (hf 4 (by norm_num)).2
    obtain ⟨h,hspec⟩ := domain_spectrum hV
    have ht := endpoint_algebra V (V-U) Z₂ Z₃ Z₄ h hspec hH
      hl₂ (hu₂.trans hH3) hl₃ (hu₃.trans hH3) hl₄ (hu₄.trans hH3)
    have he : resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U =
        resolvent 2 V*Z₂*resolvent 2 V + resolvent 3 V*Z₃*resolvent 3 V -
          (1/20000 : ℝ) • (resolvent 4 V*Z₄*resolvent 4 V) := by
      rw [← h₂, ← h₃, ← h₄]
      dsimp [resolventSum]
      module
    rwa [he]

end D5.S3.Quantum.Matrix.CfmEndpointPositivity
