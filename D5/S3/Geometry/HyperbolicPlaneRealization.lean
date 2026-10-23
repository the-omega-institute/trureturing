/- GID: D5/S3/Geometry/HyperbolicPlaneRealization
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicPlaneRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.UpperHalfPlane.Metric, mathlib/module/Mathlib.LinearAlgebra.Reflection]
   utility: none
   digest: Full actual-metric realization of each spacelike Lorentz supporting plane. -/

import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.LinearAlgebra.Reflection

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
namespace D5.S3.Geometry.HyperbolicPlaneRealization
set_option autoImplicit false

private def reflectPlane (M X : Fin 4 → ℝ) : Fin 4 → ℝ :=
  X + (-(2 * lorentz X M / lorentz M M)) • M

private theorem reflection_pair (M X Y : Fin 4 → ℝ) (hM : lorentz M M ≠ 0) :
    lorentz (reflectPlane M X) (reflectPlane M Y) = lorentz X Y := by
  have h := lorentz_linear X M Y M 1 (-(2 * lorentz X M / lorentz M M))
    1 (-(2 * lorentz Y M / lorentz M M))
  simp only [one_smul, lorentz_symm M Y] at h
  rw [reflectPlane, reflectPlane, h]
  field_simp
  <;> ring

private theorem reflection_involutive (M : Fin 4 → ℝ) (hM : lorentz M M ≠ 0) :
    Function.Involutive (reflectPlane M) := by
  let f : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun X => 2 * lorentz X M / lorentz M M
      map_add' := by
        intro X Y
        have h := lorentz_linear X Y M M 1 1 1 0
        simp only [one_smul, zero_smul, add_zero, one_mul, mul_one, mul_zero,
          zero_mul] at h
        rw [h]
        ring
      map_smul' := by
        intro a X
        have h := lorentz_linear X X M M a 0 1 0
        simp only [one_smul, zero_smul, add_zero, one_mul, mul_one, mul_zero,
          zero_mul] at h
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [h]
        ring }
  have hf : f M = 2 := by
    change 2 * lorentz M M / lorentz M M = 2
    exact mul_div_cancel_right₀ 2 hM
  have he : (Module.preReflection M f : (Fin 4 → ℝ) → (Fin 4 → ℝ)) =
      reflectPlane M := by
    funext X
    simp only [Module.preReflection_apply, f, LinearMap.coe_mk,
      AddHom.coe_mk, reflectPlane, sub_eq_add_neg, neg_smul]
  rw [← he]
  exact Module.involutive_preReflection hf

set_option maxHeartbeats 800000 in
theorem positive_time_of_pair (X Y : Fin 4 → ℝ)
    (hX : lorentz X X = -1) (hY : lorentz Y Y = -1)
    (ht : 0 < X 3) (hp : lorentz X Y < 0) : 0 < Y 3 := by
  simp [lorentz, Fin.sum_univ_succ] at hX hY hp
  have hcs : (X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2)^2 ≤
      (X 0^2 + X 1^2 + X 2^2) * (Y 0^2 + Y 1^2 + Y 2^2) := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin 3 => X i.castSucc) (fun i : Fin 3 => Y i.castSucc))
  have hx : X 0^2 + X 1^2 + X 2^2 = X 3^2 - 1 := by nlinarith
  have hy : Y 0^2 + Y 1^2 + Y 2^2 = Y 3^2 - 1 := by nlinarith
  rw [hx, hy] at hcs
  by_contra hn
  have htY : Y 3 ≤ 0 := le_of_not_gt hn
  have hprod : X 3 * Y 3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le htY
  have hsq : (X 3 * Y 3)^2 < (X 0*Y 0 + X 1*Y 1 + X 2*Y 2)^2 := by
    nlinarith
  have hx1 : 1 ≤ X 3^2 := by nlinarith [sq_nonneg (X 0),sq_nonneg (X 1),sq_nonneg (X 2)]
  have hy1 : 1 ≤ Y 3^2 := by nlinarith [sq_nonneg (Y 0),sq_nonneg (Y 1),sq_nonneg (Y 2)]
  nlinarith

private theorem reflection_future (M X : Fin 4 → ℝ) (hM : 0 < lorentz M M)
    (hu : lorentz X X = -1) (ht : 0 < X 3) : 0 < reflectPlane M X 3 := by
  apply positive_time_of_pair X _ hu
    (by rw [reflection_pair M X X hM.ne', hu]) ht
  have h := lorentz_right X X M 1 (-(2 * lorentz X M / lorentz M M))
  simp only [one_smul, hu] at h
  rw [reflectPlane, h]
  have hn : 0 ≤ 2 * (lorentz X M)^2 / lorentz M M :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM.le
  have he : -(2 * lorentz X M / lorentz M M) * lorentz X M =
      -(2 * (lorentz X M)^2 / lorentz M M) := by ring
  rw [he]
  linarith

private theorem adapted_reflection (N : Fin 4 → ℝ) (hN : 0 < lorentz N N) :
    ∃ (M : Fin 4 → ℝ) (s : ℝ), 0 < lorentz M M ∧ s ≠ 0 ∧
      ∀ X, lorentz (reflectPlane M X) N = -s * X 1 := by
  let r := Real.sqrt (lorentz N N)
  have hr : 0 < r := Real.sqrt_pos.mpr hN
  have hr2 : r^2 = lorentz N N := Real.sq_sqrt hN.le
  let s := if 0 ≤ N 1 then r else -r
  have hs : s ≠ 0 := by
    dsimp [s]
    split_ifs
    · exact hr.ne'
    · exact neg_ne_zero.mpr hr.ne'
  have hs2 : s^2 = lorentz N N := by dsimp [s]; split_ifs <;> nlinarith [hr2]
  have hsn : 0 ≤ s * N 1 := by
    dsimp [s]
    split_ifs with hn
    · exact mul_nonneg hr.le hn
    · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr.le) (le_of_not_ge hn)
  let M : Fin 4 → ℝ := ![N 0, N 1+s, N 2, N 3]
  have hM : lorentz M M = 2 * (lorentz N N + s * N 1) := by
    dsimp [M]
    simp [lorentz, Fin.sum_univ_succ] at hs2 ⊢
    nlinarith [hs2]
  have hMp : 0 < lorentz M M := by rw [hM]; positivity
  refine ⟨M, s, hMp, hs, ?_⟩
  intro X
  have hMN : lorentz M N = lorentz N N + s * N 1 := by
    simp [M, lorentz, Fin.sum_univ_succ]
    ring
  have hXM : lorentz X M = lorentz X N + s * X 1 := by
    simp [M, lorentz, Fin.sum_univ_succ]
    ring
  have h := lorentz_linear X M N N 1 (-(2 * lorentz X M / lorentz M M)) 1 0
  simp only [one_smul, zero_smul, add_zero] at h
  rw [reflectPlane, h, hMN, hXM, hM]
  have hd : lorentz N N + s * N 1 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hN hsn)
  field_simp
  <;> ring

private def vertical (z : UpperHalfPlane) : HyperbolicThreeSpace :=
  ⟨⟨WithLp.toLp 2 (Complex.mk z.re 0, z.im), z.im_pos⟩⟩

private theorem vertical_cosh (z w : UpperHalfPlane) :
    lorentz (lift (vertical z)) (lift (vertical w)) = -Real.cosh (dist z w) := by
  rw [UpperHalfPlane.cosh_dist']
  simp [lift, vertical, height, lorentz, Fin.sum_univ_succ]
  field_simp [z.im_pos.ne', w.im_pos.ne']
  <;> ring

private theorem vertical_zero (z : UpperHalfPlane) : lift (vertical z) 1 = 0 := by
  simp [lift, vertical]

private theorem vertical_surjective (Y : Fin 4 → ℝ)
    (hu : lorentz Y Y = -1) (ht : 0 < Y 3) (hy : Y 1 = 0) :
    ∃ z : UpperHalfPlane, lift (vertical z) = Y := by
  have hd := future_den Y hu ht
  let z : UpperHalfPlane := ⟨Complex.mk (Y 0/(Y 3-Y 2)) (1/(Y 3-Y 2)),
    one_div_pos.mpr hd⟩
  refine ⟨z, lift_of_coordinates _ Y hu ht ?_⟩
  simp [vertical, z, UpperHalfPlane.re, UpperHalfPlane.im, hy]

/-- Every original spacelike supporting plane is the full image of an isometric
copy of the existing hyperbolic upper half-plane, in the existing H3 metric. -/
theorem supporting_plane_isometry (N : Fin 4 → ℝ) (hN : 0 < lorentz N N) :
    ∃ e : UpperHalfPlane → HyperbolicThreeSpace, Isometry e ∧
      range e = {p | lorentz (lift p) N = 0} := by
  obtain ⟨M,s,hM,hs,hplane⟩ := adapted_reflection N hN
  let R := reflectPlane M
  have hR := reflection_involutive M hM.ne'
  let e : UpperHalfPlane → HyperbolicThreeSpace := fun z =>
    project (R (lift (vertical z)))
      (by rw [reflection_pair M _ _ hM.ne', lift_unit])
      (reflection_future M _ hM (lift_unit _) (lift_time _))
  have he (z : UpperHalfPlane) : lift (e z) = R (lift (vertical z)) :=
    lift_of_coordinates _ _
      (by rw [reflection_pair M _ _ hM.ne', lift_unit])
      (reflection_future M _ hM (lift_unit _) (lift_time _)) rfl
  refine ⟨e, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro z w
    apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
    have h := reflection_pair M (lift (vertical z)) (lift (vertical w)) hM.ne'
    change lorentz (R _) (R _) = _ at h
    rw [← he z, ← he w, lift_cosh, vertical_cosh] at h
    exact neg_injective h
  · ext p
    constructor
    · rintro ⟨z,rfl⟩
      change lorentz (lift (e z)) N = 0
      rw [he, hplane, vertical_zero, mul_zero]
    · intro hp
      have hu : lorentz (R (lift p)) (R (lift p)) = -1 := by
        rw [reflection_pair M _ _ hM.ne', lift_unit]
      have ht : 0 < R (lift p) 3 := reflection_future M _ hM (lift_unit p) (lift_time p)
      have hy : R (lift p) 1 = 0 := by
        have h := hplane (R (lift p))
        rw [hR] at h
        have hz : -s * R (lift p) 1 = 0 := h.symm.trans hp
        exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hs)
      obtain ⟨z,hz⟩ := vertical_surjective _ hu ht hy
      refine ⟨z, lift_injective ?_⟩
      rw [he, hz]
      exact hR (lift p)

#print axioms supporting_plane_isometry

end D5.S3.Geometry.HyperbolicPlaneRealization
