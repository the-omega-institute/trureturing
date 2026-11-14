/- GID: D5/S3/Geometry/AlgebraicBoundary/BoundaryCoordinates
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/BoundaryCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Invertible linear coordinates act faithfully on entire-boundary polynomial equations. -/

import D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation
import D5.S3.Geometry.AlgebraicBoundary.BoundaryElimination

/-! Polynomial coordinate transport retains every ambient vector and equation. -/

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Geometry.AlgebraicBoundary.BoundaryCoordinates

universe u v

open private affinePullback eval_affinePullback
  from D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]

private def polynomialCoordinates (c : (κ → ℝ) ≃L[ℝ] (ι → ℝ)) :
    MvPolynomial ι ℝ ≃+* MvPolynomial κ ℝ where
  toFun p := affinePullback p 0 c.toContinuousLinearMap
  invFun p := affinePullback p 0 c.symm.toContinuousLinearMap
  left_inv p := by
    apply MvPolynomial.funext
    intro x
    simp [eval_affinePullback]
  right_inv p := by
    apply MvPolynomial.funext
    intro x
    simp [eval_affinePullback]
  map_mul' p q := by
    apply MvPolynomial.funext
    intro x
    simp [eval_affinePullback]
  map_add' p q := by
    apply MvPolynomial.funext
    intro x
    simp [eval_affinePullback]

private theorem eval_polynomialCoordinates
    (c : (κ → ℝ) ≃L[ℝ] (ι → ℝ)) (p : MvPolynomial ι ℝ) (x : κ → ℝ) :
    MvPolynomial.eval x (polynomialCoordinates c p) = MvPolynomial.eval (c x) p := by
  simp [polynomialCoordinates, eval_affinePullback]

private theorem exists_transverse_coordinates (e : ι → ℝ) (he : e ≠ 0) :
    ∃ (κ : Type u) (_ : Fintype κ)
      (c : (Option κ → ℝ) ≃L[ℝ] (ι → ℝ))
      (u : (ι → ℝ) →L[ℝ] ℝ)
      (π : (ι → ℝ) →L[ℝ] (κ → ℝ))
      (J : (κ → ℝ) →L[ℝ] (ι → ℝ)),
      u e = 1 ∧ π e = 0 ∧ (∀ v, u (J v) = 0) ∧ (∀ v, π (J v) = v) ∧
      (∀ v, c v = v none • e + J (fun j => v (some j))) ∧
      (∀ x, c.symm x = fun j => j.elim (u x) (π x)) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra! h
    exact he (funext h)
  let κ := {j : ι // j ≠ i}
  let u : (ι → ℝ) →L[ℝ] ℝ := (e i)⁻¹ • ContinuousLinearMap.proj i
  let π : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.val - (e j.val) • u
  let J : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun j => if h : j = i then 0 else ContinuousLinearMap.proj ⟨j, h⟩
  have hu : u e = 1 := by simp [u, hi]
  have hπe : π e = 0 := by ext j; simp [π, hu]
  have hJi : ∀ v, J v i = 0 := by intro v; simp [J]
  have hJj : ∀ v (j : κ), J v j.val = v j := by intro v j; simp [J, j.property]
  have huJ : ∀ v, u (J v) = 0 := by intro v; simp [u, hJi]
  have hπJ : ∀ v, π (J v) = v := by intro v; ext j; simp [π, hJj, huJ]
  have hdecomp : ∀ x, u x • e + J (π x) = x := by
    intro x
    ext j
    by_cases hj : j = i
    · subst j
      simp [u, hJi, mul_comm, hi]
    · simp [J, π, hj, smul_eq_mul]
      ring
  let V : (Option κ → ℝ) →L[ℝ] (ι → ℝ) :=
    (ContinuousLinearMap.proj none).smulRight e +
      J.comp (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (some j))
  let W : (ι → ℝ) →L[ℝ] (Option κ → ℝ) :=
    ContinuousLinearMap.pi (fun j => j.elim u (fun j => ContinuousLinearMap.proj j.val - (e j.val) • u))
  have hW : ∀ x, W x = fun j => j.elim (u x) (π x) := by
    intro x
    ext j
    cases j <;> simp [W, π]
  let c : (Option κ → ℝ) ≃L[ℝ] (ι → ℝ) :=
    { toLinearEquiv :=
        { toFun := V
          invFun := W
          map_add' := V.map_add
          map_smul' := V.map_smul
          left_inv := by
            intro v
            rw [hW]
            ext j
            cases j with
            | none => simp [V, hu, huJ]
            | some j => simp [V, hπJ, hπe]
          right_inv := by
            intro x
            simpa [V, hW] using hdecomp x }
      continuous_toFun := V.continuous
      continuous_invFun := W.continuous }
  exact ⟨κ, inferInstance, c, u, π, J, hu, hπe, huJ, hπJ, fun _ => rfl, hW⟩

end D5.S3.Geometry.AlgebraicBoundary.BoundaryCoordinates
