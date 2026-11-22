/- GID: D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/PositiveMarginalMatrixEffects
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual preparation gives the exact joint-effect pairing and trace tensor isometry. -/

import D5.S3.Quantum.Foundation.PositiveMarginalMatrixComposition

/-!
# The trace pairing of product effects

The effect product of (16) is the actual bilinear preparation. Equation (17)
holds on all four vector arguments and yields the isometric linearization
in (18). The full local effect intervals suffice for joint separation.
-/

noncomputable section
open Matrix Unitary
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace TensorProduct BigOperators

open scoped PositiveMarginalMatrixComposition

namespace PositiveMarginalMatrixComposition

variable {a b d n : ℕ}

variable {M : H a →ₗ[ℝ] H b →ₗ[ℝ] H d}
  {RA : H d →ₗ[ℝ] H a} {RB : H d →ₗ[ℝ] H b}

private theorem tr_jordan (x y : H n) : tr (jordan x y) = pairing x y := by
  unfold tr pairing
  change (((2 : ℝ)⁻¹ • (x.val * y.val + y.val * x.val)).trace).re = _
  simp only [Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_mul_comm y.val x.val, Complex.smul_re, Complex.add_re]
  ring

private theorem trace_swap_left (A C W : Mat n) (h : Commute A W) :
    ((A * C) * W).trace = ((C * A) * W).trace := by
  rw [mul_assoc, Matrix.trace_mul_comm A (C * W), mul_assoc, ← h.eq, ← mul_assoc]

private theorem trace_swap_right (W B D : Mat n) (h : Commute W B) :
    (W * (B * D)).trace = (W * (D * B)).trace := by
  calc
    (W * (B * D)).trace = (B * (W * D)).trace := by
      rw [← mul_assoc, h.eq, mul_assoc]
    _ = (W * (D * B)).trace := by rw [Matrix.trace_mul_comm B, mul_assoc]

private theorem trace_symmetrized (A C B D : Mat n)
    (hAB : Commute A B) (hAD : Commute A D) (hCB : Commute C B) :
    (((2 : ℝ)⁻¹ • (A * C + C * A)) * ((2 : ℝ)⁻¹ • (B * D + D * B))).trace.re =
      ((A * B) * (C * D)).trace.re := by
  have hre : (A * B) * (C * D) = (A * C) * (B * D) := by
    rw [mul_assoc, ← mul_assoc B C D, ← hCB.eq, mul_assoc C B D, ← mul_assoc]
  rw [hre]
  have hAC : Commute (A * C) B := hAB.mul_left hCB
  have hCA : Commute (C * A) B := hCB.mul_left hAB
  have hBD : Commute A (B * D) := hAB.mul_right hAD
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_smul, Matrix.trace_add, Complex.smul_re, Complex.add_re,
    ← trace_swap_right _ _ _ hAC, ← trace_swap_right _ _ _ hCA,
    ← trace_swap_left _ _ _ hBD]
  ring

/-- The exact four-vector joint-effect pairing, using the actual preparation. -/
theorem prep_pairing (h : Marginals M RA RB) (hs : Spans M)
    (f x : H a) (g y : H b) :
    pairing (M f g) (M x y) = pairing f x * pairing g y := by
  calc
    pairing (M f g) (M x y) =
        tr (M (jordan f x) (jordan g y)) := by
      unfold pairing tr
      rw [← effect_mul h hs f g, ← effect_mul h hs x y,
        ← effect_mul h hs (jordan f x) (jordan g y),
        effect_jordanA h hs, effect_jordanB h hs]
      exact (trace_symmetrized _ _ _ _ (effect_commute h hs f g)
        (effect_commute h hs f y) (effect_commute h hs x g)).symm
    _ = _ := by rw [trace_prep h, tr_jordan, tr_jordan, mul_comm]

private theorem tensor_inner (h : Marginals M RA RB) (hs : Spans M)
    (z w : H a ⊗[ℝ] H b) :
    ⟪(TensorProduct.lift M) z, (TensorProduct.lift M) w⟫_ℝ = ⟪z, w⟫_ℝ := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ =>
    simp only [TensorProduct.inner_def, map_add, inner_add_left] at h₁ h₂ ⊢
    rw [h₁, h₂]
  | tmul x y =>
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ h₁ h₂ =>
      simp only [TensorProduct.inner_def, map_add, inner_add_right] at h₁ h₂ ⊢
      rw [h₁, h₂]
    | tmul f g =>
      rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul, TensorProduct.inner_tmul,
        inner_eq_pairing, inner_eq_pairing, inner_eq_pairing]
      exact prep_pairing h hs x f y g

/-- The trace isometry is the linearization of the supplied preparation. -/
def tensorIsometry (h : Marginals M RA RB) (hs : Spans M) :
    (H a ⊗[ℝ] H b) ≃ₗᵢ[ℝ] H d := by
  have hn (z : H a ⊗[ℝ] H b) : ‖TensorProduct.lift M z‖ = ‖z‖ := by
    calc
      ‖TensorProduct.lift M z‖ = √⟪TensorProduct.lift M z, TensorProduct.lift M z⟫_ℝ :=
        norm_eq_sqrt_real_inner _
      _ = √⟪z, z⟫_ℝ := congrArg Real.sqrt (tensor_inner h hs z z)
      _ = ‖z‖ := (norm_eq_sqrt_real_inner z).symm
  have hinj : Function.Injective (TensorProduct.lift M) := by
    intro x y he
    have hh := hn (x - y)
    rw [map_sub, he, sub_self, norm_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp hh.symm)
  exact { LinearEquiv.ofBijective (TensorProduct.lift M) ⟨hinj, lift_surjective hs⟩ with
    norm_map' := hn }

theorem tensorIsometry_toLinearMap (h : Marginals M RA RB) (hs : Spans M) :
    (tensorIsometry h hs).toLinearEquiv.toLinearMap = TensorProduct.lift M := rfl

@[simp] theorem tensorIsometry_tmul (h : Marginals M RA RB) (hs : Spans M) (x : H a) (y : H b) :
    tensorIsometry h hs (x ⊗ₜ[ℝ] y) = M x y := by
  change (tensorIsometry h hs).toLinearEquiv.toLinearMap (x ⊗ₜ[ℝ] y) = M x y
  rw [tensorIsometry_toLinearMap, TensorProduct.lift.tmul]

/-- Joint product effects separate the whole joint carrier. -/
private theorem effects_separate (h : Marginals M RA RB) (hs : Spans M) {z w : H d}
    (hz : ∀ f g, pairing (jordan (effect RA f) (effect RB g)) z =
      pairing (jordan (effect RA f) (effect RB g)) w) : z = w := by
  have he : ∀ f g, ⟪M f g, z⟫_ℝ = ⟪M f g, w⟫_ℝ := by
    intro f g
    simpa only [inner_eq_pairing, effect_product h hs] using hz f g
  let F : H d →ₗ[ℝ] ℝ := (innerₛₗ ℝ (E := H d)).flip z
  let G : H d →ₗ[ℝ] ℝ := (innerₛₗ ℝ (E := H d)).flip w
  let J := tensorIsometry h hs
  have hFG : F = G := (LinearMap.cancel_right (g := J.toLinearEquiv.toLinearMap)
      J.surjective).mp <| TensorProduct.ext' fun f g => by
    change F (tensorIsometry h hs (f ⊗ₜ[ℝ] g)) = G (tensorIsometry h hs (f ⊗ₜ[ℝ] g))
    rw [tensorIsometry_tmul]
    simpa only [F, G, LinearMap.flip_apply, innerₛₗ_apply_apply] using he f g
  exact ext_inner_left ℝ (LinearMap.congr_fun hFG)

/-- Product effects in the full local unit intervals already separate all joint vectors. -/
theorem proper_effects_separate (h : Marginals M RA RB) (hs : Spans M) {z w : H d}
    (hz : ∀ f g, IsEffect f → IsEffect g → pairing (jordan (effect RA f) (effect RB g)) z =
      pairing (jordan (effect RA f) (effect RB g)) w) : z = w := by
  let F : H d →ₗ[ℝ] ℝ := (innerₛₗ ℝ (E := H d)).flip z
  let G : H d →ₗ[ℝ] ℝ := (innerₛₗ ℝ (E := H d)).flip w
  apply effects_separate h hs
  intro f g
  rw [effect_product h hs, ← inner_eq_pairing, ← inner_eq_pairing]
  change F (M f g) = G (M f g)
  apply spectral_ext (F.comp (M.flip g)) (G.comp (M.flip g)) _ f
  intro U i
  apply spectral_ext (F.comp (M (frameProjection U i))) (G.comp (M (frameProjection U i))) _ g
  intro V j
  simpa only [F, G, LinearMap.comp_apply, LinearMap.flip_apply, innerₛₗ_apply_apply,
    inner_eq_pairing, effect_product h hs] using
      hz (frameProjection U i) (frameProjection V j)
        (frameProjection_isEffect U i) (frameProjection_isEffect V j)

/-- The product of proper effects is a proper effect for the canonical unit. -/
theorem product_effect_interval (h : Marginals M RA RB) (hs : Spans M)
    (f : H a) (g : H b) (hf : f.val.PosSemidef) (hg : g.val.PosSemidef)
    (hfc : (1 - f.val).PosSemidef) (hgc : (1 - g.val).PosSemidef) :
    (M f g).val.PosSemidef ∧ (1 - (M f g).val).PosSemidef := by
  refine ⟨h.prep_pos f g hf hg, ?_⟩
  have hA := h.prep_pos (unitH a - f) g hfc hg
  have hB := h.prep_pos (unitH a) (unitH b - g) Matrix.PosSemidef.one hgc
  have hsum := hA.add hB
  change ((M (unitH a - f) g).val + (M (unitH a) (unitH b - g)).val).PosSemidef at hsum
  have huD : (unitH d).val = 1 := rfl
  simp only [map_sub, LinearMap.sub_apply, Submodule.coe_sub, prep_unital h hs, huD] at hsum
  convert hsum using 1
  abel

end PositiveMarginalMatrixComposition
