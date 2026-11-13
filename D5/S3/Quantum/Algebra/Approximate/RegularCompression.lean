/- GID: D5/S3/Quantum/Algebra/Approximate/RegularCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Approximate/RegularCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular-action compression for a complex bilinear nonassociative Hilbert-space product. -/

module

public import D5.S3.Quantum.Algebra.Approximate.Compression

/-! The product and Hilbert norm are retained throughout. The auxiliary regular
range carries exactly `p(x) = ‖L_x‖`, without installing a multiplication instance
on the target. The compression follows Kitaev, arXiv:2405.02434v2, §7. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.Approximate.RegularCompression

open scoped InnerProductSpace

attribute [local instance] FiniteDimensional.complete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [StarAddMonoid H] [StarModule ℂ H]

/-- The original Hilbert-space product, strict unit, adjoint law and associator bound. -/
structure Product (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] [StarAddMonoid H] [StarModule ℂ H] (M δ : ℝ) where
  mul : H →L[ℂ] H →L[ℂ] H
  unit : H
  unit_norm : ‖unit‖ = 1
  left_unit : ∀ x, mul unit x = x
  right_unit : ∀ x, mul x unit = x
  star_mul : ∀ x y, star (mul x y) = mul (star y) (star x)
  adjoint_mul : ∀ x, ContinuousLinearMap.adjoint (mul x) = mul (star x)
  one_le_M : 1 ≤ M
  delta_nonneg : 0 ≤ δ
  mul_norm : ‖mul‖ ≤ M
  assoc_bound : ∀ x y z,
    ‖mul (mul x y) z - mul x (mul y z)‖ ≤ δ * ‖x‖ * ‖y‖ * ‖z‖

namespace Product

variable {M δ : ℝ} (D : Product H M δ)

/-- The norm is the original Hilbert operator norm of the actual left action. -/
def p (x : H) : ℝ := ‖D.mul x‖

private theorem mul_injective : Function.Injective D.mul := by
  intro x y h
  have := congrArg (fun f : H →L[ℂ] H => f D.unit) h
  simpa only [D.right_unit] using this

/-- An isometric realization of the regular norm as a subspace of Hilbert operators. -/
abbrev RegularSpace := LinearMap.range D.mul.toLinearMap

/-- This equivalence changes neither the underlying product nor the Hilbert norm on `H`. -/
def regularEquiv : H ≃L[ℂ] D.RegularSpace :=
  (LinearEquiv.ofInjective D.mul.toLinearMap D.mul_injective).toContinuousLinearEquiv

private theorem regularEquiv_norm (x : H) : ‖D.regularEquiv x‖ = D.p x := rfl

private theorem norm_le_p (x : H) : ‖x‖ ≤ D.p x := by
  simpa only [D.right_unit, D.unit_norm, mul_one] using (D.mul x).le_opNorm D.unit

private theorem p_le (x : H) : D.p x ≤ M * ‖x‖ :=
  (D.mul.le_opNorm x).trans (mul_le_mul_of_nonneg_right D.mul_norm (norm_nonneg x))

private theorem p_star (x : H) : D.p (star x) = D.p x := by
  unfold p
  rw [← D.adjoint_mul]
  exact ContinuousLinearMap.adjoint.norm_map _

private theorem action_defect (x y : H) :
    ‖D.mul (D.mul x y) - D.mul x * D.mul y‖ ≤ δ * ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro z
    exact D.assoc_bound x y z

private theorem p_mul (x y : H) : D.p (D.mul x y) ≤ (1 + δ) * D.p x * D.p y := by
  have h := norm_le_norm_add (D.mul (D.mul x y) - D.mul x * D.mul y) (D.mul x * D.mul y)
  have ha := D.action_defect x y
  have hb := norm_mul_le (D.mul x) (D.mul y)
  have hc : δ * ‖x‖ * ‖y‖ ≤ δ * D.p x * D.p y :=
    mul_le_mul (mul_le_mul_of_nonneg_left (D.norm_le_p x) D.delta_nonneg)
      (D.norm_le_p y) (norm_nonneg y) (by positivity [p])
  simp only [sub_add_cancel] at h
  change ‖D.mul (D.mul x y)‖ ≤ _
  calc
    _ ≤ ‖D.mul (D.mul x y) - D.mul x * D.mul y‖ + ‖D.mul x * D.mul y‖ := h
    _ ≤ δ * D.p x * D.p y + D.p x * D.p y := add_le_add (ha.trans hc) hb
    _ = _ := by ring

private theorem p_assoc (x y z : H) :
    D.p (D.mul (D.mul x y) z - D.mul x (D.mul y z)) ≤
      (M * δ) * D.p x * D.p y * D.p z := by
  calc
    _ ≤ M * ‖D.mul (D.mul x y) z - D.mul x (D.mul y z)‖ := D.p_le _
    _ ≤ M * (δ * ‖x‖ * ‖y‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left (D.assoc_bound x y z) (by linarith [D.one_le_M])
    _ ≤ _ := by
      have hxyz := mul_le_mul (mul_le_mul (D.norm_le_p x) (D.norm_le_p y)
        (norm_nonneg _) (norm_nonneg _)) (D.norm_le_p z) (norm_nonneg _) (by positivity [p])
      nlinarith [mul_le_mul_of_nonneg_left hxyz (mul_nonneg (by linarith [D.one_le_M]) D.delta_nonneg)]

/-- Actual left multiplication, transported to the regular-action norm. -/
def left (x : H) : D.RegularSpace →L[ℂ] D.RegularSpace :=
  D.regularEquiv.toContinuousLinearMap ∘L (D.mul x) ∘L
    D.regularEquiv.symm.toContinuousLinearMap

/-- Actual right multiplication, transported to the regular-action norm. -/
def right (x : H) : D.RegularSpace →L[ℂ] D.RegularSpace :=
  D.regularEquiv.toContinuousLinearMap ∘L (D.mul.flip x) ∘L
    D.regularEquiv.symm.toContinuousLinearMap

private theorem left_apply (x y : H) : D.left x (D.regularEquiv y) =
    D.regularEquiv (D.mul x y) := by simp [left]

private theorem right_apply (x y : H) : D.right x (D.regularEquiv y) =
    D.regularEquiv (D.mul y x) := by simp [right]

end Product

end D5.S3.Quantum.Algebra.Approximate.RegularCompression
