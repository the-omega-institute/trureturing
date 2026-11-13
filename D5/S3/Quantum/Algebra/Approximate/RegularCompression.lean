/- GID: D5/S3/Quantum/Algebra/Approximate/RegularCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Approximate/RegularCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular-action compression for a complex bilinear nonassociative Hilbert-space product. -/


import D5.S3.Quantum.Algebra.Approximate.Compression

/-! The product and Hilbert norm are retained throughout. The auxiliary regular
range carries exactly `p(x) = ‖L_x‖`, without installing a multiplication instance
on the target. The compression follows Kitaev, arXiv:2405.02434v2, §7. -/


noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.Approximate.RegularCompression

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [StarAddMonoid H] [StarModule ℂ H]

local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

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

/-- An isometric realization of the regular norm as a subspace of Hilbert operators. -/
abbrev RegularSpace := LinearMap.range D.mul.toLinearMap

local instance regularSpace_complete : CompleteSpace D.RegularSpace :=
  FiniteDimensional.complete ℂ D.RegularSpace

/-- This equivalence changes neither the underlying product nor the Hilbert norm on `H`. -/
def regularEquiv : H ≃L[ℂ] D.RegularSpace :=
    (LinearEquiv.ofInjective D.mul.toLinearMap (by
    intro x y h
    have := congrArg (fun f : H →L[ℂ] H => f D.unit) h
    change D.mul x D.unit = D.mul y D.unit at this
    simpa only [D.right_unit] using this)).toContinuousLinearEquiv

private theorem unit_ne_zero : D.unit ≠ 0 := by
  intro h
  have := D.unit_norm
  simp only [h, norm_zero] at this
  norm_num at this

local instance regularSpace_nontrivial : Nontrivial D.RegularSpace :=
  ⟨⟨D.regularEquiv D.unit, D.regularEquiv 0, by
    intro h
    exact D.unit_ne_zero (D.regularEquiv.injective h)⟩⟩

local instance regularSpace_nontrivialTopology : NontrivialTopology D.RegularSpace := by
  letI : Nontrivial H := ⟨⟨D.unit, 0, by intro h; exact D.unit_ne_zero h⟩⟩
  letI : NontrivialTopology H :=
    (nontrivial_iff_nontrivialTopology (X := H)).mp inferInstance
  exact (D.regularEquiv.toHomeomorph).nontrivialTopology

local instance regularMap_normedRing : NormedRing (D.RegularSpace →L[ℂ] D.RegularSpace) :=
  @ContinuousLinearMap.toNormedRing ℂ D.RegularSpace
    D.RegularSpace.normedAddCommGroup inferInstance D.RegularSpace.normedSpace

local instance regularMap_normedAlgebraComplex :
    NormedAlgebra ℂ (D.RegularSpace →L[ℂ] D.RegularSpace) :=
  @ContinuousLinearMap.toNormedAlgebra ℂ D.RegularSpace
    D.RegularSpace.seminormedAddCommGroup inferInstance D.RegularSpace.normedSpace

local instance regularMap_smulReal : SMul ℝ (D.RegularSpace →L[ℂ] D.RegularSpace) :=
  ⟨fun r f => (r : ℂ) • f⟩

local instance regularMap_normedAlgebraReal :
    NormedAlgebra ℝ (D.RegularSpace →L[ℂ] D.RegularSpace) :=
  NormedAlgebra.complexToReal

local instance regularMap_normOneClass :
    NormOneClass (D.RegularSpace →L[ℂ] D.RegularSpace) :=
  @ContinuousLinearMap.normOneClass ℂ D.RegularSpace
    D.RegularSpace.seminormedAddCommGroup inferInstance D.RegularSpace.normedSpace
      inferInstance

private theorem regularEquiv_norm (x : H) : ‖D.regularEquiv x‖ = D.p x := rfl

private theorem norm_le_p (x : H) : ‖x‖ ≤ D.p x := by
  simpa only [p, D.right_unit, D.unit_norm, mul_one] using (D.mul x).le_opNorm D.unit

private theorem p_le (x : H) : D.p x ≤ M * ‖x‖ :=
  (D.mul.le_opNorm x).trans (mul_le_mul_of_nonneg_right D.mul_norm (norm_nonneg x))

private theorem p_star (x : H) : D.p (star x) = D.p x := by
  unfold p
  rw [← D.adjoint_mul]
  exact ContinuousLinearMap.adjoint.norm_map _

/-- The regular norm is covariant under the product's star reversal. -/
theorem p_star_mul_rev (x y : H) :
    D.p (D.mul (star y) (star x)) = D.p (D.mul x y) := by
  rw [← D.star_mul, p_star]

private theorem action_defect (x y : H) :
    ‖D.mul (D.mul x y) - D.mul x * D.mul y‖ ≤ δ * ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (mul_nonneg D.delta_nonneg (norm_nonneg x)) (norm_nonneg y)
  · intro z
    exact D.assoc_bound x y z

private theorem p_mul (x y : H) : D.p (D.mul x y) ≤ (1 + δ) * D.p x * D.p y := by
  have h := norm_add_le (D.mul (D.mul x y) - D.mul x * D.mul y) (D.mul x * D.mul y)
  have ha := action_defect D x y
  have hb := norm_mul_le (D.mul x) (D.mul y)
  have hc : δ * ‖x‖ * ‖y‖ ≤ δ * D.p x * D.p y :=
    mul_le_mul (mul_le_mul_of_nonneg_left (norm_le_p D x) D.delta_nonneg)
      (norm_le_p D y) (norm_nonneg y) (mul_nonneg D.delta_nonneg (norm_nonneg (D.mul x)))
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
    _ ≤ M * ‖D.mul (D.mul x y) z - D.mul x (D.mul y z)‖ := p_le D _
    _ ≤ M * (δ * ‖x‖ * ‖y‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left (D.assoc_bound x y z) (by linarith [D.one_le_M])
    _ ≤ _ := by
      have hxy : ‖x‖ * ‖y‖ ≤ D.p x * D.p y :=
        mul_le_mul (norm_le_p D x) (norm_le_p D y) (norm_nonneg y) (norm_nonneg _)
      have hxyz : ‖x‖ * ‖y‖ * ‖z‖ ≤ D.p x * D.p y * D.p z :=
        mul_le_mul hxy (norm_le_p D z) (norm_nonneg z)
          (mul_nonneg (norm_nonneg (D.mul x)) (norm_nonneg (D.mul y)))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hxyz
        (mul_nonneg (le_trans zero_le_one D.one_le_M) D.delta_nonneg)


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

private theorem p_add (x y : H) : D.p (x + y) ≤ D.p x + D.p y := by
  simpa only [p, map_add] using norm_add_le (D.mul x) (D.mul y)

private theorem p_neg (x : H) : D.p (-x) = D.p x := by simp only [p, map_neg, norm_neg]

private theorem projection_norm_le_two (P : H) (hP : star P = P) {τ : ℝ}
    (hτ : τ ≤ 1 / 4) (hδ : δ ≤ 1 / 4) (hPP : D.p (D.mul P P - P) ≤ τ) :
    D.p P ≤ 2 := by
  have hself : ‖D.mul P * D.mul P‖ = D.p P ^ 2 := by
    have h := ContinuousLinearMap.norm_adjoint_comp_self (D.mul P)
    simpa only [D.adjoint_mul, hP, p, pow_two, ContinuousLinearMap.mul_def] using h
  have hdef := action_defect D P P
  rw [norm_sub_rev] at hdef
  have hprod : D.p (D.mul P P) ≤ τ + D.p P := by
    have h := p_add D (D.mul P P - P) P
    simpa only [sub_add_cancel] using h.trans (add_le_add hPP le_rfl)
  have htri := norm_add_le
    (D.mul P * D.mul P - D.mul (D.mul P P)) (D.mul (D.mul P P))
  rw [sub_add_cancel, hself] at htri
  have hdelta : δ * ‖P‖ * ‖P‖ ≤ δ * D.p P ^ 2 := by
    have hsq := mul_self_le_mul_self (norm_nonneg P) (norm_le_p D P)
    nlinarith [mul_le_mul_of_nonneg_left hsq D.delta_nonneg]
  change D.p P ^ 2 ≤ ‖D.mul P * D.mul P - D.mul (D.mul P P)‖ + D.p (D.mul P P) at htri
  have ht : D.p P ^ 2 ≤ δ * D.p P ^ 2 + τ + D.p P := by
    nlinarith [hdef, hprod, htri]
  have hx := norm_nonneg (D.mul P)
  by_contra h
  have hx2 : 2 < D.p P := lt_of_not_ge h
  nlinarith [sq_nonneg (D.p P - 2)]

private theorem left_norm (x : H) : ‖D.left x‖ ≤ (1 + δ) * D.p x := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (by linarith [D.delta_nonneg]) (norm_nonneg _)
  · intro y
    obtain ⟨z, rfl⟩ := D.regularEquiv.surjective y
    rw [left_apply, regularEquiv_norm, regularEquiv_norm]
    exact p_mul D x z

private theorem right_norm (x : H) : ‖D.right x‖ ≤ (1 + δ) * D.p x := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (by linarith [D.delta_nonneg]) (norm_nonneg _)
  · intro y
    obtain ⟨z, rfl⟩ := D.regularEquiv.surjective y
    rw [right_apply, regularEquiv_norm, regularEquiv_norm]
    rw [← D.p_star_mul_rev z x]
    simpa only [p_star, mul_assoc, mul_comm (D.p (star x)) (D.p (star z))] using
      p_mul D (star x) (star z)

private theorem left_square_defect (P : H) {τ : ℝ}
    (hτ : 0 ≤ τ) (hPP : D.p (D.mul P P - P) ≤ τ) :
    ‖D.left P * D.left P - D.left P‖ ≤ M * δ * D.p P ^ 2 + (1 + δ) * τ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · have hM := le_trans zero_le_one D.one_le_M
    have hp : 0 ≤ D.p P := norm_nonneg _
    positivity [D.delta_nonneg]
  · intro y
    obtain ⟨z, rfl⟩ := D.regularEquiv.surjective y
    simp only [sub_apply, mul_apply_eq_comp, left_apply,
      ]
    rw [← D.regularEquiv.map_sub, regularEquiv_norm, regularEquiv_norm]
    have heq : D.mul P (D.mul P z) - D.mul P z =
        -(D.mul (D.mul P P) z - D.mul P (D.mul P z)) + D.mul (D.mul P P - P) z := by
      simp only [map_sub, sub_apply]
      abel
    rw [heq]
    calc
      _ ≤ D.p (-(D.mul (D.mul P P) z - D.mul P (D.mul P z))) +
          D.p (D.mul (D.mul P P - P) z) := p_add D _ _
      _ = D.p (D.mul (D.mul P P) z - D.mul P (D.mul P z)) +
          D.p (D.mul (D.mul P P - P) z) := by rw [p_neg]
      _ ≤ M * δ * D.p P * D.p P * D.p z + (1 + δ) * τ * D.p z := by
        apply add_le_add (p_assoc D P P z)
        exact (p_mul D _ z).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPP (by linarith [D.delta_nonneg])) (norm_nonneg _))
      _ = _ := by ring

private theorem right_square_defect (Q : H) {τ : ℝ}
    (hτ : 0 ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) :
    ‖D.right Q * D.right Q - D.right Q‖ ≤ M * δ * D.p Q ^ 2 + (1 + δ) * τ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · have hM := le_trans zero_le_one D.one_le_M
    have hq : 0 ≤ D.p Q := norm_nonneg _
    positivity [D.delta_nonneg]
  · intro y
    obtain ⟨z, rfl⟩ := D.regularEquiv.surjective y
    simp only [sub_apply, mul_apply_eq_comp, right_apply,
      ]
    rw [← D.regularEquiv.map_sub, regularEquiv_norm, regularEquiv_norm]
    have heq : D.mul (D.mul z Q) Q - D.mul z Q =
        (D.mul (D.mul z Q) Q - D.mul z (D.mul Q Q)) + D.mul z (D.mul Q Q - Q) := by
      simp only [map_sub]
      abel
    rw [heq]
    calc
      _ ≤ D.p (D.mul (D.mul z Q) Q - D.mul z (D.mul Q Q)) +
          D.p (D.mul z (D.mul Q Q - Q)) := p_add D _ _
      _ ≤ M * δ * D.p z * D.p Q * D.p Q + (1 + δ) * D.p z * τ := by
        apply add_le_add (p_assoc D z Q Q)
        exact (p_mul D z _).trans
          (mul_le_mul_of_nonneg_left hQQ
            (mul_nonneg (by linarith [D.delta_nonneg]) (norm_nonneg _)))
      _ = _ := by ring

private theorem left_right_defect (P Q : H) :
    ‖D.left P * D.right Q - D.right Q * D.left P‖ ≤ M * δ * D.p P * D.p Q := by
  apply ContinuousLinearMap.opNorm_le_bound
  · have hM := le_trans zero_le_one D.one_le_M
    have hp : 0 ≤ D.p P := norm_nonneg _
    have hq : 0 ≤ D.p Q := norm_nonneg _
    positivity [D.delta_nonneg]
  · intro y
    obtain ⟨z, rfl⟩ := D.regularEquiv.surjective y
    simp only [sub_apply, mul_apply_eq_comp, left_apply,
      right_apply]
    rw [← D.regularEquiv.map_sub, regularEquiv_norm, regularEquiv_norm]
    have h := p_assoc D P z Q
    have he : D.p (D.mul P (D.mul z Q) - D.mul (D.mul P z) Q) =
        D.p (D.mul (D.mul P z) Q - D.mul P (D.mul z Q)) := by
      simp only [p, map_sub, norm_sub_rev]
    rw [he]
    convert h using 1 <;> ring

/-- The two transported regular actions satisfy the actual square and
commutator estimates supplied by the same product and associator bound. -/
theorem two_piece_defects (P Q : H) {τ : ℝ} (hτ : 0 ≤ τ)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) :
    (‖D.left P * D.left P - D.left P‖ ≤
      M * δ * D.p P ^ 2 + (1 + δ) * τ) ∧
    (‖D.right Q * D.right Q - D.right Q‖ ≤
      M * δ * D.p Q ^ 2 + (1 + δ) * τ) ∧
    (‖D.left P * D.right Q - D.right Q * D.left P‖ ≤
      M * δ * D.p P * D.p Q) := by
  exact ⟨left_square_defect D P hτ hPP, right_square_defect D Q hτ hQQ,
    left_right_defect D P Q⟩

private theorem symmetrized_defect {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [NormOneClass A] (a b : A) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : ‖a‖ ≤ 3) (hb : ‖b‖ ≤ 3)
    (haa : ‖a * a - a‖ ≤ 4 * r) (hbb : ‖b * b - b‖ ≤ 4 * r)
    (hab : ‖a * b - b * a‖ ≤ 4 * r) :
    ‖(a * b + b * a - 1) ^ 2 - 1‖ ≤ 512 * r := by
  let s := a * b
  let e := b * a - a * b
  let t := s + s - 1
  have he : ‖e‖ ≤ 4 * r := by simpa only [e, norm_sub_rev] using hab
  have hs : ‖s‖ ≤ 9 := (norm_mul_le a b).trans (by nlinarith [norm_nonneg a, norm_nonneg b])
  have ht : ‖t‖ ≤ 19 := by
    calc
      _ ≤ ‖s + s‖ + ‖(1 : A)‖ := norm_sub_le _ _
      _ ≤ (‖s‖ + ‖s‖) + 1 := by rw [norm_one]; gcongr; exact norm_add_le _ _
      _ ≤ 19 := by linarith
  have hid : s * s - s = a * e * b + (a * a - a) * (b * b) + a * (b * b - b) := by
    dsimp [s, e]
    noncomm_ring
  have hss : ‖s * s - s‖ ≤ 84 * r := by
    rw [hid]
    calc
      _ ≤ (‖a‖ * ‖e‖ * ‖b‖) + ‖a * a - a‖ * (‖b‖ * ‖b‖) +
          ‖a‖ * ‖b * b - b‖ := by
        grw [norm_add_le, norm_add_le, norm_mul_le, norm_mul_le, norm_mul_le,
          norm_mul_le, norm_mul_le]
      _ ≤ 3 * (4 * r) * 3 + (4 * r) * (3 * 3) + 3 * (4 * r) := by gcongr
      _ = 84 * r := by ring
  have htaylor : (a * b + b * a - 1) ^ 2 - 1 =
      (4 : ℝ) • (s * s - s) + t * e + e * t + e * e := by
    have hfour : (4 : ℝ) • (s * s - s) =
        (s * s - s) + (s * s - s) + (s * s - s) + (s * s - s) := by module
    rw [hfour]
    dsimp [s, t, e]
    noncomm_ring
  rw [htaylor]
  calc
    _ ≤ (4 * ‖s * s - s‖) + ‖t‖ * ‖e‖ + ‖e‖ * ‖t‖ + ‖e‖ * ‖e‖ := by
      grw [norm_add_le, norm_add_le, norm_add_le, norm_smul, norm_mul_le,
        norm_mul_le, norm_mul_le]
      norm_num
    _ ≤ 4 * (84 * r) + 19 * (4 * r) + (4 * r) * 19 + (4 * r) * (4 * r) := by gcongr
    _ ≤ 512 * r := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]

/-- The almost involution built from the two actual regular actions. -/
def cornerInvolution (P Q : H) : D.RegularSpace →L[ℂ] D.RegularSpace :=
  D.left P * D.right Q + D.right Q * D.left P - 1

private theorem cornerInvolution_defect (P Q : H) (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ)
    [Nontrivial D.RegularSpace] :
    ‖D.cornerInvolution P Q ^ 2 - 1‖ ≤ 512 * (τ + M * δ) := by
  have hM : 0 ≤ M := le_trans zero_le_one D.one_le_M
  have heps : 0 ≤ M * δ := mul_nonneg hM D.delta_nonneg
  have hδeps : δ ≤ M * δ := by nlinarith [D.one_le_M, D.delta_nonneg]
  have hδ : δ ≤ 1 / 4 := by linarith
  have hτ1 : τ ≤ 1 / 4 := by linarith
  have hp := projection_norm_le_two D P hP hτ1 hδ hPP
  have hq := projection_norm_le_two D Q hQ hτ1 hδ hQQ
  have hp0 : 0 ≤ D.p P := norm_nonneg _
  have hq0 : 0 ≤ D.p Q := norm_nonneg _
  have hl : ‖D.left P‖ ≤ 3 := (left_norm D P).trans (by nlinarith)
  have hr : ‖D.right Q‖ ≤ 3 := (right_norm D Q).trans (by nlinarith)
  have hpieces := two_piece_defects D P Q hτ hPP hQQ
  have hll : ‖D.left P * D.left P - D.left P‖ ≤ 4 * (τ + M * δ) := by
    apply hpieces.1.trans
    have hpsq : D.p P ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpsq heps, mul_nonneg hτ (sub_nonneg.mpr hδ)]
  have hrr : ‖D.right Q * D.right Q - D.right Q‖ ≤ 4 * (τ + M * δ) := by
    apply hpieces.2.1.trans
    have hqsq : D.p Q ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hqsq heps, mul_nonneg hτ (sub_nonneg.mpr hδ)]
  have hlr : ‖D.left P * D.right Q - D.right Q * D.left P‖ ≤ 4 * (τ + M * δ) := by
    apply hpieces.2.2.trans
    have hpq : D.p P * D.p Q ≤ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]
    nlinarith [mul_le_mul_of_nonneg_left hpq heps]
  exact symmetrized_defect (D.left P) (D.right Q) (τ + M * δ)
    (add_nonneg hτ heps) (by linarith) hl hr hll hrr hlr

/-- The Taylor compression in the Banach space with norm `p`. -/
def regularCompression (P Q : H) : D.RegularSpace →L[ℂ] D.RegularSpace :=
  Compression.correction (D.cornerInvolution P Q)

/-- The actual regular-action compression stays close to the uncorrected
midpoint; the only remaining term is the inverse-square-root Taylor tail. -/
theorem regularCompression_closeness (P Q : H) (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) :
    ‖D.regularCompression P Q - (1 / 2 : ℝ) • (1 + D.cornerInvolution P Q)‖ ≤
      (19 / 2 : ℝ) *
        ‖Compression.inverseSqrt (D.cornerInvolution P Q ^ 2 - 1) - 1‖ := by
  have he0 : D.unit ≠ 0 := by
    intro h
    have := D.unit_norm
    simp only [h, norm_zero] at this
    norm_num at this
  letI : Nontrivial D.RegularSpace := ⟨⟨D.regularEquiv D.unit, D.regularEquiv 0, by
    intro h
    exact he0 (D.regularEquiv.injective h)⟩⟩
  have hM : 0 ≤ M := le_trans zero_le_one D.one_le_M
  have heps : 0 ≤ M * δ := mul_nonneg hM D.delta_nonneg
  have hδeps : δ ≤ M * δ := by nlinarith [D.one_le_M, D.delta_nonneg]
  have hδ : δ ≤ 1 / 4 := by linarith
  have hτ1 : τ ≤ 1 / 4 := by linarith
  have hp := projection_norm_le_two D P hP hτ1 hδ hPP
  have hq := projection_norm_le_two D Q hQ hτ1 hδ hQQ
  have h1δ : 0 ≤ 1 + δ := by linarith [D.delta_nonneg]
  have hl0 : ‖D.left P‖ ≤ (1 + δ) * D.p P := left_norm D P
  have hr0 : ‖D.right Q‖ ≤ (1 + δ) * D.p Q := right_norm D Q
  have hl : ‖D.left P‖ ≤ 3 := by
    apply hl0.trans
    calc
      (1 + δ) * D.p P ≤ (1 + δ) * 2 :=
        mul_le_mul_of_nonneg_left hp h1δ
      _ ≤ 3 := by nlinarith [hδ]
  have hr : ‖D.right Q‖ ≤ 3 := by
    apply hr0.trans
    calc
      (1 + δ) * D.p Q ≤ (1 + δ) * 2 :=
        mul_le_mul_of_nonneg_left hq h1δ
      _ ≤ 3 := by nlinarith [hδ]
  have ht : ‖D.cornerInvolution P Q‖ ≤ 19 := by
    calc
      ‖D.left P * D.right Q + D.right Q * D.left P - 1‖ ≤
          ‖D.left P * D.right Q + D.right Q * D.left P‖ + ‖(1 : D.RegularSpace →L[ℂ] D.RegularSpace)‖ :=
        norm_sub_le _ _
      _ ≤ (‖D.left P * D.right Q‖ + ‖D.right Q * D.left P‖) + 1 := by
        rw [norm_one]
        exact add_le_add_left
          (norm_add_le (D.left P * D.right Q) (D.right Q * D.left P)) 1
      _ ≤ 19 := by
        have h₁ : ‖D.left P * D.right Q‖ ≤ 9 := by
          have h₁' : ‖D.left P‖ * ‖D.right Q‖ ≤ (3 : ℝ) * 3 :=
            mul_le_mul hl hr (norm_nonneg _) (by norm_num)
          exact (norm_mul_le _ _).trans (by nlinarith [h₁'])
        have h₂ : ‖D.right Q * D.left P‖ ≤ 9 := by
          have h₂' : ‖D.right Q‖ * ‖D.left P‖ ≤ (3 : ℝ) * 3 :=
            mul_le_mul hr hl (norm_nonneg _) (by norm_num)
          exact (norm_mul_le _ _).trans (by nlinarith [h₂'])
        linarith
  have hc := Compression.correction_closeness (D.cornerInvolution P Q)
  change ‖D.regularCompression P Q - (1 / 2 : ℝ) •
      (1 + D.cornerInvolution P Q)‖ ≤ _ at hc
  apply hc.trans
  have htail := norm_nonneg
    (Compression.inverseSqrt (D.cornerInvolution P Q ^ 2 - 1) - 1)
  nlinarith [ht, htail]

/-- Uniform operator bounds for both actual bracketings. -/
private theorem regularCompression_bracketing_bound (P Q : H)
    (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) :
    ‖D.regularCompression P Q - D.left P * D.right Q‖ ≤ 4866 * (τ + M * δ) ∧
    ‖D.regularCompression P Q - D.right Q * D.left P‖ ≤ 4866 * (τ + M * δ) := by
  have heps : 0 ≤ M * δ := mul_nonneg (by linarith [D.one_le_M]) D.delta_nonneg
  have hδeps : δ ≤ M * δ := by nlinarith [D.one_le_M, D.delta_nonneg]
  have hp := projection_norm_le_two D P hP (by linarith : τ ≤ 1 / 4)
    (by linarith : δ ≤ 1 / 4) hPP
  have hq := projection_norm_le_two D Q hQ (by linarith : τ ≤ 1 / 4)
    (by linarith : δ ≤ 1 / 4) hQQ
  have hpq : D.p P * D.p Q ≤ 4 := by
    have hp0 : 0 ≤ D.p P := norm_nonneg _
    have hq0 : 0 ≤ D.p Q := norm_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]
  have hcomm : ‖D.left P * D.right Q - D.right Q * D.left P‖ ≤
      4 * (τ + M * δ) := by
    apply (left_right_defect D P Q).trans
    nlinarith [mul_le_mul_of_nonneg_left hpq heps]
  have hdef := cornerInvolution_defect D P Q hP hQ hτ hsmall hPP hQQ
  have htail := Compression.inverseSqrt_tail_linear (D.cornerInvolution P Q ^ 2 - 1)
    (by linarith : ‖D.cornerInvolution P Q ^ 2 - 1‖ ≤ 1 / 2)
  have hmid : ‖D.regularCompression P Q -
      (1 / 2 : ℝ) • (1 + D.cornerInvolution P Q)‖ ≤ 4864 * (τ + M * δ) := by
    have hc := regularCompression_closeness D P Q hP hQ hτ hsmall hPP hQQ
    nlinarith
  have hid : (1 / 2 : ℝ) • (1 + D.cornerInvolution P Q) =
      (1 / 2 : ℝ) • (D.left P * D.right Q + D.right Q * D.left P) := by
    congr 1
    simp only [cornerInvolution]
    abel
  have hhalf (a b : D.RegularSpace →L[ℂ] D.RegularSpace) :
      (1 / 2 : ℝ) • (a + b) - a = (1 / 2 : ℝ) • (b - a) := by module
  have hl : ‖(1 / 2 : ℝ) • (1 + D.cornerInvolution P Q) -
      D.left P * D.right Q‖ ≤ 2 * (τ + M * δ) := by
    rw [hid, hhalf, norm_smul, norm_sub_rev]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hr : ‖(1 / 2 : ℝ) • (1 + D.cornerInvolution P Q) -
      D.right Q * D.left P‖ ≤ 2 * (τ + M * δ) := by
    rw [hid, add_comm (D.left P * D.right Q), hhalf, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  constructor
  · exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)
  · exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

/-- The same compression, acting on the original Hilbert space. -/
def compression (P Q : H) : H →L[ℂ] H :=
  D.regularEquiv.symm.toContinuousLinearMap ∘L D.regularCompression P Q ∘L
    D.regularEquiv.toContinuousLinearMap

/-- The actual mixed corner is the range of the corrected original-product compression. -/
def corner (P Q : H) : Submodule ℂ H := LinearMap.range (D.compression P Q).toLinearMap

/-- Both bracketings are the actual original product. The estimates use the
regular norm `p`, uniformly in the input vector. -/
theorem compression_closeness (P Q : H) (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) (x : H) :
    D.p (D.compression P Q x - D.mul P (D.mul x Q)) ≤
      4866 * (τ + M * δ) * D.p x ∧
    D.p (D.compression P Q x - D.mul (D.mul P x) Q) ≤
      4866 * (τ + M * δ) * D.p x := by
  have hc := regularCompression_bracketing_bound D P Q hP hQ hτ hsmall hPP hQQ
  have hid : D.regularEquiv (D.compression P Q x) =
      D.regularCompression P Q (D.regularEquiv x) := by simp [compression]
  have hl := (D.regularCompression P Q - D.left P * D.right Q).le_opNorm
    (D.regularEquiv x)
  have hr := (D.regularCompression P Q - D.right Q * D.left P).le_opNorm
    (D.regularEquiv x)
  rw [sub_apply, mul_apply_eq_comp, right_apply, left_apply, ← hid,
    ← D.regularEquiv.map_sub, regularEquiv_norm, regularEquiv_norm] at hl
  rw [sub_apply, mul_apply_eq_comp, left_apply, right_apply, ← hid,
    ← D.regularEquiv.map_sub, regularEquiv_norm, regularEquiv_norm] at hr
  exact ⟨hl.trans (mul_le_mul_of_nonneg_right hc.1 (norm_nonneg _)),
    hr.trans (mul_le_mul_of_nonneg_right hc.2 (norm_nonneg _))⟩

/-- Transport of the regular-norm estimate to the original Hilbert operator
norm costs the original comparison factor `M`. -/
theorem compression_closeness_hilbert (P Q : H) (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) :
    ‖D.compression P Q - (D.mul P).comp (D.mul.flip Q)‖ ≤
      4866 * (τ + M * δ) * M ∧
    ‖D.compression P Q - (D.mul.flip Q).comp (D.mul P)‖ ≤
      4866 * (τ + M * δ) * M := by
  have hc0 : 0 ≤ 4866 * (τ + M * δ) := by
    positivity [D.delta_nonneg, le_trans zero_le_one D.one_le_M]
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound
    · exact mul_nonneg hc0 (by linarith [D.one_le_M])
    intro x
    have h := (compression_closeness D P Q hP hQ hτ hsmall hPP hQQ x).1
    exact (norm_le_p D _).trans (h.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (p_le D x) hc0))
  · apply ContinuousLinearMap.opNorm_le_bound
    · exact mul_nonneg hc0 (by linarith [D.one_le_M])
    intro x
    have h := (compression_closeness D P Q hP hQ hτ hsmall hPP hQQ x).2
    exact (norm_le_p D _).trans (h.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (p_le D x) hc0))

private theorem star_unit : star D.unit = D.unit := by
  have h := D.star_mul D.unit (star D.unit)
  simpa only [D.left_unit, star_star] using h.symm

private theorem complement_defect (Q : H) :
    D.mul (D.unit - Q) (D.unit - Q) - (D.unit - Q) = D.mul Q Q - Q := by
  simp only [map_sub, ContinuousLinearMap.sub_apply, D.left_unit, D.right_unit]
  abel

private def regularStar : D.RegularSpace →L[ℝ] D.RegularSpace :=
  LinearMap.mkContinuous
    { toFun := fun y => D.regularEquiv (star (D.regularEquiv.symm y))
      map_add' := by intro x y; simp
      map_smul' := by
        intro r x
        change D.regularEquiv.toContinuousLinearMap
          (star (D.regularEquiv.symm.toContinuousLinearMap (r • x))) =
            r • D.regularEquiv.toContinuousLinearMap (star (D.regularEquiv.symm x))
        rw [ContinuousLinearMap.map_smul_of_tower, star_smul, star_trivial,
          ContinuousLinearMap.map_smul_of_tower]
        rfl }
    1 (by
      intro y
      change D.p (star (D.regularEquiv.symm y)) ≤ 1 * ‖y‖
      rw [p_star, ← regularEquiv_norm, D.regularEquiv.apply_symm_apply, one_mul])

private theorem regularStar_apply (x : H) :
    D.regularStar (D.regularEquiv x) = D.regularEquiv (star x) := by
  simp [regularStar, LinearMap.mkContinuous_apply]

/-- The actual compression commutes with star after exchanging its two
corner labels. No adjoint or positivity of the compression is assumed. -/
theorem compression_star (P Q : H) (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) (x : H) :
    star (D.compression P Q x) = D.compression Q P (star x) := by
  have hi (y : D.RegularSpace) :
      D.regularStar (D.cornerInvolution P Q y) =
        D.cornerInvolution Q P (D.regularStar y) := by
    obtain ⟨z, rfl⟩ := D.regularEquiv.surjective y
    simp only [cornerInvolution, sub_apply, add_apply, mul_apply_eq_comp,
      one_apply, left_apply, right_apply, map_sub, map_add,
      regularStar_apply, D.star_mul, hP, hQ]
    change D.regularEquiv (D.mul (D.mul Q (star z)) P) +
        D.regularEquiv (D.mul Q (D.mul (star z) P)) - D.regularStar (D.regularEquiv z) =
      D.regularEquiv (D.mul Q (D.mul (star z) P)) +
        D.regularEquiv (D.mul (D.mul Q (star z)) P) - D.regularEquiv (star z)
    rw [regularStar_apply]
    abel
  have ht : ‖D.cornerInvolution P Q ^ 2 - 1‖ < 1 :=
    lt_of_le_of_lt (cornerInvolution_defect D P Q hP hQ hτ hsmall hPP hQQ)
      (by linarith)
  have hu : ‖D.cornerInvolution Q P ^ 2 - 1‖ < 1 :=
    lt_of_le_of_lt (cornerInvolution_defect D Q P hQ hP hτ hsmall hQQ hPP)
      (by linarith)
  have h := Compression.correction_intertwines D.regularStar
    (D.cornerInvolution P Q) (D.cornerInvolution Q P) ht hu hi (D.regularEquiv x)
  have htransport (A B : H) (y : H) :
      D.regularEquiv (D.compression A B y) =
        D.regularCompression A B (D.regularEquiv y) := by simp [compression]
  apply D.regularEquiv.injective
  rw [← regularStar_apply, htransport, htransport]
  simpa only [regularCompression, regularStar_apply] using h

/-- The actual complementary compressions give a two-piece decomposition,
with an error measured in the same regular norm as the original product. -/
theorem compression_two_piece (P Q : H) (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) (x : H) :
    D.p (D.compression P Q x + D.compression P (D.unit - Q) x -
      D.compression P D.unit x) ≤ 14598 * (τ + M * δ) * D.p x := by
  have hQc : star (D.unit - Q) = D.unit - Q := by rw [star_sub, star_unit, hQ]
  have hQQc : D.p (D.mul (D.unit - Q) (D.unit - Q) - (D.unit - Q)) ≤ τ := by
    rw [complement_defect]
    exact hQQ
  have hee : D.p (D.mul D.unit D.unit - D.unit) ≤ τ := by
    simpa only [D.left_unit, sub_self, p, map_zero, norm_zero] using hτ
  have h₁ := (compression_closeness D P Q hP hQ hτ hsmall hPP hQQ x).1
  have h₂ := (compression_closeness D P (D.unit - Q) hP hQc hτ hsmall hPP hQQc x).1
  have h₃ := (compression_closeness D P D.unit hP (star_unit D) hτ hsmall hPP hee x).1
  have hid : D.compression P Q x + D.compression P (D.unit - Q) x -
      D.compression P D.unit x =
      (D.compression P Q x - D.mul P (D.mul x Q)) +
        (D.compression P (D.unit - Q) x - D.mul P (D.mul x (D.unit - Q))) -
        (D.compression P D.unit x - D.mul P (D.mul x D.unit)) := by
    simp only [map_sub, D.right_unit]
    abel
  rw [hid]
  have h := p_add D
    ((D.compression P Q x - D.mul P (D.mul x Q)) +
      (D.compression P (D.unit - Q) x - D.mul P (D.mul x (D.unit - Q))))
    (-(D.compression P D.unit x - D.mul P (D.mul x D.unit)))
  rw [p_neg] at h
  have h' := p_add D (D.compression P Q x - D.mul P (D.mul x Q))
    (D.compression P (D.unit - Q) x - D.mul P (D.mul x (D.unit - Q)))
  rw [sub_eq_add_neg]
  linarith

/-- The original-product compression is exactly idempotent at a universal small-error scale. -/
theorem compression_idempotent (P Q : H) (hP : star P = P) (hQ : star Q = Q)
    {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ + M * δ ≤ 1 / 1024)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hQQ : D.p (D.mul Q Q - Q) ≤ τ) :
    D.compression P Q * D.compression P Q = D.compression P Q := by
  have he0 : D.unit ≠ 0 := by
    intro h
    have := D.unit_norm
    simp only [h, norm_zero] at this
    norm_num at this
  letI : Nontrivial D.RegularSpace := ⟨⟨D.regularEquiv D.unit, D.regularEquiv 0, by
    intro h
    exact he0 (D.regularEquiv.injective h)⟩⟩
  have hdef := cornerInvolution_defect D P Q hP hQ hτ hsmall hPP hQQ
  have hlt : ‖D.cornerInvolution P Q ^ 2 - 1‖ < 1 := by linarith
  have hc := Compression.correction_idempotent (D.cornerInvolution P Q) hlt
  change D.regularCompression P Q * D.regularCompression P Q = D.regularCompression P Q at hc
  ext x
  have hx := congrArg (fun f : D.RegularSpace →L[ℂ] D.RegularSpace =>
    D.regularEquiv.symm (f (D.regularEquiv x))) hc
  simpa only [compression, mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hx

end Product

end D5.S3.Quantum.Algebra.Approximate.RegularCompression
