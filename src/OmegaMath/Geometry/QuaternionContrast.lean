import OmegaBuild.Commands
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.FieldSimp

/-!
Omega original.

# Rational quaternion kernels realizing overlap and contrast

On the rational norm-one group, the kernel is half of one plus the weighted inner product.
Positive weights on the three imaginary coordinates give a rational norm-one group.
A residual coordinate realizes the slack between a prescribed contrast and its upper bound.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Omega.Geometry.QuaternionContrast

open scoped BigOperators

/-- Realize a nonnegative rational as a positive weight times a square, using zero or one. -/
private theorem positive_weight_square (s : ℚ) (hs : 0 ≤ s) :
    ∃ B f : ℚ, 0 < B ∧ B * f ^ 2 = s := by
  rcases eq_or_lt_of_le hs with h | h
  · exact ⟨1, 0, by norm_num, by simp [← h]⟩
  · exact ⟨s, 1, h, by simp⟩

/-- The rational coordinate certificate for `y = (c, e, 0, 0)` and `z = (r, i, j, 0)`.
The last two equations give twice the overlap and twice the contrast. -/
theorem exists_rational_coordinates (t d : ℚ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hd : d ^ 2 ≤ 1 - t) :
    ∃ A B c e r i j : ℚ, 0 < A ∧ 0 < B ∧
      c ^ 2 + A * e ^ 2 = 1 ∧ r ^ 2 + A * i ^ 2 + B * j ^ 2 = 1 ∧
      1 + c = 2 * t ∧ r - (c * r + A * e * i) = 2 * d := by
  let c := 2 * t - 1
  have hfactor : 0 ≤ (1 - c) * (1 + c) :=
    mul_nonneg (by dsimp [c]; linarith) (by dsimp [c]; linarith)
  have hc : 0 ≤ 1 - c ^ 2 := by nlinarith only [hfactor]
  obtain ⟨A, e, hA, he⟩ := positive_weight_square (1 - c ^ 2) hc
  have hy : c ^ 2 + A * e ^ 2 = 1 := by linarith only [he]
  have hov : 1 + c = 2 * t := by dsimp [c]; ring
  rcases lt_or_eq_of_le ht₁ with ht | rfl
  · have hden : 0 < 1 - t := sub_pos.mpr ht
    let l := d / (2 * (1 - t))
    let s := 1 - d ^ 2 / (1 - t)
    have hs : 0 ≤ s := sub_nonneg.mpr ((div_le_iff₀ hden).2 (by simpa using hd))
    obtain ⟨B, j, hB, hj⟩ := positive_weight_square s hs
    have hlength : (1 - c) ^ 2 + A * e ^ 2 = 4 * (1 - t) := by
      nlinarith only [he, hov]
    refine ⟨A, B, c, e, l * (1 - c), -(l * e), j, hA, hB, hy, ?_, hov, ?_⟩
    · calc
        (l * (1 - c)) ^ 2 + A * (-(l * e)) ^ 2 + B * j ^ 2 =
            l ^ 2 * ((1 - c) ^ 2 + A * e ^ 2) + B * j ^ 2 := by ring
        _ = 1 := by
          rw [hlength, hj]
          dsimp [s, l]
          field_simp [ne_of_gt hden]
          ring
    · calc
        l * (1 - c) - (c * (l * (1 - c)) + A * e * (-(l * e))) =
            l * ((1 - c) ^ 2 + A * e ^ 2) := by ring
        _ = 2 * d := by
          rw [hlength]
          dsimp [l]
          field_simp [ne_of_gt hden]
          ring
  · have hd0 : d ^ 2 = 0 := le_antisymm (by simpa using hd) (sq_nonneg d)
    have hd' : d = 0 := sq_eq_zero_iff.mp hd0
    have hc' : c = 1 := by linarith only [hov]
    refine ⟨A, 1, c, e, 1, 0, 0, hA, by norm_num, hy, by norm_num, hov, ?_⟩
    simp [hc', hd']


/-- The rational quaternion algebra with basis elements squaring to `-A` and `-B`. -/
abbrev Quat (A B : ℚ) := QuaternionAlgebra ℚ (-A) 0 (-B)

variable {A B : ℚ}

/-- The weighted rational inner product on the quaternion coordinates. -/
def inner (x y : Quat A B) : ℚ :=
  x.re * y.re + A * x.imI * y.imI + B * x.imJ * y.imJ + A * B * x.imK * y.imK

/-- The quadratic form attached to the weighted inner product. -/
def normSq (x : Quat A B) : ℚ :=
  x.re ^ 2 + A * x.imI ^ 2 + B * x.imJ ^ 2 + A * B * x.imK ^ 2

private theorem normSq_eq_re_mul_star (x : Quat A B) :
    normSq x = (x * star x).re := by
  simp [normSq, QuaternionAlgebra.re_star, QuaternionAlgebra.re_mul]
  ring

private theorem mul_star (x : Quat A B) : x * star x = ((normSq x : ℚ) : Quat A B) :=
  x.mul_star_eq_coe.trans (congrArg (fun r : ℚ => (r : Quat A B))
    (normSq_eq_re_mul_star x).symm)

private theorem normSq_one : normSq (1 : Quat A B) = 1 := by
  norm_num [normSq]

/-- The weighted square norm is multiplicative. -/
theorem normSq_mul (x y : Quat A B) : normSq (x * y) = normSq x * normSq y := by
  apply QuaternionAlgebra.coe_injective (c₁ := -A) (c₂ := 0) (c₃ := -B)
  rw [← mul_star, star_mul, mul_assoc, ← mul_assoc y, mul_star y,
    QuaternionAlgebra.coe_commutes, ← mul_assoc, mul_star x, QuaternionAlgebra.coe_mul]

private theorem normSq_star (x : Quat A B) : normSq (star x) = normSq x := by
  simp [normSq]

private theorem normSq_neg (x : Quat A B) : normSq (-x) = normSq x := by
  simp [normSq]

/-- With positive weights the square norm is nonnegative. -/
theorem normSq_nonneg (hA : 0 < A) (hB : 0 < B) (x : Quat A B) : 0 ≤ normSq x :=
  add_nonneg
    (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hA.le (sq_nonneg _)))
      (mul_nonneg hB.le (sq_nonneg _)))
    (mul_nonneg (mul_pos hA hB).le (sq_nonneg _))

/-- With positive weights the square norm vanishes exactly at zero. -/
theorem normSq_eq_zero (hA : 0 < A) (hB : 0 < B) (x : Quat A B) :
    normSq x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by norm_num [h, normSq]⟩
  have hr := sq_nonneg x.re
  have hi := mul_nonneg hA.le (sq_nonneg x.imI)
  have hj := mul_nonneg hB.le (sq_nonneg x.imJ)
  have hk := mul_nonneg (mul_pos hA hB).le (sq_nonneg x.imK)
  rw [normSq, add_eq_zero_iff_of_nonneg (add_nonneg (add_nonneg hr hi) hj) hk,
    add_eq_zero_iff_of_nonneg (add_nonneg hr hi) hj, add_eq_zero_iff_of_nonneg hr hi,
    mul_eq_zero, mul_eq_zero, mul_eq_zero] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  exact QuaternionAlgebra.ext (sq_eq_zero_iff.mp h₁)
    (sq_eq_zero_iff.mp (h₂.resolve_left hA.ne'))
    (sq_eq_zero_iff.mp (h₃.resolve_left hB.ne'))
    (sq_eq_zero_iff.mp (h₄.resolve_left (mul_pos hA hB).ne'))

/-- The multiplication group on the rational norm-one quaternions. -/
def UnitQuat (A B : ℚ) := {x : Quat A B // normSq x = 1}

instance instGroupUnitQuat : Group (UnitQuat A B) where
  one := ⟨1, normSq_one⟩
  mul x y := ⟨x.val * y.val, by rw [normSq_mul, x.property, y.property, mul_one]⟩
  inv x := ⟨star x.val, (normSq_star _).trans x.property⟩
  mul_assoc x y z := Subtype.ext (mul_assoc x.val y.val z.val)
  one_mul x := Subtype.ext (one_mul x.val)
  mul_one x := Subtype.ext (mul_one x.val)
  inv_mul_cancel x := Subtype.ext (show star x.val * x.val = 1 by
    rw [star_comm_self', mul_star, x.property, QuaternionAlgebra.coe_one])

private theorem inner_self (x : Quat A B) : inner x x = normSq x := by
  unfold inner normSq
  ring

private theorem inner_comm (x y : Quat A B) : inner x y = inner y x := by
  unfold inner
  ring

private theorem normSq_add (x y : Quat A B) :
    normSq (x + y) = normSq x + normSq y + 2 * inner x y := by
  simp [normSq, inner]
  ring

private theorem normSq_sub (x y : Quat A B) :
    normSq (x - y) = normSq x + normSq y - 2 * inner x y := by
  simp [normSq, inner]
  ring

/-- Left multiplication by a norm-one quaternion preserves the inner product. -/
theorem inner_mul_left (g x y : Quat A B) (hg : normSq g = 1) :
    inner (g * x) (g * y) = inner x y := by
  have h := normSq_add (g * x) (g * y)
  rw [← mul_add, normSq_mul g (x + y), normSq_mul g x, normSq_mul g y, hg,
    one_mul, one_mul, one_mul, normSq_add] at h
  linarith only [h]

/-- Right multiplication by a norm-one quaternion preserves the inner product. -/
theorem inner_mul_right (g x y : Quat A B) (hg : normSq g = 1) :
    inner (x * g) (y * g) = inner x y := by
  have h := normSq_add (x * g) (y * g)
  rw [← add_mul, normSq_mul (x + y) g, normSq_mul x g, normSq_mul y g, hg,
    mul_one, mul_one, mul_one, normSq_add] at h
  linarith only [h]

/-- The normalized, rational kernel on the norm-one group. -/
def kernel (x y : UnitQuat A B) : ℚ :=
  (1 + inner x.val y.val) / 2

theorem kernel_symm (x y : UnitQuat A B) : kernel x y = kernel y x := by
  rw [kernel, kernel, inner_comm]

@[simp] theorem kernel_self (x : UnitQuat A B) : kernel x x = 1 := by
  rw [kernel, inner_self, x.property]
  norm_num

theorem kernel_nonneg (hA : 0 < A) (hB : 0 < B) (x y : UnitQuat A B) :
    0 ≤ kernel x y := by
  have h := normSq_nonneg hA hB (x.val + y.val)
  rw [normSq_add, x.property, y.property] at h
  unfold kernel
  linarith only [h]

theorem kernel_le_one (hA : 0 < A) (hB : 0 < B) (x y : UnitQuat A B) :
    kernel x y ≤ 1 := by
  have h := normSq_nonneg hA hB (x.val - y.val)
  rw [normSq_sub, x.property, y.property] at h
  unfold kernel
  linarith only [h]

theorem kernel_eq_one_iff (hA : 0 < A) (hB : 0 < B) (x y : UnitQuat A B) :
    kernel x y = 1 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ kernel_self x⟩
  have hn : normSq (x.val - y.val) = 0 := by
    rw [normSq_sub, x.property, y.property]
    unfold kernel at h
    linarith only [h]
  exact Subtype.ext (sub_eq_zero.mp ((normSq_eq_zero hA hB _).mp hn))

theorem kernel_mul_left (g x y : UnitQuat A B) : kernel (g * x) (g * y) = kernel x y := by
  change (1 + inner (g.val * x.val) (g.val * y.val)) / 2 = kernel x y
  rw [inner_mul_left _ _ _ g.property]
  rfl

theorem kernel_mul_right (g x y : UnitQuat A B) : kernel (x * g) (y * g) = kernel x y := by
  change (1 + inner (x.val * g.val) (y.val * g.val)) / 2 = kernel x y
  rw [inner_mul_right _ _ _ g.property]
  rfl

/-- The negative of the quaternion identity is a point of zero overlap with the identity. -/
theorem exists_kernel_zero (A B : ℚ) : ∃ p : UnitQuat A B, kernel 1 p = 0 := by
  refine ⟨⟨-1, (normSq_neg _).trans normSq_one⟩, ?_⟩
  change (1 + inner (1 : Quat A B) (-1)) / 2 = 0
  norm_num [inner]


private theorem sum_mul_products {R ι : Type*} [CommSemiring R] [Fintype ι] (f : ι → R) :
    (∑ i, ∑ j, f i * f j) = (∑ i, f i) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]

private theorem sum_weighted_products {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : R) (f : ι → R) :
    (∑ i, ∑ j, a * (f i * f j)) = a * (∑ i, f i) ^ 2 := by
  simp_rw [← Finset.mul_sum _ _ a, sum_mul_products]

/-- The Gram form is the constant square plus the four weighted coordinate squares, scaled by
one half. The identity holds after casting the rational entries to any characteristic-zero field. -/
theorem kernel_gram_eq {R ι : Type*} [Field R] [CharZero R] [Fintype ι]
    (x : ι → UnitQuat A B) (w : ι → R) :
    (∑ i, ∑ j, w i * (kernel (x i) (x j) : R) * w j) =
      ((∑ i, w i) ^ 2 + (∑ i, w i * ((x i).val.re : R)) ^ 2 +
        (A : R) * (∑ i, w i * ((x i).val.imI : R)) ^ 2 +
        (B : R) * (∑ i, w i * ((x i).val.imJ : R)) ^ 2 +
        (A : R) * (B : R) * (∑ i, w i * ((x i).val.imK : R)) ^ 2) / 2 := by
  let re : ι → R := fun i => w i * ((x i).val.re : R)
  let imI : ι → R := fun i => w i * ((x i).val.imI : R)
  let imJ : ι → R := fun i => w i * ((x i).val.imJ : R)
  let imK : ι → R := fun i => w i * ((x i).val.imK : R)
  have hentry (i j : ι) :
      w i * (kernel (x i) (x j) : R) * w j =
        (w i * w j + re i * re j + (A : R) * (imI i * imI j) +
          (B : R) * (imJ i * imJ j) + (A : R) * (B : R) * (imK i * imK j)) * (2 : R)⁻¹ := by
    simp only [kernel, inner, Rat.cast_add, Rat.cast_mul, Rat.cast_one,
      re, imI, imJ, imK, div_eq_mul_inv]
    ring
  simp_rw [hentry, ← Finset.sum_mul, Finset.sum_add_distrib, sum_mul_products,
    sum_weighted_products, ← div_eq_mul_inv]
  rfl

/-- Every finite Gram form is nonnegative over any ordered field, including `ℚ` and `ℝ`. -/
theorem kernel_gram_nonneg {R ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] (hA : 0 < A) (hB : 0 < B) (x : ι → UnitQuat A B) (w : ι → R) :
    0 ≤ ∑ i, ∑ j, w i * (kernel (x i) (x j) : R) * w j := by
  have hA' : 0 ≤ (A : R) := Rat.cast_nonneg.mpr hA.le
  have hB' : 0 ≤ (B : R) := Rat.cast_nonneg.mpr hB.le
  rw [kernel_gram_eq]
  exact div_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hA' (sq_nonneg _)))
        (mul_nonneg hB' (sq_nonneg _)))
      (mul_nonneg (mul_nonneg hA' hB') (sq_nonneg _)))
    (by norm_num)

private theorem cayley_norm (a : ℚ) (ha : 0 < a) :
    ((1 - a) / (1 + a)) ^ 2 + a * (2 / (1 + a)) ^ 2 = 1 := by
  have hden : 0 < 1 + a := by linarith
  field_simp [hden.ne']
  ring

/-- Each group with positive weights has explicit rational elements that do not commute. -/
theorem exists_noncommuting (hA : 0 < A) (hB : 0 < B) :
    ∃ u v : UnitQuat A B, u * v ≠ v * u := by
  let u : UnitQuat A B := ⟨⟨(1 - A) / (1 + A), 2 / (1 + A), 0, 0⟩, by
    simpa [normSq] using cayley_norm A hA⟩
  let v : UnitQuat A B := ⟨⟨(1 - B) / (1 + B), 0, 2 / (1 + B), 0⟩, by
    simpa [normSq] using cayley_norm B hB⟩
  refine ⟨u, v, fun h => ?_⟩
  have hk := congrArg (fun q : UnitQuat A B => q.val.imK) h
  change (u.val * v.val).imK = (v.val * u.val).imK at hk
  simp [u, v] at hk
  have hI : 0 < 2 / (1 + A) := div_pos (by norm_num) (by linarith)
  have hJ : 0 < 2 / (1 + B) := div_pos (by norm_num) (by linarith)
  linarith only [hk, mul_pos hI hJ]

/-- Positive weights and explicit norm-one quaternions realize the prescribed readings. -/
theorem exists_quaternion_overlap_contrast (t d : ℚ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hd : d ^ 2 ≤ 1 - t) :
    ∃ A B : ℚ, 0 < A ∧ 0 < B ∧
      ∃ y z : UnitQuat A B, kernel 1 y = t ∧ kernel 1 z - kernel y z = d := by
  obtain ⟨A, B, c, e, r, i, j, hA, hB, hy, hz, hov, hcontrast⟩ :=
    exists_rational_coordinates t d ht₀ ht₁ hd
  let y : UnitQuat A B := ⟨⟨c, e, 0, 0⟩, by simpa [normSq] using hy⟩
  let z : UnitQuat A B := ⟨⟨r, i, j, 0⟩, by simpa [normSq] using hz⟩
  refine ⟨A, B, hA, hB, y, z, ?_, ?_⟩
  · change (1 + inner (1 : Quat A B) y.val) / 2 = t
    simp [inner, y]
    linarith only [hov]
  · change (1 + inner (1 : Quat A B) z.val) / 2 - (1 + inner y.val z.val) / 2 = d
    simp [inner, y, z]
    linarith only [hcontrast]

/-- A rational kernel with the normalization, order, separation, and finite Gram laws, and both
translation laws. Gram nonnegativity holds over every ordered field. -/
structure IsSeparatedBiInvariantKernel {G : Type*} [Group G] (K : G → G → ℚ) : Prop where
  symm (x y : G) : K x y = K y x
  normalized (x : G) : K x x = 1
  nonneg (x y : G) : 0 ≤ K x y
  le_one (x y : G) : K x y ≤ 1
  separated (x y : G) : K x y = 1 ↔ x = y
  gram_nonneg {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
      (n : ℕ) (x : Fin n → G) (w : Fin n → R) :
      0 ≤ ∑ i, ∑ j, w i * (K (x i) (x j) : R) * w j
  left_invariant (g x y : G) : K (g * x) (g * y) = K x y
  right_invariant (g x y : G) : K (x * g) (y * g) = K x y

/-- Every admissible rational overlap and signed contrast is realized on a nonabelian group by a
separated rational bi-invariant PSD kernel which attains zero. -/
theorem exists_rational_biinvariant_kernel (t d : ℚ) (ht₀ : 0 ≤ t)
    (hd : d ^ 2 ≤ 1 - t) :
    ∃ (G : Type) (_ : Group G) (K : G → G → ℚ),
      IsSeparatedBiInvariantKernel K ∧ (∃ p : G, K 1 p = 0) ∧
      (∃ u v : G, u * v ≠ v * u) ∧ (∃ y z : G, K 1 y = t ∧ K 1 z - K y z = d) := by
  obtain ⟨A, B, hA, hB, y, z, hov, hcontrast⟩ :=
    exists_quaternion_overlap_contrast t d ht₀ (by linarith only [sq_nonneg d, hd]) hd
  refine ⟨UnitQuat A B, inferInstance, kernel, ?_, exists_kernel_zero A B,
    exists_noncommuting hA hB, y, z, hov, hcontrast⟩
  exact
    { symm := kernel_symm
      normalized := kernel_self
      nonneg := kernel_nonneg hA hB
      le_one := kernel_le_one hA hB
      separated := kernel_eq_one_iff hA hB
      gram_nonneg := fun _ => kernel_gram_nonneg hA hB
      left_invariant := kernel_mul_left
      right_invariant := kernel_mul_right }

end Omega.Geometry.QuaternionContrast
