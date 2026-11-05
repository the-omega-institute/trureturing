/- GID: D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearMap, mathlib/module/Mathlib.LinearAlgebra.Dimension.Constructions, mathlib/module/Mathlib.Algebra.Order.Ring.Unbundled.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.claim; result=D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result; claim=D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.claim
   digest: An anisotropic quadratic multiplication obstructs the infinite-field dimension bound. -/

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Nilpotent bilinear algebras over infinite fields

An algebra without an identity is a vector space with a bilinear multiplication.
Associativity and commutativity are stated as laws for that actual multiplication.
A list of length `k` followed by its terminal element is a product of length `k+1`.
Thus the common product-length condition includes every positive nilpotence length.
For positive `n`, folding `n-1` copies of `v` onto `v` is its ordinary `n`-th power.

The quadratic construction uses the same scalar field for the ambient vector
space, its subspace, the bilinear law and both dimensions. Over the rationals,
its square on the first two coordinates is anisotropic, while every product of
three elements is zero. This is a two-step associative algebra; the cubing algebra
in Bergman's Example 20 is nonassociative and is not used as a law supplier.
-/

namespace D5.S0.Certificates.Algebra.BergmanInfiniteFieldRefutation

/-- Common nilpotence: every product of one fixed positive length is zero. -/
def CommonNilpotent {F R : Type*} [Field F] [AddCommGroup R] [Module F R]
    (μ : R →ₗ[F] R →ₗ[F] R) : Prop :=
  ∃ k : ℕ, ∀ (xs : List R) (z : R), xs.length = k →
    xs.foldr (fun x y => μ x y) z = 0

/-- The complete infinite-field assertion in the field-condition branch of Question 19. -/
def claim : Prop :=
  ∀ (F : Type) [Field F] [Infinite F]
    (R : Type) [AddCommGroup R] [Module F R] [FiniteDimensional F R]
    (μ : R →ₗ[F] R →ₗ[F] R),
    (∀ x y z : R, μ (μ x y) z = μ x (μ y z)) →
    (∀ x y : R, μ x y = μ y x) →
    CommonNilpotent μ →
    ∀ (V : Submodule F R) (n : ℕ), 0 < n →
      (∀ v ∈ V, v ≠ 0 →
        (List.replicate (n - 1) v).foldr (fun x y => μ x y) v ≠ 0) →
      n * Module.finrank F V ≤ Module.finrank F R

/-- Two coordinates multiply into an annihilating third coordinate. -/
def product (F : Type*) [Field F] :
    ((F × F) × F) →ₗ[F] ((F × F) × F) →ₗ[F] ((F × F) × F) :=
  LinearMap.mk₂ F
    (fun x y => ((0, 0), x.1.1 * y.1.1 + x.1.2 * y.1.2))
    (by intro x x' y; ext <;> simp; ring)
    (by intro c x y; ext <;> simp [smul_eq_mul]; ring)
    (by intro x y y'; ext <;> simp; ring)
    (by intro c x y; ext <;> simp [smul_eq_mul]; ring)

/-- The actual two-dimensional linear subspace, defined as the range of an injection. -/
def modelSubspace (F : Type*) [Field F] : Submodule F ((F × F) × F) :=
  LinearMap.range (LinearMap.inl F (F × F) F)

/-- The infinite-field dimension assertion is refuted at exponent two over the rationals. -/
theorem result : ¬ claim := by
  intro h
  have hassoc : ∀ x y z : ((ℚ × ℚ) × ℚ),
      product ℚ (product ℚ x y) z = product ℚ x (product ℚ y z) := by
    intro x y z
    ext <;> simp [product]
  have hcomm : ∀ x y : ((ℚ × ℚ) × ℚ), product ℚ x y = product ℚ y x := by
    intro x y
    ext <;> simp [product, mul_comm]
  have hnil : CommonNilpotent (product ℚ) := by
    refine ⟨2, ?_⟩
    intro xs z hlen
    obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
    simp [product]
  have hpower : ∀ v ∈ modelSubspace ℚ, v ≠ 0 →
      (List.replicate (2 - 1) v).foldr (fun x y => product ℚ x y) v ≠ 0 := by
    intro v hv hv0 hp
    obtain ⟨w, rfl⟩ := hv
    have hsq : w.1 * w.1 + w.2 * w.2 = 0 := by
      simpa [product] using congrArg Prod.snd hp
    obtain ⟨hw1, hw2⟩ := mul_self_add_mul_self_eq_zero.mp hsq
    apply hv0
    change (w, (0 : ℚ)) = 0
    have hw : w = (0, 0) := Prod.ext hw1 hw2
    rw [hw]
    rfl
  have hinj : Function.Injective (LinearMap.inl ℚ (ℚ × ℚ) ℚ) := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  have hV : Module.finrank ℚ (modelSubspace ℚ) = 2 := by
    change Module.finrank ℚ (LinearMap.range (LinearMap.inl ℚ (ℚ × ℚ) ℚ)) = 2
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  have hR : Module.finrank ℚ ((ℚ × ℚ) × ℚ) = 3 := by simp
  have hdim := h ℚ ((ℚ × ℚ) × ℚ) (product ℚ) hassoc hcomm hnil
    (modelSubspace ℚ) 2 (by decide) hpower
  norm_num [hV, hR] at hdim

end D5.S0.Certificates.Algebra.BergmanInfiniteFieldRefutation
