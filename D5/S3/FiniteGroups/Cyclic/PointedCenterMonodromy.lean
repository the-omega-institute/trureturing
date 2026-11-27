/- GID: D5/S3/FiniteGroups/Cyclic/PointedCenterMonodromy
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/PointedCenterMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.CategoryTheory.Monoidal.Center]
   utility: none
   digest: The order power of a self-half-braiding scalar equals the cyclic associator product. -/

import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.SingleObj
import D5.S3.FiniteGroups.Cyclic.CyclicAssociatorObstruction
import OmegaBuild.Commands

/-!
# The cyclic associator product from a half-braiding

Use a functor to `SingleObj A` to read morphisms as scalars in a commutative group `A`.
In the skeletal pointed monoidal groupoid attached to a normalized three-cocycle,
objects are group elements and tensor on objects is group multiplication. Each
object has automorphism group `A`, and distinct objects have empty hom sets.
Composition and tensor of morphisms multiply their labels. The functor forgets
the object index and keeps the morphism label. Both whiskerings preserve labels
because identity morphisms have label `1`. The family `X` is the identity on
indices, the associator hom has the cocycle as its label, and both unitors have
label `1`. The cocycle condition gives the pentagon and normalization gives the
triangle. These data also restrict to the cyclic subgroup of the generator.

The coefficient of the self-half-braiding is the scalar in the power identity.
An application to a VOA still needs a comparison identifying this scalar with
the canonical ribbon twist of the corresponding central object.
-/

compile_only_with_mathlib

set_option autoImplicit false

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace D5.S3.FiniteGroups.Cyclic.PointedCenterMonodromy

open CyclicAssociatorObstruction (cyclicProduct)

universe u v w t

variable {G : Type u} {A : Type v} {C : Type w}
  [Group G] [CommGroup A] [Category.{t} C] [MonoidalCategory C]

variable (F : C ⥤ SingleObj A) (X : G → C)

/-- The scalar of the associator in the direction `(X a ⊗ X b) ⊗ X c ⟶ X a ⊗ (X b ⊗ X c)`. -/
def associatorScalar (a b c : G) : A :=
  F.map (α_ (X a) (X b) (X c)).hom

/-- The scalar of a component of an actual Mathlib half-braiding. -/
def halfBraidingScalar {U : C} (b : HalfBraiding U) (h : G) : A :=
  F.map (b.β (X h)).hom

-- `SingleObj` composes in the opposite order from the displayed scalar product.
private theorem map_comp_mul {U V W : C} (f : U ⟶ V) (k : V ⟶ W) :
    (F.map (f ≫ k) : A) = (F.map f : A) * (F.map k : A) := by
  rw [F.map_comp, SingleObj.comp_as_mul, mul_comm]

private theorem map_iso_inv {U V : C} (e : U ≅ V) :
    (F.map e.inv : A) = (F.map e.hom : A)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_comp_mul F, e.hom_inv_id, F.map_id, SingleObj.id_as_one]

section

variable (hTensor : ∀ a b : G, X (a * b) = X a ⊗ X b)
  (hLeft : ∀ (U : C) {V W : C} (f : V ⟶ W), (F.map (U ◁ f) : A) = F.map f)
  (hRight : ∀ {U V : C} (f : U ⟶ V) (W : C), (F.map (f ▷ W) : A) = F.map f)
  (g : G) (b : HalfBraiding (X g))

include hTensor hLeft hRight

/-- In the half-braiding law at `X h` and `X g`, the forward and inverse
associators at `(X h, X g, X g)` cancel after taking scalars. -/
theorem halfBraidingScalar_mul (h : G) :
    halfBraidingScalar F X b h * halfBraidingScalar F X b g =
      associatorScalar F X g h g * halfBraidingScalar F X b (h * g) := by
  have hmonoidal :
      halfBraidingScalar F X b (h * g) =
        (associatorScalar F X g h g)⁻¹ *
          (halfBraidingScalar F X b h *
            (associatorScalar F X h g g *
              (halfBraidingScalar F X b g * (associatorScalar F X h g g)⁻¹))) := by
    unfold halfBraidingScalar associatorScalar
    rw [hTensor h g]
    simpa only [map_comp_mul, map_iso_inv, hLeft, hRight] using
      congrArg (fun f => (F.map f : A)) (b.monoidal (X h) (X g))
  have hcancel (a s : A) : a * (s * a⁻¹) = s := by
    rw [mul_comm s (a⁻¹), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hmonoidal, hcancel (associatorScalar F X h g g) (halfBraidingScalar F X b g),
    ← mul_assoc, mul_inv_cancel, one_mul]

/-- The triangle identity gives the normalized unit component when the two
unitors of `X g` have the same scalar. -/
theorem halfBraidingScalar_one (hUnit : X 1 = 𝟙_ C)
    (hUnitors : (F.map (ρ_ (X g)).hom : A) = F.map (λ_ (X g)).hom) :
    halfBraidingScalar F X b 1 = 1 := by
  have hmul :
      halfBraidingScalar F X b 1 * halfBraidingScalar F X b g =
        associatorScalar F X g 1 g * halfBraidingScalar F X b g := by
    simpa only [one_mul] using halfBraidingScalar_mul F X hTensor hLeft hRight g b (1 : G)
  have htriangle :
      associatorScalar F X g 1 g * (F.map (λ_ (X g)).hom : A) = F.map (ρ_ (X g)).hom := by
    unfold associatorScalar
    rw [hUnit]
    simpa only [map_comp_mul, hLeft, hRight] using
      congrArg (fun f => (F.map f : A)) (MonoidalCategory.triangle (X g) (X g))
  rw [mul_right_cancel hmul]
  apply mul_right_cancel (b := (F.map (λ_ (X g)).hom : A))
  rw [one_mul, htriangle, hUnitors]

/-- The order power of the self-half-braiding scalar is the cyclic product of
the associator hom scalars. The unit component cancels at the two endpoints. -/
theorem pow_orderOf_eq_cyclicProduct :
    halfBraidingScalar F X b g ^ orderOf g = cyclicProduct (associatorScalar F X) g := by
  let θ : G → A := halfBraidingScalar F X b
  let α : G → G → G → A := associatorScalar F X
  have hstep (i : ℕ) : θ (g ^ i) * θ g = α g (g ^ i) g * θ (g ^ (i + 1)) := by
    rw [pow_succ g i]
    exact halfBraidingScalar_mul F X hTensor hLeft hRight g b (g ^ i)
  have hpow (n : ℕ) :
      θ 1 * θ g ^ n = (∏ i ∈ Finset.range n, α g (g ^ i) g) * θ (g ^ n) := by
    induction n with
    | zero => simp only [pow_zero, Finset.range_zero, Finset.prod_empty, mul_one, one_mul]
    | succ n ih =>
        rw [pow_succ (θ g) n, ← mul_assoc, ih, mul_assoc, hstep n,
          Finset.prod_range_succ, mul_assoc]
  have hend : θ 1 * θ g ^ orderOf g = cyclicProduct α g * θ 1 := by
    simpa only [pow_orderOf_eq_one, cyclicProduct] using hpow (orderOf g)
  exact mul_left_cancel (hend.trans (mul_comm (cyclicProduct α g) (θ 1)))

end

end D5.S3.FiniteGroups.Cyclic.PointedCenterMonodromy
