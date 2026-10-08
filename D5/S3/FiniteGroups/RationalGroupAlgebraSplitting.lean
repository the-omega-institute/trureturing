/- GID: D5/S3/FiniteGroups/RationalGroupAlgebraSplitting
   generality: G
   utility: augmentation-first rational simple factors and their exact uniform kernel
   digest: The quotient by uniform coefficients splits rational group algebra into augmentation and all nontrivial Wedderburn factors, with a faithful uniform-kernel characterization.
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.FiniteGroups.RationalGroupAlgebraSplitting

universe u
variable {H : Type u} [Group H] [Fintype H]

abbrev augmentation : MonoidAlgebra ℚ H →ₐ[ℚ] ℚ :=
  MonoidAlgebra.lift ℚ ℚ H (1 : H →* ℚ)

def Uniform (x : MonoidAlgebra ℚ H) : Prop := ∀ g : H, x.coeff g = x.coeff 1

theorem augmentation_eq_sum (x : MonoidAlgebra ℚ H) : augmentation x = ∑ g : H, x.coeff g := by
  classical
  rw [augmentation, MonoidAlgebra.lift_apply']
  simp only [MonoidHom.one_apply, Algebra.algebraMap_self, RingHom.id_apply, mul_one]
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

@[simp] theorem augmentation_single (g : H) (c : ℚ) : augmentation (MonoidAlgebra.single g c) = c := by
  simp [augmentation, MonoidAlgebra.lift_single]

private theorem uniform_mul_left (x y : MonoidAlgebra ℚ H) (hy : Uniform y) :
    Uniform (x*y) := by
  change ∀ g, y.coeff g = y.coeff 1 at hy
  intro g
  rw [MonoidAlgebra.coeff_mul_apply_left, MonoidAlgebra.coeff_mul_apply_left]
  simp_rw [hy]

private theorem uniform_mul_right (x y : MonoidAlgebra ℚ H) (hx : Uniform x) :
    Uniform (x*y) := by
  change ∀ g, x.coeff g = x.coeff 1 at hx
  intro g
  rw [MonoidAlgebra.coeff_mul_apply_right, MonoidAlgebra.coeff_mul_apply_right]
  simp_rw [hx]

private theorem uniform_smul (c : ℚ) (x : MonoidAlgebra ℚ H) (hx : Uniform x) :
    Uniform (c • x) := by
  intro g
  simp only [MonoidAlgebra.coeff_smul_apply, hx g]

/-- Exact augmentation action on a uniform left factor, by public convolution. -/
private theorem uniform_mul_eq_aug_smul (x y : MonoidAlgebra ℚ H) (hx : Uniform x) :
    x*y = augmentation y • x := by
  classical
  change ∀ g, x.coeff g = x.coeff 1 at hx
  ext g
  rw [MonoidAlgebra.coeff_mul_apply_right]
  rw [Finsupp.sum_fintype _ _ (fun _ => mul_zero _)]
  simp_rw [hx]
  rw [← Finset.mul_sum, augmentation_eq_sum]
  simp only [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, hx g]
  exact mul_comm _ _

/-- Actual Q[H]-ideal whose elements have constant coefficients. -/
def uniformIdeal (H : Type*) [Group H] [Fintype H] : Ideal (MonoidAlgebra ℚ H) where
  carrier := {x | Uniform x}
  zero_mem' := by intro g; rfl
  add_mem' := by
    intro x y hx hy g
    change x.coeff g + y.coeff g = x.coeff 1 + y.coeff 1
    rw [hx g, hy g]
  smul_mem' := by
    intro x y hy
    exact uniform_mul_left x y hy

instance uniformIdeal_twoSided : (uniformIdeal H).IsTwoSided where
  mul_mem_of_left y hx := uniform_mul_right _ y hx

/-- Original normalized sum e_H: each actual coefficient equals 1/|H|. -/
def average (H : Type*) [Group H] [Fintype H] : MonoidAlgebra ℚ H :=
  ∑ g : H, MonoidAlgebra.single g (Fintype.card H : ℚ)⁻¹

@[simp] theorem average_coeff (g : H) :
    (average H).coeff g = (Fintype.card H : ℚ)⁻¹ := by
  classical
  simp [average, MonoidAlgebra.coeff_sum, Finsupp.sum_apply]

private theorem average_uniform : Uniform (average H) := by
  intro g
  rw [average_coeff, average_coeff]

@[simp] theorem augmentation_average : augmentation (average H) = 1 := by
  have hcard : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [augmentation_eq_sum]
  simp only [average_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ hcard

private theorem uniform_augmentation_zero (x : MonoidAlgebra ℚ H)
    (hx : Uniform x) (haug : augmentation x = 0) : x = 0 := by
  have hcard : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Fintype.card H : ℚ) * x.coeff 1 = 0 := by
    rw [augmentation_eq_sum] at haug
    have hx' (g : H) : x.coeff g = x.coeff 1 := hx g
    simpa only [hx', Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using haug
  have h1 : x.coeff 1 = 0 := (mul_eq_zero.mp hs).resolve_left hcard
  ext g
  exact (hx g).trans h1

abbrev Reduced (H : Type*) [Group H] [Fintype H] :=
  MonoidAlgebra ℚ H ⧸ uniformIdeal H

/-- The first coordinate is literally augmentation; the second is the actual
quotient removing the uniform ideal. -/
def splitHom (H : Type*) [Group H] [Fintype H] :
    MonoidAlgebra ℚ H →ₐ[ℚ] ℚ × Reduced H :=
  augmentation.prod (Ideal.Quotient.mkₐ ℚ (uniformIdeal H))

private theorem splitHom_injective : Function.Injective (splitHom H) := by
  intro x y hxy
  have haug : augmentation x = augmentation y := congrArg Prod.fst hxy
  have hquot : Ideal.Quotient.mk (uniformIdeal H) x =
      Ideal.Quotient.mk (uniformIdeal H) y := congrArg Prod.snd hxy
  have hu : Uniform (x-y) := (Ideal.Quotient.eq.mp hquot)
  apply sub_eq_zero.mp
  exact uniform_augmentation_zero (x-y) hu (by rw [map_sub, haug, sub_self])

private theorem splitHom_surjective : Function.Surjective (splitHom H) := by
  rintro ⟨a,z⟩
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨x + (a-augmentation x) • average H, ?_⟩
  apply Prod.ext
  · change augmentation (x + (a-augmentation x) • average H) = a
    rw [map_add, map_smul, augmentation_average, smul_eq_mul, mul_one]
    ring
  · change Ideal.Quotient.mk (uniformIdeal H) (x + (a-augmentation x) • average H) = _
    rw [map_add]
    have hz : Ideal.Quotient.mk (uniformIdeal H) ((a-augmentation x) • average H) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (uniform_smul _ _ average_uniform)
    rw [hz, add_zero]

/-- Actual augmentation-first splitting, constructed without choosing a
trivial factor from an arbitrary list of Wedderburn factors. -/
def augmentationSplit (H : Type*) [Group H] [Fintype H] :
    MonoidAlgebra ℚ H ≃ₐ[ℚ] ℚ × Reduced H :=
  AlgEquiv.ofBijective (splitHom H) ⟨splitHom_injective,splitHom_surjective⟩

@[simp] theorem augmentationSplit_first (x : MonoidAlgebra ℚ H) :
    (augmentationSplit H x).1 = augmentation x := rfl

/-- Nontrivial H leaves a nontrivial quotient, so its Wedderburn index set cannot
be empty. This branch is not used to invent b_H for a trivial group. -/
instance reduced_nontrivial [Nontrivial H] : Nontrivial (Reduced H) := by
  apply nontrivial_of_ne (1 : Reduced H) 0
  intro h10
  have hu : Uniform (1 : MonoidAlgebra ℚ H) := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (show Ideal.Quotient.mk (uniformIdeal H) (1 : MonoidAlgebra ℚ H) = 0 by
        simpa only [map_one] using h10)
  obtain ⟨g,hg⟩ := exists_ne (1 : H)
  have hbad : (0 : ℚ) = 1 := by
    simpa [MonoidAlgebra.one_def, hg, Ne.symm hg] using hu g
  exact zero_ne_one hbad

/-- A rational uniform element is its augmentation times the normalized
uniform idempotent. The formula includes zero. -/
theorem uniform_eq_augmentation_smul_average (x : MonoidAlgebra ℚ H) (hx : Uniform x) :
    x = augmentation x • average H := by
  apply (augmentationSplit H).injective
  apply Prod.ext
  · change augmentation x = augmentation (augmentation x • average H)
    rw [map_smul, augmentation_average, smul_eq_mul, mul_one]
  · change Ideal.Quotient.mk (uniformIdeal H) x =
      Ideal.Quotient.mk (uniformIdeal H) (augmentation x • average H)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx,
      Ideal.Quotient.eq_zero_iff_mem.mpr (uniform_smul _ _ average_uniform)]

/-- A faithful product decomposition whose first factor is augmentation has
precisely the uniform group-algebra elements in the kernel of its tail. -/
theorem uniform_iff_tail_zero {S : Type*} [Ring S] [Algebra ℚ S]
    (phi : MonoidAlgebra ℚ H ≃ₐ[ℚ] ℚ × S)
    (hfirst : ∀ x, (phi x).1 = augmentation x)
    (x : MonoidAlgebra ℚ H) : Uniform x ↔ (phi x).2 = 0 := by
  have hfst (z : MonoidAlgebra ℚ H) : (phi z).1 = augmentation z := hfirst z
  constructor
  · intro hx
    let p : MonoidAlgebra ℚ H := phi.symm (1,0)
    have hp : augmentation p = 1 := by
      rw [← hfst]
      simp [p]
    have hxp : x*p = x := by
      rw [uniform_mul_eq_aug_smul x p hx, hp, one_smul]
    have htail := congrArg (fun z : MonoidAlgebra ℚ H => (phi z).2) hxp
    simpa [map_mul, p] using htail.symm
  · intro hx
    have htranslate (g : H) : MonoidAlgebra.single g 1 * x = x := by
      apply phi.injective
      apply Prod.ext
      · change (phi (MonoidAlgebra.single g 1 * x)).1 = (phi x).1
        rw [hfst, hfst, map_mul, augmentation_single, one_mul]
      · rw [map_mul]
        change (phi (MonoidAlgebra.single g 1)).2 * (phi x).2 = (phi x).2
        rw [hx, mul_zero]
    intro t
    have hcoeff := congrArg (fun z : MonoidAlgebra ℚ H => z.coeff 1) (htranslate (t⁻¹))
    simpa only [MonoidAlgebra.coeff_single_mul_apply, one_mul, inv_inv, mul_one] using hcoeff

instance reduced_finite : Module.Finite ℚ (Reduced H) := by
  letI : Module.Finite ℚ (MonoidAlgebra ℚ H) :=
    Module.Finite.of_basis (MonoidAlgebra.basis H ℚ)
  exact Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ ℚ (uniformIdeal H)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℚ (uniformIdeal H))

instance reduced_semisimple : IsSemisimpleRing (Reduced H) := by
  letI : NeZero (Nat.card H : ℚ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  letI : IsSemisimpleRing (MonoidAlgebra ℚ H) := inferInstance
  exact RingHom.isSemisimpleRing_of_surjective
    (Ideal.Quotient.mk (uniformIdeal H)) Ideal.Quotient.mk_surjective

/-- An augmentation-first rational decomposition with the original orders
of its nontrivial simple matrix factors. -/
structure RationalDecomposition (H : Type u) [Group H] [Fintype H] where
  count : ℕ
  count_pos : 0 < count
  DivisionAlgebra : Fin count → Type u
  [divisionRing : ∀ l, DivisionRing (DivisionAlgebra l)]
  [algebra : ∀ l, Algebra ℚ (DivisionAlgebra l)]
  [finite : ∀ l, Module.Finite ℚ (DivisionAlgebra l)]
  order : Fin count → ℕ
  order_pos : ∀ l, 0 < order l
  equiv : MonoidAlgebra ℚ H ≃ₐ[ℚ]
    ℚ × (∀ l, Matrix (Fin (order l)) (Fin (order l)) (DivisionAlgebra l))
  augmentation_first : ∀ x, (equiv x).1 = augmentation x

attribute [instance] RationalDecomposition.divisionRing RationalDecomposition.algebra
  RationalDecomposition.finite

/-- Maschke and the finite Wedderburn theorem applied to the actual quotient
produce all nontrivial blocks, with augmentation first by construction. -/
theorem nonempty_decomposition [Nontrivial H] : Nonempty (RationalDecomposition H) := by
  obtain ⟨m,D,r,instD,instA,instFinite,hr,⟨psi⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite ℚ (Reduced H)
  letI := instD
  letI := instA
  letI := instFinite
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have h01 : psi (0 : Reduced H) = psi 1 := by
      funext i
      exact Fin.elim0 i
    exact zero_ne_one (psi.injective h01)
  let phi := (augmentationSplit H).trans (AlgEquiv.prodCongr (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) psi)
  exact ⟨{
    count := m
    count_pos := hm
    DivisionAlgebra := D
    divisionRing := instD
    algebra := instA
    finite := instFinite
    order := r
    order_pos := fun l => by
      letI := hr l
      exact Nat.pos_of_ne_zero (NeZero.ne (r l))
    equiv := phi
    augmentation_first := fun x => augmentationSplit_first x }⟩

end D5.S3.FiniteGroups.RationalGroupAlgebraSplitting
