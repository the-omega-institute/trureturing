/- GID: D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/FusionCenterMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.CategoryTheory.Monoidal.Center, mathlib/module/Mathlib.CategoryTheory.Monoidal.Linear]
   utility: none
   digest: A genuine half-braiding computes the cyclic product of the associator transported through fusion isomorphisms. -/

import D5.S3.FiniteGroups.Cyclic.CyclicAssociatorObstruction
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Basic.Complex.Basic
import OmegaBuild.Commands

/-!
The associator is read in the coordinates of chosen fusion isomorphisms.
A half-braiding gives the successive power comparisons via its hexagon and
naturality. The two occurrences of the unit-degree comparison cancel upon
telescoping, so the choice of fusion isomorphisms requires no unit normalization.
-/

compile_only_with_mathlib

set_option autoImplicit false

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace D5.S3.FiniteGroups.Cyclic.FusionCenterMonodromy

open CyclicAssociatorObstruction (cyclicProduct cyclicProduct_eq_one_of_mem twoCoboundary)

universe u v w

variable {G : Type u} {C : Type v} [Group G] [Category.{w} C]
  [MonoidalCategory C] [Preadditive C] [Linear ℂ C]

/-- Representatives with chosen fusion maps and endomorphisms spanned freely by the identity. -/
structure FusionCoordinates (G : Type u) (C : Type v) [Group G] [Category.{w} C]
    [MonoidalCategory C] [Preadditive C] [Linear ℂ C] where
  obj : G → C
  μ : ∀ a b, obj a ⊗ obj b ≅ obj (a * b)
  scalarIdentity : ∀ a, Function.Bijective (fun z : ℂ => z • 𝟙 (obj a))

namespace FusionCoordinates

variable (F : FusionCoordinates G C)

private noncomputable def endomorphismScalar (a : G) (f : F.obj a ⟶ F.obj a) : ℂ :=
  Classical.choose ((F.scalarIdentity a).2 f)

private theorem endomorphismScalar_smul (a : G) (f : F.obj a ⟶ F.obj a) :
    F.endomorphismScalar a f • 𝟙 (F.obj a) = f :=
  Classical.choose_spec ((F.scalarIdentity a).2 f)

private noncomputable def isoScalar (a : G) (e : F.obj a ≅ F.obj a) : ℂˣ := by
  let z := F.endomorphismScalar a e.hom
  let w := F.endomorphismScalar a e.inv
  have hz : z • 𝟙 (F.obj a) = e.hom := F.endomorphismScalar_smul a e.hom
  have hw : w • 𝟙 (F.obj a) = e.inv := F.endomorphismScalar_smul a e.inv
  have hzw : z * w = 1 := by
    apply (F.scalarIdentity a).1
    change (z * w) • 𝟙 (F.obj a) = (1 : ℂ) • 𝟙 (F.obj a)
    calc
      _ = (z • 𝟙 (F.obj a)) ≫ (w • 𝟙 (F.obj a)) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
        rw [mul_comm z w]
      _ = _ := by rw [hz, hw, e.hom_inv_id, one_smul]
  exact ⟨z, w, hzw, (mul_comm w z).trans hzw⟩

private noncomputable def compare {Y : C} (a : G) (p q : Y ≅ F.obj a) : ℂˣ :=
  F.isoScalar a (p.symm ≪≫ q)

private theorem compare_hom {Y : C} (a : G) (p q : Y ≅ F.obj a) :
    q.hom = (F.compare a p q : ℂ) • p.hom := by
  have h : (F.compare a p q : ℂ) • 𝟙 (F.obj a) = (p.symm ≪≫ q).hom :=
    F.endomorphismScalar_smul a (p.symm ≪≫ q).hom
  simpa only [Linear.comp_smul, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
    p.hom_inv_id_assoc] using (congrArg (fun f => p.hom ≫ f) h).symm

private theorem smul_hom_injective {Y : C} (a : G) (p : Y ≅ F.obj a) :
    Function.Injective (fun z : ℂ => z • p.hom) := by
  intro z w h
  apply (F.scalarIdentity a).1
  simpa only [Linear.comp_smul, p.inv_hom_id] using
    congrArg (fun f : Y ⟶ F.obj a => p.inv ≫ f) h

private def fuseLeft (a b c : G) : (F.obj a ⊗ F.obj b) ⊗ F.obj c ≅ F.obj ((a * b) * c) :=
  whiskerRightIso (F.μ a b) (F.obj c) ≪≫ F.μ (a * b) c

private def fuseRight (a b c : G) : F.obj a ⊗ (F.obj b ⊗ F.obj c) ≅ F.obj (a * (b * c)) :=
  whiskerLeftIso (F.obj a) (F.μ b c) ≪≫ F.μ a (b * c)

/-- Reassociation in fusion coordinates, read in the direction of the associator hom. -/
def reassociation (a b c : G) : F.obj ((a * b) * c) ≅ F.obj ((a * b) * c) :=
  (F.fuseLeft a b c).symm ≪≫
    (α_ (F.obj a) (F.obj b) (F.obj c)) ≪≫ F.fuseRight a b c ≪≫
    eqToIso (congrArg F.obj (mul_assoc a b c).symm)

/-- The scalar of the actual associator after identifying its source and target by fusion. -/
noncomputable def associatorScalar (a b c : G) : ℂˣ :=
  F.isoScalar ((a * b) * c) (F.reassociation a b c)

/-- The reassociation hom acts by the associator scalar on the fused object. -/
theorem reassociation_hom (a b c : G) :
    (F.reassociation a b c).hom =
      (F.associatorScalar a b c : ℂ) • 𝟙 (F.obj ((a * b) * c)) :=
  (F.endomorphismScalar_smul ((a * b) * c) (F.reassociation a b c).hom).symm

private theorem associator_comp_fuseRight (a b c : G) :
    (α_ (F.obj a) (F.obj b) (F.obj c)).hom ≫ (F.fuseRight a b c).hom ≫
        eqToHom (congrArg F.obj (mul_assoc a b c).symm) =
      (F.associatorScalar a b c : ℂ) • (F.fuseLeft a b c).hom := by
  simpa only [reassociation, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Linear.comp_smul,
    Category.comp_id, (F.fuseLeft a b c).hom_inv_id_assoc] using
    congrArg (fun f => (F.fuseLeft a b c).hom ≫ f) (F.reassociation_hom a b c)

/-- Compare the two fusion maps across the given half-braiding at a commuting degree. -/
noncomputable def halfBraidingScalar {g h : G} (b : HalfBraiding (F.obj g))
    (hc : Commute g h) : ℂˣ :=
  F.compare (g * h) (F.μ g h)
    (b.β (F.obj h) ≪≫ F.μ h g ≪≫ eqToIso (congrArg F.obj hc.eq.symm))

private theorem halfBraiding_comp_fusion {g h : G} (b : HalfBraiding (F.obj g))
    (hc : Commute g h) :
    (b.β (F.obj h)).hom ≫ (F.μ h g).hom =
      (F.halfBraidingScalar b hc : ℂ) • ((F.μ g h).hom ≫ eqToHom (congrArg F.obj hc.eq)) := by
  have hcomparison := F.compare_hom (g * h) (F.μ g h)
    (b.β (F.obj h) ≪≫ F.μ h g ≪≫ eqToIso (congrArg F.obj hc.eq.symm))
  simpa only [halfBraidingScalar, Iso.trans_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, Linear.smul_comp] using
    congrArg (fun f : F.obj g ⊗ F.obj h ⟶ F.obj (g * h) =>
      f ≫ eqToHom (congrArg F.obj hc.eq)) hcomparison

private theorem self_halfBraiding_hom (g : G) (b : HalfBraiding (F.obj g)) :
    (b.β (F.obj g)).hom = (F.halfBraidingScalar b (Commute.refl g) : ℂ) •
      𝟙 (F.obj g ⊗ F.obj g) := by
  apply (cancel_mono (F.μ g g).hom).mp
  simpa only [eqToHom_refl, Category.comp_id, Linear.smul_comp, Category.id_comp] using
    F.halfBraiding_comp_fusion b (Commute.refl g)

private theorem halfBraidingScalar_congr {g h k : G} (b : HalfBraiding (F.obj g))
    (hh : Commute g h) (hk : Commute g k) (p : h = k) :
    F.halfBraidingScalar b hh = F.halfBraidingScalar b hk := by
  subst k
  rfl

private theorem transport_whiskerRight_fusion {a a' : G} (p : a = a') (c : G) :
    (eqToHom (congrArg F.obj p) ▷ F.obj c) ≫ (F.μ a' c).hom =
      (F.μ a c).hom ≫ eqToHom (congrArg F.obj (congrArg (fun x => x * c) p)) := by
  cases p
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]

variable [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- When the last variable of the hexagon is the central object's own degree,
its forward and inverse associators at `(h,g,g)` cancel in fusion coordinates. -/
theorem halfBraidingScalar_mul (g h : G) (b : HalfBraiding (F.obj g)) (hc : Commute g h) :
    F.halfBraidingScalar b hc * F.halfBraidingScalar b (Commute.refl g) =
      F.associatorScalar g h g * F.halfBraidingScalar b (hc.mul_right (Commute.refl g)) := by
  let hProduct := hc.mul_right (Commute.refl g)
  let chart := F.fuseLeft g h g ≪≫
    eqToIso (congrArg F.obj (congrArg (fun x => x * g) hc.eq))
  let transport := eqToHom (congrArg F.obj hProduct.eq)
  have hCross :
      ((b.β (F.obj h)).hom ▷ F.obj g) ≫ (F.fuseLeft h g g).hom =
        (F.halfBraidingScalar b hc : ℂ) • chart.hom := by
    simp only [chart, fuseLeft, Iso.trans_hom, whiskerRightIso_hom, eqToIso.hom]
    rw [← Category.assoc, ← comp_whiskerRight, F.halfBraiding_comp_fusion b hc]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, comp_whiskerRight,
      Category.assoc, F.transport_whiskerRight_fusion hc.eq g]
  have hAssoc :
      (α_ (F.obj g) (F.obj h) (F.obj g)).hom ≫ (F.fuseRight g h g).hom ≫ transport =
        (F.associatorScalar g h g : ℂ) • chart.hom := by
    simpa only [chart, transport, Iso.trans_hom, eqToIso.hom, Category.assoc,
      Linear.smul_comp, eqToHom_trans] using
      congrArg (fun f : (F.obj g ⊗ F.obj h) ⊗ F.obj g ⟶ F.obj ((g * h) * g) =>
        f ≫ eqToHom (congrArg F.obj (congrArg (fun x => x * g) hc.eq)))
        (F.associator_comp_fuseRight g h g)
  have hHexagon :
      (α_ (F.obj g) (F.obj h) (F.obj g)).hom ≫ (b.β (F.obj h ⊗ F.obj g)).hom ≫
          (F.fuseLeft h g g).hom =
        ((F.halfBraidingScalar b (Commute.refl g) : ℂ) * (F.halfBraidingScalar b hc : ℂ)) •
          chart.hom := by
    rw [b.monoidal (F.obj h) (F.obj g)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, F.self_halfBraiding_hom g b,
      MonoidalLinear.whiskerLeft_smul, whiskerLeft_id, Linear.comp_smul, Linear.smul_comp,
      Category.id_comp, hCross, smul_smul]
  have hNaturality :
      (α_ (F.obj g) (F.obj h) (F.obj g)).hom ≫ (b.β (F.obj h ⊗ F.obj g)).hom ≫
          (F.fuseLeft h g g).hom =
        ((F.halfBraidingScalar b hProduct : ℂ) * (F.associatorScalar g h g : ℂ)) •
          chart.hom := by
    simp only [fuseLeft, Iso.trans_hom, whiskerRightIso_hom]
    rw [← b.naturality_assoc (F.μ h g).hom, F.halfBraiding_comp_fusion b hProduct]
    simpa only [fuseRight, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc,
      Linear.comp_smul, smul_smul, transport] using
      congrArg (fun f => (F.halfBraidingScalar b hProduct : ℂ) • f) hAssoc
  have hScalars := F.smul_hom_injective ((h * g) * g) chart (hHexagon.symm.trans hNaturality)
  apply Units.ext
  simpa only [Units.val_mul, mul_comm] using hScalars

/-- The self-half-braiding's order power is the cyclic product of the fusion-coordinate associator. -/
theorem pow_orderOf_eq_cyclicProduct (g : G) (b : HalfBraiding (F.obj g)) :
    F.halfBraidingScalar b (Commute.refl g) ^ orderOf g = cyclicProduct F.associatorScalar g := by
  let θ (i : ℕ) := F.halfBraidingScalar b (Commute.self_pow g i)
  let s := F.halfBraidingScalar b (Commute.refl g)
  have hstep (i : ℕ) : θ i * s = F.associatorScalar g (g ^ i) g * θ (i + 1) := by
    have hnext := F.halfBraidingScalar_congr b ((Commute.self_pow g i).mul_right (Commute.refl g))
      (Commute.self_pow g (i + 1)) (pow_succ g i).symm
    exact (F.halfBraidingScalar_mul g (g ^ i) b (Commute.self_pow g i)).trans
      (congrArg (fun z => F.associatorScalar g (g ^ i) g * z) hnext)
  have hpow (n : ℕ) : θ 0 * s ^ n =
      (∏ i ∈ Finset.range n, F.associatorScalar g (g ^ i) g) * θ n := by
    induction n with
    | zero => simp only [pow_zero, Finset.range_zero, Finset.prod_empty, mul_one, one_mul]
    | succ n ih => rw [pow_succ s n, ← mul_assoc, ih, mul_assoc, hstep n,
        Finset.prod_range_succ, mul_assoc]
  have hEnd : θ (orderOf g) = θ 0 :=
    F.halfBraidingScalar_congr b (Commute.self_pow g (orderOf g)) (Commute.self_pow g 0)
      ((pow_orderOf_eq_one g).trans (pow_zero g).symm)
  have h : θ 0 * s ^ orderOf g = cyclicProduct F.associatorScalar g * θ 0 := by
    simpa only [cyclicProduct, hEnd] using hpow (orderOf g)
  exact mul_left_cancel (h.trans (mul_comm (cyclicProduct F.associatorScalar g) (θ 0)))

/-- Nontrivial order power excludes the degree from every subgroup trivializing
the associator of these fusion coordinates by a two-cochain. -/
theorem not_mem_of_selfHalfBraiding_pow_ne_one (g : G) (b : HalfBraiding (F.obj g))
    (z : ℂˣ) (hSelf : (b.β (F.obj g)).hom = (z : ℂ) • 𝟙 (F.obj g ⊗ F.obj g))
    (hPower : z ^ orderOf g ≠ 1)
    (H : Subgroup G) (γ : H → H → ℂˣ)
    (hγ : ∀ a b c : H, F.associatorScalar a.val b.val c.val = twoCoboundary γ a b c) : g ∉ H := by
  have hz : F.halfBraidingScalar b (Commute.refl g) = z := by
    apply Units.ext
    apply F.smul_hom_injective (g * g) (F.μ g g)
    simpa only [Linear.smul_comp, Category.id_comp] using
      congrArg (fun f : F.obj g ⊗ F.obj g ⟶ F.obj g ⊗ F.obj g => f ≫ (F.μ g g).hom)
        ((F.self_halfBraiding_hom g b).symm.trans hSelf)
  intro hg
  apply hPower
  rw [← hz, F.pow_orderOf_eq_cyclicProduct g b]
  exact cyclicProduct_eq_one_of_mem F.associatorScalar H γ hγ hg

end FusionCoordinates

end D5.S3.FiniteGroups.Cyclic.FusionCenterMonodromy
