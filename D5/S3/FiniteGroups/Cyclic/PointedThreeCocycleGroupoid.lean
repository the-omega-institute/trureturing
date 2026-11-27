/- GID: D5/S3/FiniteGroups/Cyclic/PointedThreeCocycleGroupoid
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/PointedThreeCocycleGroupoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.CategoryTheory.Monoidal.Center]
   utility: none
   digest: A normalized three-cocycle gives a pointed monoidal groupoid and the cyclic carry model realizes its generator half-braiding. -/

import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.Tactic.Abel
import D5.S3.FiniteGroups.Cyclic.PointedCenterMonodromy
import OmegaBuild.Commands

/-! The monoidal groupoid of degrees and scalar isomorphisms for a normalized
three-cocycle with trivial coefficient action. Applying its center formula to
lattice-VOA sectors requires a monoidal comparison on the invertible sectors
and identification of the self-half-braiding scalar with the ribbon twist. -/

compile_only_with_mathlib

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace D5.S3.FiniteGroups.Cyclic.PointedThreeCocycleGroupoid

open CyclicAssociatorObstruction (carryPhase cyclicPowerHom cyclicProduct
  cyclicProduct_eq_type_phase twoCoboundary)
open PointedCenterMonodromy (associatorScalar halfBraidingScalar)

universe u v

/-- The multiplicative three-cocycle equation in the direction of the associator hom. -/
structure NormalizedThreeCocycle (G : Type u) (A : Type v) [Group G] [CommGroup A] where
  toFun : G → G → G → A
  normalized (a b : G) : toFun 1 a b = 1 ∧ toFun a 1 b = 1 ∧ toFun a b 1 = 1
  cocycle (a b c d : G) :
    toFun a b c * (toFun a (b * c) d * toFun b c d) =
      toFun (a * b) c d * toFun a b (c * d)

/-- Mathlib's product groupoid. The second factor has one object and records scalars. -/
abbrev Model (G : Type u) (A : Type v) := Discrete G × SingleObj A

def ofDegree {G : Type u} (A : Type v) (g : G) : Model G A :=
  (Discrete.mk g, SingleObj.star A)

def degreeEquiv (G : Type u) (A : Type v) : Model G A ≃ G where
  toFun X := X.1.as
  invFun := ofDegree A
  left_inv X := Prod.ext (Discrete.mk_as X.1) (Quiver.SingleObj.ext (α := A))
  right_inv _ := rfl

/-- Project a morphism to its scalar label. -/
abbrev scalars (G : Type u) (A : Type v) [Monoid A] : Model G A ⥤ SingleObj A :=
  CategoryTheory.Prod.snd (Discrete G) (SingleObj A)

variable {G : Type u} {A : Type v} [Group G] [CommGroup A]

private theorem hom_ext {X Y : Model G A} {f k : X ⟶ Y} (h : f.2 = k.2) : f = k :=
  CategoryTheory.Prod.hom_ext Discrete.hom_eq h

/-- Isomorphisms exist between equal degrees, with any chosen scalar label. -/
def isoOfScalar {X Y : Model G A} (h : X.1.as = Y.1.as) (s : A) : X ≅ Y where
  hom := ⟨Discrete.Hom.mk h, s⟩
  inv := ⟨Discrete.Hom.mk h.symm, s⁻¹⟩
  hom_inv_id := by
    apply hom_ext
    exact inv_mul_cancel s
  inv_hom_id := by
    apply hom_ext
    exact mul_inv_cancel s

/-- Install this structure locally with `letI := monoidal ω` to select the cocycle. -/
def monoidal (ω : NormalizedThreeCocycle G A) : MonoidalCategory (Model G A) where
  tensorObj X Y := ofDegree A (X.1.as * Y.1.as)
  tensorUnit := ofDegree A (1 : G)
  whiskerLeft := by
    intro X Y₁ Y₂ f
    exact ⟨Discrete.Hom.mk (congrArg (fun y => X.1.as * y) (Discrete.eq_of_hom f.1)), f.2⟩
  whiskerRight := by
    intro X₁ X₂ f Y
    exact ⟨Discrete.Hom.mk (congrArg (fun x => x * Y.1.as) (Discrete.eq_of_hom f.1)), f.2⟩
  tensorHom := by
    intro X₁ Y₁ X₂ Y₂ f k
    exact ⟨Discrete.Hom.mk (congrArg₂ (· * ·)
      (Discrete.eq_of_hom f.1) (Discrete.eq_of_hom k.1)), (f.2 : A) * (k.2 : A)⟩
  associator X Y Z :=
    isoOfScalar (mul_assoc X.1.as Y.1.as Z.1.as) (ω.toFun X.1.as Y.1.as Z.1.as)
  leftUnitor X := isoOfScalar (one_mul X.1.as) 1
  rightUnitor X := isoOfScalar (mul_one X.1.as) 1
  tensorHom_def := by
    intro X₁ Y₁ X₂ Y₂ f k
    apply hom_ext
    exact mul_comm (f.2 : A) k.2
  id_tensorHom_id X Y := by
    apply hom_ext
    exact mul_one (1 : A)
  tensorHom_comp_tensorHom := by
    intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ k₁ k₂
    apply hom_ext
    exact mul_mul_mul_comm (k₁.2 : A) k₂.2 f₁.2 f₂.2
  whiskerLeft_id X Y := hom_ext rfl
  id_whiskerRight X Y := hom_ext rfl
  associator_naturality := by
    intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    apply hom_ext
    change ω.toFun Y₁.1.as Y₂.1.as Y₃.1.as * ((f₁.2 * f₂.2) * f₃.2) =
      (f₁.2 * (f₂.2 * f₃.2)) * ω.toFun X₁.1.as X₂.1.as X₃.1.as
    rw [← Discrete.eq_of_hom f₁.1, ← Discrete.eq_of_hom f₂.1,
      ← Discrete.eq_of_hom f₃.1, mul_assoc (f₁.2 : A) f₂.2 f₃.2]
    exact mul_comm _ _
  leftUnitor_naturality := by
    intro X Y f
    apply hom_ext
    exact (one_mul (f.2 : A)).trans (mul_one _).symm
  rightUnitor_naturality := by
    intro X Y f
    apply hom_ext
    exact (one_mul (f.2 : A)).trans (mul_one _).symm
  pentagon a b c d := by
    apply hom_ext
    change (ω.toFun b.1.as c.1.as d.1.as * ω.toFun a.1.as (b.1.as * c.1.as) d.1.as) *
      ω.toFun a.1.as b.1.as c.1.as =
        ω.toFun a.1.as b.1.as (c.1.as * d.1.as) * ω.toFun (a.1.as * b.1.as) c.1.as d.1.as
    simpa only [mul_comm, mul_left_comm, mul_assoc] using ω.cocycle a.1.as b.1.as c.1.as d.1.as
  triangle a b := by
    apply hom_ext
    change 1 * ω.toFun a.1.as 1 b.1.as = 1
    rw [one_mul, (ω.normalized a.1.as b.1.as).2.1]

theorem tensor_degree (ω : NormalizedThreeCocycle G A) (g h : G) :
    letI := monoidal ω
    ofDegree A (g * h) = ofDegree A g ⊗ ofDegree A h :=
  rfl

theorem scalars_tensorHom (ω : NormalizedThreeCocycle G A) {U V X Y : Model G A}
    (f : U ⟶ V) (k : X ⟶ Y) :
    letI := monoidal ω
    ((scalars G A).map (f ⊗ₘ k) : A) =
      ((scalars G A).map f : A) * ((scalars G A).map k : A) :=
  rfl

theorem scalars_whiskerLeft (ω : NormalizedThreeCocycle G A) (X : Model G A)
    {Y Z : Model G A} (f : Y ⟶ Z) :
    letI := monoidal ω
    (scalars G A).map (X ◁ f) = (scalars G A).map f :=
  rfl

theorem scalars_whiskerRight (ω : NormalizedThreeCocycle G A) {X Y : Model G A}
    (f : X ⟶ Y) (Z : Model G A) :
    letI := monoidal ω
    (scalars G A).map (f ▷ Z) = (scalars G A).map f :=
  rfl

/-- The two tensor inverse isomorphisms have label one. -/
def tensorInverseIsos (ω : NormalizedThreeCocycle G A) (g : G) :
    letI := monoidal ω
    ((ofDegree A g⁻¹ ⊗ ofDegree A g) ≅ 𝟙_ (Model G A)) ×
      ((ofDegree A g ⊗ ofDegree A g⁻¹) ≅ 𝟙_ (Model G A)) := by
  letI := monoidal ω
  exact ⟨isoOfScalar (inv_mul_cancel g) 1, isoOfScalar (mul_inv_cancel g) 1⟩

/-- Apply the checked center theorem to a half-braiding in the cocycle model. -/
theorem pow_orderOf_eq_cyclicProduct (ω : NormalizedThreeCocycle G A) (g : G)
    (b : letI := monoidal ω; HalfBraiding (ofDegree A g)) :
    letI := monoidal ω
    halfBraidingScalar (scalars G A) (ofDegree A) b g ^ orderOf g =
      cyclicProduct ω.toFun g := by
  letI := monoidal ω
  have hAssoc : associatorScalar (scalars G A) (ofDegree A) = ω.toFun := by
    funext a b c
    rfl
  simpa only [hAssoc] using
    PointedCenterMonodromy.pow_orderOf_eq_cyclicProduct (scalars G A) (ofDegree A)
      (tensor_degree ω) (scalars_whiskerLeft ω) (scalars_whiskerRight ω) g b

open CyclicCarryThreeCocycle (carry w w_normalized w_cocycle)

/-- The checked cyclic carry cocycle, with its phase in the given scalar group. -/
def carryCocycle {n : ℕ} [NeZero n] (ζ : A) (hζ : orderOf ζ = n) (t : ZMod n) :
    NormalizedThreeCocycle (Multiplicative (ZMod n)) A where
  toFun := carryPhase ζ hζ t
  normalized a b := by
    obtain ⟨h₁, h₂, h₃⟩ := w_normalized t a.toAdd b.toAdd
    simp only [carryPhase, Multiplicative.toAdd_one, h₁, h₂, h₃,
      Multiplicative.ofAdd_zero, map_one, and_self]
  cocycle a b c d := by
    have h :
        w t a.toAdd b.toAdd c.toAdd +
            (w t a.toAdd (b.toAdd + c.toAdd) d.toAdd + w t b.toAdd c.toAdd d.toAdd) =
          w t (a.toAdd + b.toAdd) c.toAdd d.toAdd + w t a.toAdd b.toAdd (c.toAdd + d.toAdd) := by
      apply sub_eq_zero.mp
      convert w_cocycle t a.toAdd b.toAdd c.toAdd d.toAdd using 1 <;> abel
    have hmul := congrArg
      (fun x : ZMod n => cyclicPowerHom ζ hζ (Multiplicative.ofAdd x)) h
    simp only [Multiplicative.ofAdd_add, map_mul] at hmul
    unfold carryPhase
    simpa only [Multiplicative.toAdd_mul, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- A root of the type phase gives a degree-one half-braiding. The component
at degree `h` has scalar label `root ^ h.toAdd.val`. -/
def carryGeneratorHalfBraiding {n : ℕ} [NeZero n]
    (ζ : A) (hζ : orderOf ζ = n) (t : ZMod n) (root : A) (hroot : root ^ n = ζ ^ t.val) :
    letI := monoidal (carryCocycle ζ hζ t)
    HalfBraiding (ofDegree A (Multiplicative.ofAdd (1 : ZMod n))) := by
  letI := monoidal (carryCocycle ζ hζ t)
  let g := Multiplicative.ofAdd (1 : ZMod n)
  refine
    { β := fun X => by
        refine isoOfScalar ?_ (root ^ X.1.as.toAdd.val)
        change g * X.1.as = X.1.as * g
        exact mul_comm g X.1.as
      monoidal := ?_
      naturality := ?_ }
  · intro X Y
    apply hom_ext
    let a := X.1.as.toAdd
    let b := Y.1.as.toAdd
    let phase := carryPhase ζ hζ t
    -- Composition in `SingleObj` multiplies the labels in reverse order.
    change root ^ (a + b).val =
      (phase X.1.as Y.1.as g)⁻¹ * (root ^ b.val * (phase X.1.as g Y.1.as *
        (root ^ a.val * (phase g X.1.as Y.1.as)⁻¹)))
    have hswap : phase X.1.as g Y.1.as = phase X.1.as Y.1.as g := by
      have hcarry : carry (1 : ZMod n) b = carry b 1 := by
        unfold carry
        rw [Nat.add_comm]
      exact congrArg (fun k : ℕ =>
        cyclicPowerHom ζ hζ (Multiplicative.ofAdd (t * a * (k : ZMod n)))) hcarry
    have hphase : phase g X.1.as Y.1.as = (ζ ^ t.val) ^ carry a b := by
      change cyclicPowerHom ζ hζ (Multiplicative.ofAdd (t * 1 * (carry a b : ZMod n))) =
        (cyclicPowerHom ζ hζ (Multiplicative.ofAdd t)) ^ carry a b
      rw [← map_pow (cyclicPowerHom ζ hζ) (Multiplicative.ofAdd t) (carry a b),
        ← Multiplicative.ofAdd_nsmul (carry a b) t, nsmul_eq_mul, mul_one, mul_comm t]
    have hsum : n * carry a b + (a + b).val = a.val + b.val := by
      rw [ZMod.val_add]
      exact Nat.div_add_mod _ _
    have hlabels : phase g X.1.as Y.1.as * root ^ (a + b).val = root ^ a.val * root ^ b.val := by
      rw [hphase, ← hroot, ← pow_mul root n (carry a b), ← pow_add, hsum, pow_add]
    rw [hswap]
    calc
      root ^ (a + b).val = (phase g X.1.as Y.1.as)⁻¹ * (root ^ a.val * root ^ b.val) := by
        rw [← hlabels, inv_mul_cancel_left]
      _ = (phase X.1.as Y.1.as g)⁻¹ * (phase X.1.as Y.1.as g *
          ((phase g X.1.as Y.1.as)⁻¹ * (root ^ a.val * root ^ b.val))) :=
        (inv_mul_cancel_left _ _).symm
      _ = _ := by ac_rfl
  · intro X Y f
    apply hom_ext
    change root ^ Y.1.as.toAdd.val * (f.2 : A) = f.2 * root ^ X.1.as.toAdd.val
    rw [← Discrete.eq_of_hom f.1]
    exact mul_comm _ _

/-- For `1 < n` the self-half-braiding of the degree-one object has label `root`. -/
theorem carryGeneratorHalfBraiding_self {n : ℕ} [NeZero n] (hn : 1 < n)
    (ζ : A) (hζ : orderOf ζ = n) (t : ZMod n) (root : A) (hroot : root ^ n = ζ ^ t.val) :
    letI := monoidal (carryCocycle ζ hζ t)
    halfBraidingScalar (scalars (Multiplicative (ZMod n)) A) (ofDegree A)
      (carryGeneratorHalfBraiding ζ hζ t root hroot) (Multiplicative.ofAdd (1 : ZMod n)) = root := by
  change root ^ (1 : ZMod n).val = root
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn, pow_one]

/-- In the carry model the generator's self-half-braiding has order power equal
to the type phase. Use `carryGeneratorHalfBraiding` for a concrete input. -/
theorem carry_generator_monodromy {n : ℕ} [NeZero n] (hn : 1 < n)
    (ζ : A) (hζ : orderOf ζ = n) (t : ZMod n)
    (b : letI := monoidal (carryCocycle ζ hζ t)
         HalfBraiding (ofDegree A (Multiplicative.ofAdd (1 : ZMod n)))) :
    letI := monoidal (carryCocycle ζ hζ t)
    halfBraidingScalar (scalars (Multiplicative (ZMod n)) A) (ofDegree A) b
      (Multiplicative.ofAdd (1 : ZMod n)) ^ n = ζ ^ t.val := by
  letI := monoidal (carryCocycle ζ hζ t)
  let g := Multiplicative.ofAdd (1 : ZMod n)
  have hg : orderOf g = n := ZMod.addOrderOf_one n
  have hpow := pow_orderOf_eq_cyclicProduct (carryCocycle ζ hζ t) g b
  rw [hg] at hpow
  refine hpow.trans ?_
  change cyclicProduct (carryPhase ζ hζ t) g = ζ ^ t.val
  refine cyclicProduct_eq_type_phase hn (carryPhase ζ hζ t) g hg ζ hζ t
    (fun _ _ => 1) ?_
  have hid (a : Multiplicative (ZMod n)) : cyclicPowerHom g hg a = a := by
    apply Multiplicative.ext
    change a.toAdd.val • (1 : ZMod n) = a.toAdd
    rw [Nat.smul_one_eq_cast, ZMod.natCast_zmod_val]
  intro a x c
  simp only [hid, twoCoboundary, div_one, mul_one]

end D5.S3.FiniteGroups.Cyclic.PointedThreeCocycleGroupoid
