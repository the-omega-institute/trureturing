/- GID: D5/S3/FiniteGroups/Frobenius/NormalizerImageAction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/NormalizerImageAction
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual normalizer and center actions on a restricted representation image. -/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Central.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.SimpleRing.Field
import D5.S3.FiniteGroups.FrobeniusInnerActionObstruction
import D5.S3.FiniteGroups.GroupAlgebra.SkolemNoether
import D5.S3.FiniteGroups.Frobenius.FiniteIsotypicImageSimple

/-!
The actual module is U throughout. In particular, the last theorem installs the
restricted group-algebra action on U by compHom; its semisimplicity/isotypy inputs
refer to precisely that action. No scalar extension, characteristic restriction,
chosen action on the image, covariance hypothesis, or supplied inner unit occurs.

Reuse: Mathlib's conjNormal (including normality and inverse preservation),
domCongr, conjAlgEquiv, rangeRestrict, and centerCongr. Skolem proof attribution:
AxiomMath/Stacks contributors, Apache-2.0, pinned upstream revision
5ed82d14634e8d9576bb844c7bd4e3da66d450e7; see GroupAlgebra/SkolemNoether.lean for exact source hashes.
-/

noncomputable section

namespace NormalizerImageAction

universe uk uh uu

variable {k : Type uk} {H : Type uh} {U : Type uu}
  [Field k] [Group H] [AddCommGroup U] [Module k U]

variable (ρ : H →* (U ≃ₗ[k] U)) (N : Subgroup H) [N.Normal]

/-- Forget invertibility of the genuine representation operators. -/
def representation : Representation k H U :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ

/-- The actual restricted group-algebra action on the original U. -/
def q : MonoidAlgebra k N →ₐ[k] Module.End k U :=
  Representation.asAlgebraHom ((representation ρ).comp N.subtype)

abbrev Image := (q ρ N).range

/-- Mathlib calls the genuine range factorization `rangeRestrict`. -/
abbrev quotient : MonoidAlgebra k N →ₐ[k] Image ρ N := (q ρ N).rangeRestrict

theorem q_of (n : N) :
    q ρ N (MonoidAlgebra.of k N n) = (ρ (n : H)).toLinearMap := by
  change Representation.asAlgebraHom ((representation ρ).comp N.subtype) _ = _
  exact Representation.asAlgebraHom_of ((representation ρ).comp N.subtype) n

/-- Conjugation is defined first on actual endomorphisms of U. -/
def ambient (h : H) : Module.End k U ≃ₐ[k] Module.End k U :=
  (ρ h).conjAlgEquiv k

theorem ambient_apply (h : H) (a : Module.End k U) :
    ambient ρ h a = representation ρ h * a * representation ρ h⁻¹ := by
  change (ρ h).conjAlgEquiv k a =
    (ρ h).toLinearMap * a * (ρ h⁻¹).toLinearMap
  rw [LinearEquiv.conjAlgEquiv_apply]
  change (ρ h).toLinearMap ∘ₗ a ∘ₗ (ρ h).symm.toLinearMap = _
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  have hinv : ρ h⁻¹ = (ρ h).symm := by
    rw [map_inv]
    rfl
  rw [hinv]
  simp only [mul_assoc]

private theorem ambient_inv_apply (h : H) (a : Module.End k U) :
    ambient ρ h⁻¹ (ambient ρ h a) = a := by
  change (ρ h⁻¹).conjAlgEquiv k ((ρ h).conjAlgEquiv k a) = a
  rw [map_inv]
  exact ((ρ h).conjAlgEquiv k).symm_apply_apply a

private theorem ambient_one (a : Module.End k U) : ambient ρ 1 a = a := by
  simp only [ambient_apply, map_one, one_mul, mul_one, inv_one]

private theorem ambient_mul (h g : H) (a : Module.End k U) :
    ambient ρ (h * g) a = ambient ρ h (ambient ρ g a) := by
  change (ρ (h * g)).conjAlgEquiv k a =
    (ρ h).conjAlgEquiv k ((ρ g).conjAlgEquiv k a)
  have hmul : ρ (h * g) = ρ h * ρ g := map_mul ρ h g
  rw [hmul]
  ext x
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]
  rfl

/-- Normality is supplied by conjNormal; covariance is proved on the entire
group algebra by induction, rather than postulated on the representation. -/
theorem ambient_q (h : H) (x : MonoidAlgebra k N) :
    ambient ρ h (q ρ N x) =
      q ρ N (MonoidAlgebra.domCongr k k (MulAut.conjNormal h) x) := by
  induction x using MonoidAlgebra.induction_on with
  | of n =>
      have hd : MonoidAlgebra.domCongr k k (MulAut.conjNormal h)
          (MonoidAlgebra.of k N n) =
          MonoidAlgebra.of k N (MulAut.conjNormal h n) := by
        simp only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single]
      rw [hd, q_of, q_of, ambient_apply]
      change (ρ h).toLinearMap * (ρ (n : H)).toLinearMap * (ρ h⁻¹).toLinearMap =
        (ρ ((MulAut.conjNormal h n : N) : H)).toLinearMap
      ext x
      change ρ h (ρ (n : H) (ρ h⁻¹ x)) = ρ ((MulAut.conjNormal h n : N) : H) x
      simp only [MulAut.conjNormal_apply, map_mul, map_inv]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

theorem ambient_mem_image (h : H) {a : Module.End k U}
    (ha : a ∈ (q ρ N).range) : ambient ρ h a ∈ (q ρ N).range := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨MonoidAlgebra.domCongr k k (MulAut.conjNormal h) x, (ambient_q ρ N h x).symm⟩

/-- The reverse implication uses preservation for h⁻¹, with no extra hypothesis. -/
theorem ambient_mem_image_iff (h : H) (a : Module.End k U) :
    ambient ρ h a ∈ (q ρ N).range ↔ a ∈ (q ρ N).range := by
  constructor
  · intro ha
    simpa only [ambient_inv_apply] using ambient_mem_image ρ N h⁻¹ ha
  · exact ambient_mem_image ρ N h

/-- Restriction of genuine operator conjugation, with its genuine inverse. -/
def imageAut (h : H) : Image ρ N ≃ₐ[k] Image ρ N where
  toFun a := ⟨ambient ρ h a.1, ambient_mem_image ρ N h a.2⟩
  invFun a := ⟨ambient ρ h⁻¹ a.1, ambient_mem_image ρ N h⁻¹ a.2⟩
  left_inv a := Subtype.ext (ambient_inv_apply ρ h a.1)
  right_inv a := Subtype.ext (by
    simpa only [inv_inv] using ambient_inv_apply ρ h⁻¹ a.1)
  map_mul' a b := Subtype.ext ((ambient ρ h).map_mul a.1 b.1)
  map_add' a b := Subtype.ext ((ambient ρ h).map_add a.1 b.1)
  commutes' c := Subtype.ext ((ambient ρ h).commutes c)

/-- The constructed algebra action, not a chosen action parameter. -/
def alpha : H →* (Image ρ N ≃ₐ[k] Image ρ N) where
  toFun := imageAut ρ N
  map_one' := by
    apply AlgEquiv.ext
    intro a
    exact Subtype.ext (ambient_one ρ a.1)
  map_mul' h g := by
    apply AlgEquiv.ext
    intro a
    exact Subtype.ext (ambient_mul ρ h g a.1)

theorem alpha_coe (h : H) (a : Image ρ N) :
    (alpha ρ N h a : Module.End k U) = ambient ρ h a.1 := rfl

/-- Exact action on the genuine image of [n]. -/
theorem alpha_of (h : H) (n : N) :
    alpha ρ N h (quotient ρ N (MonoidAlgebra.of k N n)) =
      quotient ρ N (MonoidAlgebra.of k N (MulAut.conjNormal h n)) := by
  apply Subtype.ext
  change ambient ρ h (q ρ N (MonoidAlgebra.of k N n)) = _
  simpa [quotient] using ambient_q ρ N h (MonoidAlgebra.of k N n)

abbrev Center := Subalgebra.center k (Image ρ N)

instance centerImageAlgebra : Algebra (Center ρ N) (Image ρ N) :=
  (Center ρ N).val.toRingHom.toAlgebra' (fun c x =>
    (Subalgebra.mem_center_iff.mp c.2 x).symm)

/-- Reuse centerCongr; only its scalar compatibility needs to be supplied. -/
def centerAut (h : H) : Center ρ N ≃ₐ[k] Center ρ N where
  __ := Subring.centerCongr (alpha ρ N h).toRingEquiv
  commutes' c := Subtype.ext ((alpha ρ N h).commutes c)

def centerAction : H →* (Center ρ N ≃ₐ[k] Center ρ N) where
  toFun := centerAut ρ N
  map_one' := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    change alpha ρ N 1 z.1 = z.1
    apply Subtype.ext
    change ambient ρ 1 (z.1 : Module.End k U) = (z.1 : Module.End k U)
    exact ambient_one ρ z.1
  map_mul' h g := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    change alpha ρ N (h * g) z.1 = alpha ρ N h (alpha ρ N g z.1)
    apply Subtype.ext
    change ambient ρ (h * g) (z.1 : Module.End k U) =
      ambient ρ h (ambient ρ g (z.1 : Module.End k U))
    exact ambient_mul ρ h g z.1

theorem centerAction_coe (h : H) (z : Center ρ N) :
    (centerAction ρ N h z : Image ρ N) = alpha ρ N h z.1 := rfl

/-- The implementing unit for n is explicitly q([n]), with inverse q([n⁻¹]). -/
def subgroupUnit (n : N) : (Image ρ N)ˣ where
  val := quotient ρ N (MonoidAlgebra.of k N n)
  inv := quotient ρ N (MonoidAlgebra.of k N n⁻¹)
  val_inv := by rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  inv_val := by rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]

theorem alpha_subgroup_inner (n : N) (a : Image ρ N) :
    alpha ρ N (n : H) a =
      (subgroupUnit ρ N n : Image ρ N) * a * (↑((subgroupUnit ρ N n)⁻¹) : Image ρ N) := by
  apply Subtype.ext
  change ambient ρ (n : H) a.1 =
    q ρ N (MonoidAlgebra.of k N n) * a.1 * q ρ N (MonoidAlgebra.of k N n⁻¹)
  rw [ambient_apply, q_of, q_of]
  rfl

/-- N fixes the actual center directly because its action is the preceding
inner action. No simplicity, semisimplicity, or faithfulness is used here. -/
theorem centerAction_subgroup (n : N) : centerAction ρ N (n : H) = 1 := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change alpha ρ N (n : H) z.1 = z.1
  rw [alpha_subgroup_inner]
  rw [Subring.mem_center_iff.mp z.2 (subgroupUnit ρ N n : Image ρ N), mul_assoc]
  simp

/-- The actual image is finite over k whenever the original module is. -/
theorem finite_image [Module.Finite k U] : Module.Finite k (Image ρ N) :=
  Module.Finite.of_injective (q ρ N).range.val.toLinearMap Subtype.val_injective

/-- The field structure is obtained from simplicity of the actual image. -/
def centerField [IsSimpleRing (Image ρ N)] : Field (Center ρ N) :=
  (IsSimpleRing.isField_center (Image ρ N)).toField

private def centerTower : IsScalarTower k (Center ρ N) (Image ρ N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem image_central : Algebra.IsCentral (Center ρ N) (Image ρ N) where
  out a ha := Algebra.mem_bot.mpr ⟨⟨a, ha⟩, rfl⟩

/-- The attributed Skolem-Noether theorem supplies the unit. The
canonical arbitrary-field obstruction then forces the restricted action to be
trivial, contradicting hnt. IsSimpleRing is discharged from original-module
semisimplicity/isotypy in the final theorem below, not assumed there. -/
private theorem mem_of_center_fixed [Finite N] [Module.Finite k U]
    [IsSimpleRing (Image ρ N)]
    (hfix : ∀ h : H, h ∉ N → ∀ n : N, MulAut.conjNormal h n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial ((representation ρ).comp N.subtype))
    (h : H) (hz : centerAction ρ N h = 1) : h ∈ N := by
  classical
  by_contra hh
  letI : Module.Finite k (Image ρ N) := finite_image ρ N
  letI : Field (Center ρ N) := centerField ρ N
  letI : IsScalarTower k (Center ρ N) (Image ρ N) := centerTower ρ N
  letI : Module.Finite (Center ρ N) (Image ρ N) :=
    Module.Finite.of_restrictScalars_finite k (Center ρ N) (Image ρ N)
  letI : Algebra (Center ρ N) (Image ρ N) :=
    (Center ρ N).val.toRingHom.toAlgebra' (fun c x =>
      (Subalgebra.mem_center_iff.mp c.2 x).symm)
  letI : Algebra.IsCentral (Center ρ N) (Image ρ N) := image_central ρ N
  let centerLinear' : Image ρ N ≃ₐ[Center ρ N] Image ρ N := {
    __ := (alpha ρ N h).toRingEquiv
    commutes' z := congrArg Subtype.val (AlgEquiv.congr_fun hz z)
  }
  have hsk := @D5.S3.RingTheory.SkolemNoether.skolemNoether'
    (Center ρ N) (Image ρ N)
    (inferInstance : Field (Center ρ N))
    (inferInstance : Ring (Image ρ N))
    (inferInstance : Algebra (Center ρ N) (Image ρ N))
    (inferInstance : Module.Finite (Center ρ N) (Image ρ N))
    (inferInstance : Algebra.IsCentral (Center ρ N) (Image ρ N))
    (inferInstance : IsSimpleRing (Image ρ N)) centerLinear'
  obtain ⟨u, hu⟩ := hsk
  have hcov (n : N) :
      quotient ρ N (MonoidAlgebra.of k N (MulAut.conjNormal h n)) =
        (u : Image ρ N) * quotient ρ N (MonoidAlgebra.of k N n) *
          (↑(u⁻¹) : Image ρ N) := by
    calc
      _ = alpha ρ N h (quotient ρ N (MonoidAlgebra.of k N n)) :=
        (alpha_of ρ N h n).symm
      _ = centerLinear' (quotient ρ N (MonoidAlgebra.of k N n)) := rfl
      _ = _ := hu _
  have hout := D5.S3.FiniteGroups.FrobeniusInnerActionObstruction.inner_action_obstruction
    (quotient ρ N) (AlgHom.rangeRestrict_surjective (q ρ N))
    (MulAut.conjNormal h) (hfix h hh) u hcov
  apply hnt
  constructor
  intro n
  have hn := congrArg (fun a : Image ρ N => (a : Module.End k U)) (hout.1 n)
  change q ρ N (MonoidAlgebra.of k N n) = (1 : Module.End k U) at hn
  rw [q_of] at hn
  exact hn

/-- Identifies the entire center kernel in the nontrivial branch. -/
private theorem centerAction_ker_eq [Finite N] [Module.Finite k U]
    [IsSimpleRing (Image ρ N)]
    (hfix : ∀ h : H, h ∉ N → ∀ n : N, MulAut.conjNormal h n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial ((representation ρ).comp N.subtype)) :
    (centerAction ρ N).ker = N := by
  ext h
  constructor
  · exact mem_of_center_fixed ρ N hfix hnt h
  · intro hh
    exact centerAction_subgroup ρ N ⟨h, hh⟩

/-- Restriction of the genuine algebra action to the original carrier U. -/
def actualModule : Module (MonoidAlgebra k N) U := Module.compHom U (q ρ N).toRingHom

private theorem actualTower :
    letI := actualModule ρ N
    IsScalarTower k (MonoidAlgebra k N) U := by
  letI := actualModule ρ N
  apply IsScalarTower.of_algebraMap_smul
  intro c x
  change q ρ N (algebraMap k (MonoidAlgebra k N) c) x = c • x
  exact congrArg (fun f : Module.End k U => f x) ((q ρ N).commutes c)

/-- The complement's center kernel is trivial for the original
finite semisimple isotypic module. Simplicity of A follows from the actual image theorem; finite dimensionality of A over k and over Z(A) is derived above.
The fixed-point-free condition is the actual Frobenius-kernel conjugation
condition inside H. The complement is an actual subgroup complement inside H.
No assumption supplies a center action, covariance, inner implementer, or
faithfulness, and no condition of algebraic closedness/separability is used. -/
theorem complement_center_kernel_eq_bot [Finite N] [Module.Finite k U] [Nontrivial U]
    (hsemi : letI := actualModule ρ N; IsSemisimpleModule (MonoidAlgebra k N) U)
    (hiso : letI := actualModule ρ N; IsIsotypic (MonoidAlgebra k N) U)
    (hfix : ∀ h : H, h ∉ N → ∀ n : N, MulAut.conjNormal h n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial ((representation ρ).comp N.subtype))
    (J : Subgroup H) (hJ : N.IsComplement' J) :
    ((centerAction ρ N).comp J.subtype).ker = ⊥ := by
  letI := actualModule ρ N
  letI : IsScalarTower k (MonoidAlgebra k N) U := actualTower ρ N
  letI : IsSemisimpleModule (MonoidAlgebra k N) U := hsemi
  have hlsmul : Algebra.lsmul k k U (A := MonoidAlgebra k N) = q ρ N := by
    apply AlgHom.ext
    intro r
    apply LinearMap.ext
    intro x
    rfl
  letI : IsSimpleRing (Image ρ N) := by
    change IsSimpleRing (q ρ N).range
    rw [← hlsmul]
    exact FiniteIsotypicImage.isSimpleRing_actionRange hiso
  have hker := centerAction_ker_eq ρ N hfix hnt
  ext j
  rw [Subgroup.mem_bot]
  constructor
  · intro hj
    have hjN : (j : H) ∈ N := by
      rw [← hker]
      exact hj
    exact Subtype.ext (Subgroup.disjoint_def.mp hJ.disjoint hjN j.2)
  · rintro rfl
    exact ((centerAction ρ N).comp J.subtype).map_one

end NormalizerImageAction
