/- GID: D5/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Basic, mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary.cyclic_projectivity_detection_claim; result=D5/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary.cyclic_projectivity_detection_fails; claim=D5/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary.cyclic_projectivity_detection_claim
   digest: An explicit six-dimensional F3 representation refutes projectivity detection by all actual cyclic subgroups of C3 x C3. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
The closed cyclic_projectivity_detection_claim asserts cyclic-subgroup
projectivity detection for every representation on the fixed F, E and V.
The sole public theorem refutes this claim using the explicit rho below.

The polynomial action below is exactly S^a T^b, where S = 1 + N,
T = 1 + Jbar N, N(v0,v1,v2) = (v1,v2,0), and J(x,y) = (-y,x).
All subgroup modules use the actual inclusion into E. The imported p-group
norm criterion is used in both directions. No literature priority is claimed
for the explicit matrices. Elementary-abelian detection is compatible with
this example because its test family includes E itself.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.RankTwoCyclicDetectionBoundary

open scoped BigOperators MonoidAlgebra

/-- The coefficient field with three elements. -/
abbrev F := ZMod 3

/-- The actual elementary abelian group C3 × C3, in multiplicative notation. -/
abbrev E := Multiplicative (F × F)

/-- The two-dimensional block on which J(x,y) = (-y,x). -/
abbrev W := F × F

/-- Three ordered two-dimensional blocks, with coordinates v0, v1, v2. -/
abbrev V := W × (W × W)

private local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- mix r s is r I + s J. All these coordinate helpers are consumed below.
private def mix (r s : F) (w : W) : W :=
  (r * w.1 - s * w.2, s * w.1 + r * w.2)

private theorem mix_comp (r s a b : F) (w : W) :
    mix r s (mix a b w) = mix (r * a - s * b) (r * b + s * a) w := by
  apply Prod.ext <;> dsimp [mix] <;> ring

private theorem mix_id (w : W) : mix 1 0 w = w := by
  apply Prod.ext <;> simp [mix]

-- The inverse of 2 is 2 in F3.
private def c (a : F) : F := 2 * (a * a - a)

-- L = a I + b J; Q = (c(a) - c(b)) I + ab J.
private def act (a b : F) (v : V) : V :=
  (v.1 + mix a b v.2.1 + mix (c a - c b) (a * b) v.2.2,
    (v.2.1 + mix a b v.2.2, v.2.2))

private def actionMap (a b : F) : V →ₗ[F] V where
  toFun := act a b
  map_add' v w := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
      dsimp [act, mix] <;> ring
  map_smul' r v := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
      dsimp [act, mix] <;> ring

/-- The explicit polynomial representation of the actual group E on F3^6.
For g = (a,b), this is I + Lbar N + Qbar N² with the displayed L and Q. -/
def rho : Representation F E V where
  toFun g := actionMap g.toAdd.1 g.toAdd.2
  map_one' := by
    apply LinearMap.ext
    intro v
    change act 0 0 v = v
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
      simp [act, mix, c]
  map_mul' g h := by
    have : CharP F 3 := inferInstance
    apply LinearMap.ext
    intro v
    change act (g.toAdd.1 + h.toAdd.1) (g.toAdd.2 + h.toAdd.2) v =
      act g.toAdd.1 g.toAdd.2 (act h.toAdd.1 h.toAdd.2 v)
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
      dsimp [act, mix, c] <;> ring_nf <;> reduce_mod_char!

-- Nine actual group elements, each killed by the third power. This is a
-- kernel decision proof over a finite type, not native_decide.
private theorem exponent_three (g : E) : g ^ 3 = 1 := by
  have h : ∀ g : E, g ^ 3 = 1 := by decide
  exact h g

private theorem elementary_three : IsPGroup 3 E := by
  intro g
  exact ⟨1, by simpa using exponent_three g⟩

-- Both identities reduce to the nine pairs of field elements. The
-- nonzero-direction hypothesis excludes exactly the zero pair.
private theorem direction_coefficients (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    (a * a + b * b) * (a * a + b * b) = 1 ∧
      (a * a - b * b) * (a * a - b * b) + (a * b) * (a * b) = 1 := by
  have h : ∀ a b : F, (a ≠ 0 ∨ b ≠ 0) →
      (a * a + b * b) * (a * a + b * b) = 1 ∧
        (a * a - b * b) * (a * a - b * b) + (a * b) * (a * b) = 1 := by
    decide
  exact h a b hab

-- Delta(a I - b J) is a uniform left inverse of L in every nonzero direction.
private theorem direction_inverse (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) (w : W) :
    mix ((a * a + b * b) * a) (-((a * a + b * b) * b)) (mix a b w) = w := by
  rw [mix_comp]
  have hr : ((a * a + b * b) * a) * a - (-((a * a + b * b) * b)) * b = 1 := by
    calc
      _ = (a * a + b * b) * (a * a + b * b) := by ring
      _ = 1 := (direction_coefficients a b hab).1
  have hs : ((a * a + b * b) * a) * b + (-((a * a + b * b) * b)) * a = 0 := by
    ring
  rw [hr, hs]
  exact mix_id w

-- L² = (a² - b²) I - ab J, and its inverse is (a² - b²) I + ab J.
private theorem square_inverse (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) (w : W) :
    mix (a * a - b * b) (-(a * b)) (mix (a * a - b * b) (a * b) w) = w := by
  rw [mix_comp]
  have hr : (a * a - b * b) * (a * a - b * b) - (-(a * b)) * (a * b) = 1 := by
    calc
      _ = (a * a - b * b) * (a * a - b * b) + (a * b) * (a * b) := by ring
      _ = 1 := (direction_coefficients a b hab).2
  have hs : (a * a - b * b) * (a * b) + (-(a * b)) * (a * a - b * b) = 0 := by
    ring
  rw [hr, hs]
  exact mix_id w

private theorem fixed_tail_zero (a b : F) (hab : a ≠ 0 ∨ b ≠ 0)
    (v : V) (hv : act a b v = v) : v.2.1 = 0 ∧ v.2.2 = 0 := by
  have hL2 : mix a b v.2.2 = 0 := by
    have he := congrArg (fun z : V => z.2.1) hv
    change v.2.1 + mix a b v.2.2 = v.2.1 at he
    exact add_left_cancel (he.trans (add_zero _).symm)
  have hv2 : v.2.2 = 0 := by
    calc
      v.2.2 = mix ((a * a + b * b) * a) (-((a * a + b * b) * b))
          (mix a b v.2.2) := (direction_inverse a b hab v.2.2).symm
      _ = 0 := by
        rw [hL2]
        apply Prod.ext <;> simp [mix]
  have hL1 : mix a b v.2.1 = 0 := by
    have he := congrArg (fun z : V => z.1) hv
    change v.1 + mix a b v.2.1 + mix (c a - c b) (a * b) v.2.2 = v.1 at he
    have he' : v.1 + mix a b v.2.1 = v.1 := by
      rw [hv2] at he
      have hz : mix (c a - c b) (a * b) (0 : W) = 0 := by
        apply Prod.ext <;> simp [mix]
      simpa only [hz, add_zero] using he
    exact add_left_cancel (he'.trans (add_zero _).symm)
  have hv1 : v.2.1 = 0 := by
    calc
      v.2.1 = mix ((a * a + b * b) * a) (-((a * a + b * b) * b))
          (mix a b v.2.1) := (direction_inverse a b hab v.2.1).symm
      _ = 0 := by
        rw [hL1]
        apply Prod.ext <;> simp [mix]
  exact ⟨hv1, hv2⟩

-- This is the sum over the actual subtype H, reindexed by a bijection
-- i ↦ h^i from Fin 3. No separate abstract cyclic action is substituted.
private theorem cyclic_norm (H : Subgroup E) [Fintype H] (h : H)
    (hgen : ∀ x : H, x ∈ Subgroup.zpowers h) (hh : h ≠ 1) (v : V) :
    Representation.norm (rho.comp H.subtype : Representation F H V) v =
      (mix (h.val.toAdd.1 * h.val.toAdd.1 - h.val.toAdd.2 * h.val.toAdd.2)
        (-(h.val.toAdd.1 * h.val.toAdd.2)) v.2.2, (0, 0)) := by
  classical
  have : CharP F 3 := inferInstance
  have hc : h ^ 3 = 1 := by
    apply Subtype.ext
    exact exponent_three h.val
  have ho : orderOf h = 3 := orderOf_eq_prime hc hh
  have hinj : Function.Injective (fun i : Fin 3 => h ^ i.val) := by
    intro i j hij
    apply Fin.ext
    exact (pow_injOn_Iio_orderOf (x := h)) (by simp [ho])
      (by simp [ho]) hij
  have hsurj : Function.Surjective (fun i : Fin 3 => h ^ i.val) := by
    intro x
    have hx := (mem_zpowers_iff_mem_range_orderOf (x := h) (y := x)).mp (hgen x)
    rw [ho] at hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, hix⟩
  have hsum := Fintype.sum_bijective (fun i : Fin 3 => h ^ i.val) ⟨hinj, hsurj⟩
    (fun i : Fin 3 => rho ((h ^ i.val : H) : E) v)
    (fun x : H => rho (x : E) v) (fun _ => rfl)
  calc
    Representation.norm (rho.comp H.subtype : Representation F H V) v = ∑ x : H, rho (x : E) v := by
      simp only [Representation.norm, LinearMap.sum_apply, MonoidHom.comp_apply,
        Subgroup.subtype_apply]
    _ = v + rho (h : E) v + rho ((h : E) ^ 2) v := by
      simpa [Fin.sum_univ_three] using hsum.symm
    _ = (mix (h.val.toAdd.1 * h.val.toAdd.1 - h.val.toAdd.2 * h.val.toAdd.2)
        (-(h.val.toAdd.1 * h.val.toAdd.2)) v.2.2, (0, 0)) := by
      rw [pow_two]
      change v + act h.val.toAdd.1 h.val.toAdd.2 v +
          act (h.val.toAdd.1 + h.val.toAdd.1) (h.val.toAdd.2 + h.val.toAdd.2) v = _
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
        dsimp [act, mix, c] <;> ring_nf <;> reduce_mod_char! <;> ring_nf <;> reduce_mod_char!

private theorem cyclic_projective (H : Subgroup E) [IsCyclic H] :
    Module.Projective F[H]
      (Representation.asModule (rho.comp H.subtype : Representation F H V)) := by
  classical
  apply (PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
    3 1 (by decide) (by decide) (elementary_three.to_subgroup H)
    (rho.comp H.subtype)).mpr
  refine ⟨inferInstance, ?_⟩
  intro w
  obtain ⟨h, hgen⟩ := IsCyclic.exists_generator (α := H)
  by_cases hh : h = 1
  · have hall (x : H) : x = 1 := by
      obtain ⟨i, hi⟩ := hgen x
      simpa [hh] using hi.symm
    have huniv : (Finset.univ : Finset H) = {1} := by
      apply Finset.ext
      intro x
      simp [hall x]
    refine ⟨(w : V), ?_⟩
    simp [Representation.norm, huniv]
  · have hab : h.val.toAdd.1 ≠ 0 ∨ h.val.toAdd.2 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hh
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      exact Prod.ext hn.1 hn.2
    have hw : act h.val.toAdd.1 h.val.toAdd.2 (w : V) = (w : V) := w.property h
    obtain ⟨hw1, hw2⟩ := fixed_tail_zero h.val.toAdd.1 h.val.toAdd.2 hab (w : V) hw
    refine ⟨(0, (0, mix
      (h.val.toAdd.1 * h.val.toAdd.1 - h.val.toAdd.2 * h.val.toAdd.2)
      (h.val.toAdd.1 * h.val.toAdd.2) (w : V).1)), ?_⟩
    rw [cyclic_norm H h hgen hh]
    dsimp only
    rw [square_inverse h.val.toAdd.1 h.val.toAdd.2 hab]
    apply Prod.ext
    · rfl
    · exact (Prod.ext hw1 hw2).symm

private theorem field_sum (f : F → V) : (∑ a : F, f a) = f 0 + f 1 + f 2 := by
  exact Fin.sum_univ_three f

private theorem ambient_norm_zero (v : V) : rho.norm v = 0 := by
  classical
  have : CharP F 3 := inferInstance
  calc
    rho.norm v = ∑ g : E, rho g v := by
      simp only [Representation.norm, LinearMap.sum_apply]
    _ = ∑ z : F × F, rho (Multiplicative.ofAdd z) v :=
      Fintype.sum_equiv Multiplicative.toAdd _ _ (fun _ => rfl)
    _ = ∑ a : F, ∑ b : F, act a b v := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = 0 := by
      simp only [field_sum]
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
        dsimp [act, mix, c] <;> ring_nf <;> reduce_mod_char!

/-- The closed universal assertion that projectivity on every actual cyclic
subgroup detects ambient projectivity for representations on the fixed F, E and V. -/
def cyclic_projectivity_detection_claim : Prop :=
  ∀ tau : Representation F E V,
    (∀ H : Subgroup E, IsCyclic H →
      Module.Projective F[H]
        (Representation.asModule (tau.comp H.subtype : Representation F H V))) →
      Module.Projective F[E] tau.asModule

/-- The explicit six-dimensional action refutes cyclic-subgroup projectivity
detection: every actual cyclic restriction is projective, but rho is not. -/
theorem cyclic_projectivity_detection_fails : Not cyclic_projectivity_detection_claim := by
  intro hdetect
  have hproj : Module.Projective F[E] rho.asModule :=
    hdetect rho (by
      intro H hH
      let : IsCyclic H := hH
      exact cyclic_projective H)
  let w : rho.invariants :=
    ⟨((1, 0), (0, 0)), by
      intro g
      change act g.toAdd.1 g.toAdd.2 ((1, 0), (0, 0)) = ((1, 0), (0, 0))
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
        simp [act, mix]⟩
  obtain ⟨x, hx⟩ :=
    ((PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
      3 1 (by decide) (by decide) elementary_three rho).mp hproj).2 w
  have he : (0 : V) = (w : V) := (ambient_norm_zero x).symm.trans hx
  have h01 : (0 : F) = 1 := congrArg (fun z : V => z.1.1) he
  exact zero_ne_one h01

end D5.S3.FiniteGroups.GroupAlgebra.RankTwoCyclicDetectionBoundary
