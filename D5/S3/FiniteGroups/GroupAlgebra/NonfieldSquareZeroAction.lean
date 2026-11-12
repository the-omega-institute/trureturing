/- GID: D5/S3/FiniteGroups/GroupAlgebra/NonfieldSquareZeroAction
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/NonfieldSquareZeroAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.GaloisField, mathlib/module/Mathlib.RepresentationTheory.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/GroupAlgebra/NonfieldSquareZeroAction.field_translation_universality; result=D5/S3/FiniteGroups/GroupAlgebra/NonfieldSquareZeroAction.field_translation_universality_fails; claim=D5/S3/FiniteGroups/GroupAlgebra/NonfieldSquareZeroAction.field_translation_universality
   digest: A minimal square-zero action with projective actual cyclic restrictions admits no field-scalar shear model. -/

import D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldCyclicDimension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! A nonsingular additive binary code on a common Loewy layer gives an actual
square-zero action that cannot be conjugate to any field-scalar shear. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.NonfieldSquareZeroAction

open scoped BigOperators MonoidAlgebra

private local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The field with four elements, realized as a splitting field. -/
abbrev K := GaloisField 2 2
/-- The actual elementary abelian group of rank four. -/
abbrev E := Multiplicative (Fin 4 → ZMod 2)
/-- The shared two-dimensional Loewy layer. -/
abbrev U := K × K
/-- The four-dimensional representation space. -/
abbrev V := U × U

private theorem field_card : Nat.card K = 4 := by
  exact GaloisField.card 2 2 (by decide)

private theorem root_exists : ∃ w : K, w ≠ 0 ∧ w ≠ 1 ∧ w ^ 2 = w + 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by simpa [Nat.card_eq_fintype_card] using field_card
  have hex : ∃ w : K, w ≠ 0 ∧ w ≠ 1 := by
    by_contra hn
    push Not at hn
    have hs : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (hn x hx)
    have := Finset.card_le_card hs
    simp [hc] at this
  obtain ⟨w, hw0, hw1⟩ := hex
  refine ⟨w, hw0, hw1, ?_⟩
  have h3 : w ^ 3 = 1 := by simpa [hc] using FiniteField.pow_card_sub_one_eq_one w hw0
  have hz : (w - 1) * (w ^ 2 + w + 1) = 0 := by
    calc
      _ = w ^ 3 - 1 := by ring
      _ = 0 := by rw [h3]; ring
  have hr : w ^ 2 + w + 1 = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hw1)
  calc
    w ^ 2 = -(w + 1) := by linear_combination hr
    _ = w + 1 := CharTwo.neg_eq _

private noncomputable def root : K := Classical.choose root_exists
private theorem root_zero : root ≠ 0 := (Classical.choose_spec root_exists).1
private theorem root_one : root ≠ 1 := (Classical.choose_spec root_exists).2.1
private theorem root_square : root ^ 2 = root + 1 := (Classical.choose_spec root_exists).2.2

private noncomputable def coeff (t : Fin 4 → ZMod 2) (i : Fin 4) : K := algebraMap (ZMod 2) K (t i)

private noncomputable def code (t : Fin 4 → ZMod 2) : U →ₗ[K] U where
  toFun v :=
    ((coeff t 0 + coeff t 1 + root * coeff t 2) * v.1 +
      (root * coeff t 1 + root * coeff t 2 + (1 + root) * coeff t 3) * v.2,
     (root * coeff t 1 + (1 + root) * coeff t 2 + coeff t 3) * v.1 +
      (coeff t 0 + root * coeff t 1) * v.2)
  map_add' v z := by apply Prod.ext <;> dsimp <;> ring
  map_smul' a v := by apply Prod.ext <;> dsimp <;> ring

private noncomputable def determinant (t : Fin 4 → ZMod 2) : K :=
  (coeff t 0 + coeff t 1 + root * coeff t 2) * (coeff t 0 + root * coeff t 1) -
  (root * coeff t 1 + root * coeff t 2 + (1 + root) * coeff t 3) *
    (root * coeff t 1 + (1 + root) * coeff t 2 + coeff t 3)

private theorem determinant_ne_zero (t : Fin 4 → ZMod 2) (ht : t ≠ 0) :
    determinant t ≠ 0 := by
  have : CharP K 2 := inferInstance
  have hw : root + 1 ≠ 0 := by
    intro h
    have : root = 1 := by
      calc
        root = -1 := eq_neg_of_add_eq_zero_left h
        _ = 1 := CharTwo.neg_eq _
    exact root_one this
  have hb (a : ZMod 2) : a = 0 ∨ a = 1 := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact h a
  rcases hb (t 0) with h0 | h0 <;> rcases hb (t 1) with h1 | h1 <;>
    rcases hb (t 2) with h2 | h2 <;> rcases hb (t 3) with h3 | h3
  all_goals simp only [determinant, coeff, h0, h1, h2, h3]
  all_goals simp only [map_zero, map_one]
  all_goals norm_num
  all_goals try { exfalso; apply ht; ext i; fin_cases i <;> assumption }
  all_goals ring_nf
  all_goals reduce_mod_char!
  all_goals try simp only [root_square]
  all_goals ring_nf
  all_goals reduce_mod_char!
  all_goals simp [root_zero, hw, add_comm]


private noncomputable def codeMatrix (t : Fin 4 → ZMod 2) : Matrix (Fin 2) (Fin 2) K :=
  !![coeff t 0 + coeff t 1 + root * coeff t 2,
     root * coeff t 1 + root * coeff t 2 + (1 + root) * coeff t 3;
     root * coeff t 1 + (1 + root) * coeff t 2 + coeff t 3,
     coeff t 0 + root * coeff t 1]

private theorem code_bijective (t : Fin 4 → ZMod 2) (ht : t ≠ 0) :
    Function.Bijective (code t) := by
  classical
  have hd : (codeMatrix t).det ≠ 0 := by
    simpa [codeMatrix, Matrix.det_fin_two, determinant] using determinant_ne_zero t ht
  have hu : IsUnit (codeMatrix t) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  have hb : Function.Bijective (codeMatrix t).mulVec :=
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩
  let e := LinearEquiv.finTwoArrow K K
  have he : (code t : U → U) = e ∘ (codeMatrix t).mulVec ∘ e.symm := by
    funext v
    apply Prod.ext <;>
      simp [code, codeMatrix, e, LinearEquiv.finTwoArrow, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two]
  rw [he]
  exact e.bijective.comp (hb.comp e.symm.bijective)

private theorem code_add (s t : Fin 4 → ZMod 2) (v : U) :
    code (s + t) v = code s v + code t v := by
  apply Prod.ext <;> simp only [code, coeff, Pi.add_apply, map_add] <;> dsimp <;> ring

private noncomputable def actionMap (t : Fin 4 → ZMod 2) : V →ₗ[K] V where
  toFun v := (v.1 + code t v.2, v.2)
  map_add' v z := by
    apply Prod.ext
    · change v.1 + z.1 + code t (v.2 + z.2) = (v.1 + code t v.2) + (z.1 + code t z.2)
      rw [map_add]
      abel
    · rfl
  map_smul' a v := by
    apply Prod.ext
    · change a • v.1 + code t (a • v.2) = a • (v.1 + code t v.2)
      rw [map_smul, smul_add]
    · rfl

private noncomputable def rho : Representation K E V where
  toFun g := actionMap g.toAdd
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · simp [actionMap, code, coeff]
    · rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change (v.1 + code (g.toAdd + h.toAdd) v.2, v.2) =
      (v.1 + code h.toAdd v.2 + code g.toAdd v.2, v.2)
    rw [code_add]
    congr 1
    abel

private theorem square_zero (g h : E) : (rho g - 1) * (rho h - 1) = 0 := by
  apply LinearMap.ext
  intro v
  change actionMap g.toAdd (actionMap h.toAdd v - v) - (actionMap h.toAdd v - v) = 0
  apply Prod.ext <;> simp [actionMap]

private theorem exponent_two (g : E) : g ^ 2 = 1 := by
  apply Multiplicative.ext
  rw [toAdd_pow, toAdd_one]
  funext i
  exact ZModModule.char_nsmul_eq_zero 2 (g.toAdd i)

-- Reindex the norm on the actual subgroup, including its actual inclusion.
private theorem cyclic_norm (H : Subgroup E) [Fintype H] (h : H)
    (hgen : ∀ x : H, x ∈ Subgroup.zpowers h) (hh : h ≠ 1) (v : V) :
    Representation.norm (rho.comp H.subtype : Representation K H V) v =
      (code h.val.toAdd v.2, 0) := by
  classical
  have hc : h ^ 2 = 1 := by
    apply Subtype.ext
    exact exponent_two h.val
  have ho : orderOf h = 2 := orderOf_eq_prime hc hh
  have hinj : Function.Injective (fun i : Fin 2 => h ^ i.val) := by
    intro i j hij
    apply Fin.ext
    exact (pow_injOn_Iio_orderOf (x := h)) (by change i.val < orderOf h; rw [ho]; exact i.isLt)
      (by change j.val < orderOf h; rw [ho]; exact j.isLt) hij
  have hsurj : Function.Surjective (fun i : Fin 2 => h ^ i.val) := by
    intro x
    have hx := (mem_zpowers_iff_mem_range_orderOf (x := h) (y := x)).mp (hgen x)
    rw [ho] at hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, hix⟩
  have hsum := Fintype.sum_bijective (fun i : Fin 2 => h ^ i.val) ⟨hinj, hsurj⟩
    (fun i : Fin 2 => rho ((h ^ i.val : H) : E) v)
    (fun x : H => rho (x : E) v) (fun _ => rfl)
  calc
    Representation.norm (rho.comp H.subtype : Representation K H V) v =
        ∑ x : H, rho (x : E) v := by
      simp only [Representation.norm, LinearMap.sum_apply, MonoidHom.comp_apply,
        Subgroup.subtype_apply]
    _ = v + rho (h : E) v := by simpa [Fin.sum_univ_two] using hsum.symm
    _ = (code h.val.toAdd v.2, 0) := by
      change v + (v.1 + code h.val.toAdd v.2, v.2) = _
      apply Prod.ext
      · change v.1 + (v.1 + code h.val.toAdd v.2) = code h.val.toAdd v.2
        apply Prod.ext <;> exact CharTwo.add_cancel_left _ _
      · apply Prod.ext <;> dsimp <;> exact CharTwo.add_self_eq_zero _

private theorem cyclic_projective (H : Subgroup E) [IsCyclic H] :
    Module.Projective K[H]
      (Representation.asModule (rho.comp H.subtype : Representation K H V)) := by
  classical
  apply (PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
    2 1 (by decide) (by simpa using (CharP.cast_eq_zero K 2))
    ((FiniteFieldCyclicDimension.elementary_isPGroup 2 4).to_subgroup H)
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
  · have ht : h.val.toAdd ≠ 0 := by
      intro ht
      apply hh
      apply Subtype.ext
      exact Multiplicative.toAdd.injective ht
    have hw : (w : V).1 + code h.val.toAdd (w : V).2 = (w : V).1 :=
      congrArg Prod.fst (w.property h)
    have hz : code h.val.toAdd (w : V).2 = 0 :=
      add_left_cancel (hw.trans (add_zero _).symm)
    have hw2 : (w : V).2 = 0 :=
      (code_bijective _ ht).1 (hz.trans (map_zero _).symm)
    let e := LinearEquiv.ofBijective (code h.val.toAdd) (code_bijective _ ht)
    refine ⟨(0, e.symm (w : V).1), ?_⟩
    rw [cyclic_norm H h hgen hh]
    exact Prod.ext (e.apply_symm_apply (w : V).1) hw2.symm

private def direction (i : Fin 4) : E := Multiplicative.ofAdd (Pi.single i 1)

private theorem code_identity (u : U) : code (direction 0).toAdd u = u := by
  apply Prod.ext <;> simp [direction, code, coeff]

-- This argument starts with an arbitrary intertwiner of the entire space.
-- The identity direction recovers the layer and its injective first readout.
private theorem no_field_model {L : Type*} [Field L] [Algebra K L]
    (T : V ≃ₗ[K] L × L) (c : E → L)
    (hT : ∀ (g : E) (z : V), T (rho g z) =
      ((T z).1 + c g * (T z).2, (T z).2)) : False := by
  have haug (g : E) (z : V) :
      T (code g.toAdd z.2, 0) = (c g * (T z).2, 0) := by
    have he := congrArg (fun y : L × L => y - T z) (hT g z)
    rw [← map_sub] at he
    have hz : rho g z - z = (code g.toAdd z.2, 0) := by
      apply Prod.ext <;> simp [rho, actionMap]
    rw [hz] at he
    refine he.trans ?_
    apply Prod.ext <;> simp
  have hid (u : U) : T (u, 0) = (c (direction 0) * (T (0, u)).2, 0) := by
    simpa only [code_identity] using haug (direction 0) (0, u)
  have hc : c (direction 0) ≠ 0 := by
    intro hc
    have he := hid (1, 0)
    rw [hc, zero_mul] at he
    have hz : (((1, 0), 0) : V) = 0 := T.injective (he.trans T.map_zero.symm)
    exact one_ne_zero (congrArg (fun z : V => z.1.1) hz)
  have hlayer (u : U) : (T (u, 0)).2 = 0 := by
    have he := haug (direction 0) (u, 0)
    simp only [map_zero] at he
    have hz : c (direction 0) * (T (u, 0)).2 = 0 := by
      have := congrArg Prod.fst he
      have hz0 : T (0, 0) = 0 := T.map_zero
      rw [hz0] at this
      exact this.symm
    exact (mul_eq_zero.mp hz).resolve_left hc
  let P : U → L := fun u => (T (u, 0)).1
  have hP : Function.Injective P := by
    intro u v huv
    have he : T (u, 0) = T (v, 0) := Prod.ext huv ((hlayer u).trans (hlayer v).symm)
    exact congrArg Prod.fst (T.injective he)
  have hnorm (g : E) (u : U) :
      P (code g.toAdd u) = (c g / c (direction 0)) * P u := by
    have hg : P (code g.toAdd u) = c g * (T (0, u)).2 :=
      congrArg Prod.fst (haug g (0, u))
    have h0 : P u = c (direction 0) * (T (0, u)).2 := congrArg Prod.fst (hid u)
    rw [hg, h0]
    field_simp
  have hcomm (g h : E) (u : U) :
      code g.toAdd (code h.toAdd u) = code h.toAdd (code g.toAdd u) := by
    apply hP
    rw [hnorm, hnorm, hnorm, hnorm]
    ring
  have he := congrArg Prod.snd (hcomm (direction 1) (direction 2) (1, 0))
  have he' : root * root + root * (1 + root) = 1 + root := by
    simpa [direction, code, coeff] using he
  have h01 : (1 : K) = 0 := by
    have hs : root * root + root * (1 + root) = root := by
      calc
        _ = root + (root * root + root * root) := by ring
        _ = root := by rw [CharTwo.add_self_eq_zero, add_zero]
    rw [hs] at he'
    exact add_right_cancel (he'.symm.trans (zero_add root).symm)
  exact one_ne_zero h01

/-- The closed assertion that minimal actual-cyclic-projective, square-zero
representations on the fixed K, E and V are field-scalar shears. -/
def field_translation_universality : Prop :=
  ∀ tau : Representation K E V,
    (∀ H : Subgroup E, IsCyclic H → Module.Projective K[H]
      (Representation.asModule (tau.comp H.subtype : Representation K H V))) →
    Module.finrank K V = 2 * (4 ⌈/⌉ Module.finrank (ZMod 2) K) →
    (∀ g h : E, (tau g - 1) * (tau h - 1) = 0) →
    ∃ (L : Type) (fieldL : Field L),
      letI : Field L := fieldL
      ∃ (algebraL : Algebra K L),
        letI : Algebra K L := algebraL
        ∃ (T : V ≃ₗ[K] L × L) (c : E → L),
          ∀ (g : E) (z : V), T (tau g z) =
            ((T z).1 + c g * (T z).2, (T z).2)

/-- A full-rank binary code on the common layer refutes field-translation
universality within the minimal, actual-cyclic-projective, square-zero class. -/
theorem field_translation_universality_fails : ¬ field_translation_universality := by
  intro h
  have hcyc : ∀ H : Subgroup E, IsCyclic H → Module.Projective K[H]
      (Representation.asModule (rho.comp H.subtype : Representation K H V)) := by
    intro H hH
    let : IsCyclic H := hH
    exact cyclic_projective H
  have hd : Module.finrank K V = 4 := by
    simp [V, U, Module.finrank_prod]
  have hf : Module.finrank (ZMod 2) K = 2 := GaloisField.finrank 2 (by decide)
  have hlower :=
    FiniteFieldCyclicDimension.prime_mul_ceilDiv_finrank_le_finrank_of_cyclic_projective
      2 4 rho hcyc
  have hmin : Module.finrank K V = 2 * (4 ⌈/⌉ Module.finrank (ZMod 2) K) := by
    apply Nat.le_antisymm
    · rw [hd, hf]
      decide
    · have halg : ZMod.algebra K 2 = (inferInstance : Algebra (ZMod 2) K) :=
        Subsingleton.elim _ _
      rw [halg] at hlower
      exact hlower
  obtain ⟨L, fieldL, algebraL, T, c, hinter⟩ := h rho hcyc hmin square_zero
  let : Field L := fieldL
  let : Algebra K L := algebraL
  exact no_field_model T c hinter

end D5.S3.FiniteGroups.GroupAlgebra.NonfieldSquareZeroAction
