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
import Mathlib.Tactic

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
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by simpa [Nat.card_eq_fintype_card] using field_card
  have hex : ∃ w : K, w ≠ 0 ∧ w ≠ 1 := by
    by_contra hn
    push_neg at hn
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

private def coeff (t : Fin 4 → ZMod 2) (i : Fin 4) : K := algebraMap (ZMod 2) K (t i)

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
  have hw : root + 1 ≠ 0 := by
    intro h
    have : root = 1 := by linear_combination h
    exact root_one this
  fin_cases h0 : t 0 <;> fin_cases h1 : t 1 <;>
    fin_cases h2 : t 2 <;> fin_cases h3 : t 3
  all_goals simp [determinant, coeff, h0, h1, h2, h3]
  all_goals try { exfalso; apply ht; ext i; fin_cases i <;> assumption }
  all_goals ring_nf
  all_goals reduce_mod_char!
  all_goals simp [root_square, root_zero, hw]
