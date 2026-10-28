/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction
   mirror-E: none(waiver:finite-nonabelian-countermodel)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.claim; result=D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.result; claim=D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.claim
   digest: An explicit noncommutative group of order 72 has an order-six element with square and cube roots but no sixth root. -/

import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SemidirectProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction

open QuaternionGroup Multiplicative

private abbrev Q8 := QuaternionGroup 2
private abbrev C9 := Multiplicative (ZMod 9)

/-- The quaternion-unit cycle, in Mathlib's `a, xa` coordinates. -/
private def cycleFun : Q8 → Q8
  | .a z => match z.val with
    | 0 => .a 0
    | 1 => .xa 0
    | 2 => .a 2
    | _ => .xa 2
  | .xa z => match z.val with
    | 0 => .xa 3
    | 1 => .a 3
    | 2 => .xa 1
    | _ => .a 1

private def cycle : MulAut Q8 where
  toFun := cycleFun
  invFun q := cycleFun (cycleFun q)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private def action : C9 →* MulAut Q8 where
  toFun r := cycle ^ r.toAdd.val
  map_one' := by ext q; rfl
  map_mul' r s := by
    have law : ∀ r s : C9, ∀ q : Q8,
        (cycle ^ (r * s).toAdd.val) q =
          (cycle ^ r.toAdd.val) ((cycle ^ s.toAdd.val) q) := by decide
    ext q
    exact law r s q

/-- Q8 semidirect C9, with the C9 generator cycling i, j, k. -/
abbrev H := Q8 ⋊[action] C9

instance : Fintype H := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

/-- The central element (-1,t^3) in the explicit semidirect product. -/
def h : H := ⟨.a 2, ofAdd 3⟩

private def a : H := ⟨.a 1, ofAdd 6⟩
private def b : H := ⟨.a 2, ofAdd 1⟩

set_option maxRecDepth 16384 in
private theorem square_root : a ^ 2 = h := by decide

set_option maxRecDepth 16384 in
private theorem cube_root : b ^ 3 = h := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem no_sixth_root : ∀ x : H, x ^ 6 ≠ h := by decide

/-- The concrete coprime-root sufficiency assertion at this holonomy. -/
def claim : Prop :=
  (∃ x : H, x ^ 2 = h) → (∃ x : H, x ^ 3 = h) → ∃ x : H, x ^ 6 = h

/-- Square and cube roots do not suffice for a sixth root in this finite group. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨x, hx⟩ := hc ⟨a, square_root⟩ ⟨b, cube_root⟩
  exact no_sixth_root x hx

/-- The exact finite nonabelian countermodel, including both specified roots. -/
theorem finite72_obstruction :
    Nat.card H = 72 ∧ orderOf h = 6 ∧
    (⟨.a 1, ofAdd 6⟩ : H) ^ 2 = h ∧
    (⟨.a 2, ofAdd 1⟩ : H) ^ 3 = h ∧
    (∀ x : H, x ^ 6 ≠ h) ∧
    (∃ x y : H, x * y ≠ y * x) := by
  refine ⟨?_, ?_, square_root, cube_root, ?_, ?_⟩
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, QuaternionGroup.card,
      Nat.card_eq_fintype_card]
    decide
  · apply (orderOf_eq_iff (by decide : 0 < 6)).2
    refine ⟨by decide, ?_⟩
    have small : ∀ m : Fin 6, 0 < m.val → h ^ m.val ≠ 1 := by decide
    intro m hm hpos
    exact small ⟨m, hm⟩ hpos
  · intro x hx
    exact result (fun _ _ => ⟨x, hx⟩)
  · exact ⟨⟨.a 1, 1⟩, ⟨.xa 0, 1⟩, by decide⟩

#print axioms result
#print axioms finite72_obstruction

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction
