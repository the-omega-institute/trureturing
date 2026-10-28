import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation
import Mathlib.GroupTheory.SpecificGroups.Quaternion

open D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation

#print pow_eq_pow_iff_exists_unique
#print axioms pow_eq_pow_iff_exists_unique

-- Natural zero and one boundaries retain the exact unique witness.
example {G : Type*} [Group G] [Group.IsNilpotent G] (x : G) :
    ∃! z : G, x = z ^ 1 ∧ (1 : G) = z ^ 0 :=
  (pow_eq_pow_iff_exists_unique x 1 0 1 (by decide)).mp (by simp)

example {G : Type*} [Group G] [Group.IsNilpotent G] (y : G) :
    ∃! z : G, (1 : G) = z ^ 0 ∧ y = z ^ 1 :=
  (pow_eq_pow_iff_exists_unique 1 y 1 0 (by decide)).mp (by simp)

example {G : Type*} [Group G] [Group.IsNilpotent G] (x : G) :
    ∃! z : G, x = z ^ 1 ∧ x = z ^ 1 :=
  (pow_eq_pow_iff_exists_unique x x 1 1 (by decide)).mp rfl

private abbrev Q8 := QuaternionGroup 2
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Group.IsNilpotent Q8 :=
  (IsPGroup.of_card (p := 2) (n := 3) (G := Q8) (by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    decide)).isNilpotent

private abbrev i : Q8 := QuaternionGroup.a 1
private abbrev j : Q8 := QuaternionGroup.xa 0

example : ¬ Commute i j := by decide
example : i ≠ j ∧ i ^ 2 = j ^ 2 ∧ i ^ 2 ≠ 1 := by decide
example : ¬ ∃ z : Q8, i = z ^ 2 ∧ j = z ^ 2 := by
  rintro ⟨z,hz,hj⟩
  exact (by decide : i ≠ j) (hz.trans hj.symm)

-- Both m=2 and n=3 powers are nontrivial in the finite torsion example.
example : i ^ 2 ≠ 1 ∧ i ^ 3 ≠ 1 := by decide
example : ∃! z : Q8, i ^ 3 = z ^ 3 ∧ i ^ 2 = z ^ 2 :=
  (pow_eq_pow_iff_exists_unique (i ^ 3) (i ^ 2) 2 3 (by decide)).mp (by decide)
example (w : Q8) (hw : i ^ 3 = w ^ 3 ∧ i ^ 2 = w ^ 2) : w = i := by
  obtain ⟨z,_,hu⟩ :=
    (pow_eq_pow_iff_exists_unique (i ^ 3) (i ^ 2) 2 3 (by decide)).mp (by decide)
  exact (hu w hw).trans (hu i ⟨rfl,rfl⟩).symm

private abbrev InfiniteExample := Q8 × Multiplicative ℤ
private abbrev bigz : InfiniteExample := (i, Multiplicative.ofAdd 1)

example : Infinite InfiniteExample := inferInstance
example : Group.IsNilpotent InfiniteExample := inferInstance
example : ¬ Commute (i, (1 : Multiplicative ℤ)) (j, 1) := by decide
example : bigz ^ 2 = (QuaternionGroup.a 2, Multiplicative.ofAdd 2) := by decide
example : bigz ^ 3 = (QuaternionGroup.a 3, Multiplicative.ofAdd 3) := by decide
example : bigz ^ 2 ≠ 1 ∧ bigz ^ 3 ≠ 1 := by decide
example : ∃! z : InfiniteExample,
    (QuaternionGroup.a 3, Multiplicative.ofAdd 3) = z ^ 3 ∧
    (QuaternionGroup.a 2, Multiplicative.ofAdd 2) = z ^ 2 :=
  (pow_eq_pow_iff_exists_unique _ _ 2 3 (by decide)).mp (by decide)
example (w : InfiniteExample) (hw : bigz ^ 3 = w ^ 3 ∧ bigz ^ 2 = w ^ 2) : w = bigz := by
  obtain ⟨z,_,hu⟩ :=
    (pow_eq_pow_iff_exists_unique (bigz ^ 3) (bigz ^ 2) 2 3 (by decide)).mp (by decide)
  exact (hu w hw).trans (hu bigz ⟨rfl,rfl⟩).symm
