/- GID: D5/S3/FiniteGroups/Heisenberg/Basic
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Heisenberg/Basic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Heisenberg triples, powers and their derived subgroup. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Compatible port of consumed material from TauCetiProject/TauCeti,
commit 29b9cc14af71b7c058316535d555c9bbf64b2df7,
TauCeti/GroupTheory/SpecificGroups/Heisenberg.lean,
SHA-256 463ecf30758118dfaf714cda9a0af728ddfaf4806547aa5cf9ea8a22b79e0be7.
Retire this port when the repository's pinned Mathlib supplies equivalent APIs.
-/

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

open Subgroup
open scoped commutatorElement

namespace D5.S3.FiniteGroups

/-- The **Heisenberg group** over a ring `R`: triples `(x, y, z)` with the
multiplication `(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x * y')`, the group of
unipotent upper triangular `3 × 3` matrices in the coordinates of the strictly upper triangle. -/
@[ext]
structure HeisenbergGroup (R : Type*) where
  /-- The `(1, 2)` matrix entry. -/
  x : R
  /-- The `(2, 3)` matrix entry. -/
  y : R
  /-- The `(1, 3)` matrix entry. -/
  z : R

namespace HeisenbergGroup

variable {R : Type*}

/-- The Heisenberg group is the product `R × R × R` as a type. -/
def equivProd : HeisenbergGroup R ≃ R × R × R where
  toFun a := (a.x, a.y, a.z)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

instance [Fintype R] : Fintype (HeisenbergGroup R) := Fintype.ofEquiv _ equivProd.symm

instance [Finite R] : Finite (HeisenbergGroup R) := Finite.of_equiv _ equivProd.symm

/-- The Heisenberg group over `R` has cardinality `(Nat.card R) ^ 3`; over `𝔽_p` its order is
`p ^ 3`. -/
theorem card_eq : Nat.card (HeisenbergGroup R) = Nat.card R ^ 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod]
  ring

variable [Ring R]

instance : Mul (HeisenbergGroup R) := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩⟩
instance : One (HeisenbergGroup R) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (HeisenbergGroup R) := ⟨fun a => ⟨-a.x, -a.y, -a.z + a.x * a.y⟩⟩

@[simp] theorem mul_x (a b : HeisenbergGroup R) : (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y (a b : HeisenbergGroup R) : (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_z (a b : HeisenbergGroup R) : (a * b).z = a.z + b.z + a.x * b.y := rfl
@[simp] theorem one_x : (1 : HeisenbergGroup R).x = 0 := rfl
@[simp] theorem one_y : (1 : HeisenbergGroup R).y = 0 := rfl
@[simp] theorem one_z : (1 : HeisenbergGroup R).z = 0 := rfl
@[simp] theorem inv_x (a : HeisenbergGroup R) : a⁻¹.x = -a.x := rfl
@[simp] theorem inv_y (a : HeisenbergGroup R) : a⁻¹.y = -a.y := rfl
@[simp] theorem inv_z (a : HeisenbergGroup R) : a⁻¹.z = -a.z + a.x * a.y := rfl

instance : Group (HeisenbergGroup R) where
  mul_assoc a b c := by ext <;> simp only [mul_x, mul_y, mul_z, add_mul, mul_add] <;> abel
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

/-- **The commutator formula**: `⁅(x, y, z), (x', y', z')⁆ = (0, 0, x * y' - x' * y)`. -/
theorem commutatorElement_eq (a b : HeisenbergGroup R) :
    ⁅a, b⁆ = ⟨0, 0, a.x * b.y - b.x * a.y⟩ := by
  ext <;> simp [commutatorElement_def, add_mul]
  abel

/-- **The power formula**: `(x, y, z) ^ n = (n • x, n • y, n • z + (n choose 2) • (x * y))`. -/
theorem pow_eq (a : HeisenbergGroup R) (n : ℕ) :
    a ^ n = ⟨n • a.x, n • a.y, n • a.z + n.choose 2 • (a.x * a.y)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    ext <;> simp [add_smul, nsmul_eq_mul, mul_assoc]
    abel

/-- The **`z`-axis** `{(0, 0, z)}`, a central subgroup. -/
def zAxis : Subgroup (HeisenbergGroup R) where
  carrier := {a | a.x = 0 ∧ a.y = 0}
  mul_mem' := by
    rintro a b ⟨hax, hay⟩ ⟨hbx, hby⟩
    simp [hax, hay, hbx, hby]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨hax, hay⟩
    simp [hax, hay]

@[simp]
theorem mem_zAxis_iff {a : HeisenbergGroup R} : a ∈ zAxis ↔ a.x = 0 ∧ a.y = 0 := Iff.rfl

/-- Every commutator lies on the `z`-axis: the Heisenberg group is nilpotent of class at most
two. -/
theorem commutatorElement_mem_zAxis (a b : HeisenbergGroup R) : ⁅a, b⁆ ∈ zAxis := by
  rw [commutatorElement_eq]
  exact ⟨rfl, rfl⟩

/-- **The commutator subgroup of the Heisenberg group is its `z`-axis**: every commutator lies on
the `z`-axis, and `(0, 0, c)` is the commutator of `(c, 0, 0)` and `(0, 1, 0)`. -/
theorem commutator_eq_zAxis : commutator (HeisenbergGroup R) = zAxis := by
  refine le_antisymm (commutator_le.mpr fun a _ b _ ↦ commutatorElement_mem_zAxis a b)
    fun a ha ↦ ?_
  obtain ⟨hax, hay⟩ := mem_zAxis_iff.mp ha
  have h : ⁅(⟨a.z, 0, 0⟩ : HeisenbergGroup R), ⟨0, 1, 0⟩⁆ = a := by
    rw [commutatorElement_eq]
    ext <;> simp [hax, hay]
  rw [← h]
  exact commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)


end HeisenbergGroup
end D5.S3.FiniteGroups
