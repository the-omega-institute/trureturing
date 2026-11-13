/- GID: D5/S0/Certificates/Algebra/BergmanQuestion23Refutation
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanQuestion23Refutation
   mirror-E: none(waiver:noncomputational)
   anchors: [D5/S0/Certificates/Algebra/BergmanQuestion15Refutation, mathlib/module/Mathlib.Data.Sym.Card, mathlib/module/Mathlib.Data.Finsupp.Multiset]
   utility: kind=none
   digest: Bounded monomials and their reverse-degree dual action for Question 23. -/

import D5.S0.Certificates.Algebra.BergmanQuestion15Refutation
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.Order.Monoid.Multiset
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace D5.S0.Certificates.Algebra.BergmanQuestion23Refutation

open scoped IsMulCommutative
open BergmanQuestion15Refutation

/-- A monomial in `m` variables, with multiplicities rather than divided powers. -/
abbrev Monomial (m : ℕ) := Multiset (Fin m)

/-- Nonconstant monomials below the truncation degree. -/
abbrev PositiveIndex (m t : ℕ) :=
  {a : Monomial m // 0 < a.card ∧ a.card ≤ t}

/-- Dual monomials include the constant coefficient functional. -/
abbrev DualIndex (m t : ℕ) := {a : Monomial m // a.card ≤ t}

/-- The absorbing zero and the two disjoint families of basis labels. -/
inductive Model (m t : ℕ) where
  | zero
  | e (a : PositiveIndex m t)
  | f (b : DualIndex m t)
  deriving DecidableEq

instance {m t : ℕ} : Zero (Model m t) := ⟨.zero⟩

private def eOf {m t : ℕ} (a : Monomial m) : Model m t :=
  if h : 0 < a.card ∧ a.card ≤ t then .e ⟨a, h⟩ else 0

private def act {m t : ℕ} (a : Monomial m) (b : DualIndex m t) : Model m t :=
  if h : a ≤ b.val then .f ⟨b.val - a, (Multiset.card_le_card (tsub_le_self)).trans b.property⟩
  else 0

/-- Truncated monomial multiplication and the transpose of monomial multiplication. -/
def modelMul {m t : ℕ} : Model m t → Model m t → Model m t
  | .e a, .e b => eOf (a.val + b.val)
  | .e a, .f b => act a.val b
  | .f b, .e a => act a.val b
  | _, _ => 0

instance {m t : ℕ} : Mul (Model m t) := ⟨modelMul⟩

private theorem zero_mul_model {m t : ℕ} (x : Model m t) : (0 : Model m t) * x = 0 := by
  cases x <;> rfl

private theorem mul_zero_model {m t : ℕ} (x : Model m t) : x * (0 : Model m t) = 0 := by
  cases x <;> rfl

private theorem mul_comm_model {m t : ℕ} (x y : Model m t) : x * y = y * x := by
  cases x <;> cases y <;> simp [HMul.hMul, Mul.mul, modelMul, add_comm]

private theorem eOf_e {m t : ℕ} (a : PositiveIndex m t) : eOf a.val = Model.e a := by
  simp [eOf, a.property]

private theorem eOf_mul_eOf {m t : ℕ} (a b : Monomial m)
    (ha : 0 < a.card) (hb : 0 < b.card) :
    (eOf a : Model m t) * eOf b = eOf (a + b) := by
  by_cases hA : a.card ≤ t
  · by_cases hB : b.card ≤ t
    · simp [eOf, ha, hb, hA, hB, HMul.hMul, Mul.mul, modelMul]
    · have hAB : ¬ (a + b).card ≤ t := by simp only [Multiset.card_add]; omega
      simp [eOf, ha, hb, hA, hB, hAB, mul_zero_model]
  · have hAB : ¬ (a + b).card ≤ t := by simp only [Multiset.card_add]; omega
    simp [eOf, ha, hb, hA, hAB, zero_mul_model]

private theorem eOf_mul_f {m t : ℕ} (a : Monomial m)
    (ha : 0 < a.card) (b : DualIndex m t) :
    (eOf a : Model m t) * .f b = act a b := by
  by_cases hA : a.card ≤ t
  · simp [eOf, ha, hA, HMul.hMul, Mul.mul, modelMul]
  · have hab : ¬ a ≤ b.val := fun h => hA ((Multiset.card_le_card h).trans b.property)
    simp [eOf, ha, hA, act, hab, zero_mul_model]

private theorem mul_act {m t : ℕ} (a : PositiveIndex m t)
    (b : Monomial m) (c : DualIndex m t) :
    (Model.e a : Model m t) * act b c = act (a.val + b) c := by
  by_cases hbc : b ≤ c.val
  · have hiff : a.val ≤ c.val - b ↔ a.val + b ≤ c.val := le_tsub_iff_right hbc
    simp only [act, dif_pos hbc]
    change act a.val ⟨c.val - b, _⟩ = _
    by_cases habc : a.val + b ≤ c.val
    · have hac : a.val ≤ c.val - b := hiff.mpr habc
      simp only [act, dif_pos hac, dif_pos habc]
      congr 2
      rw [← tsub_add_eq_tsub_tsub, add_comm]
    · have hac : ¬ a.val ≤ c.val - b := mt hiff.mp habc
      simp [act, hac, habc]
  · have habc : ¬ a.val + b ≤ c.val := fun h => hbc (le_add_self.trans h)
    simp [act, hbc, habc, mul_zero_model]

private theorem mul_assoc_model {m t : ℕ} (x y z : Model m t) :
    (x * y) * z = x * (y * z) := by
  cases x with
  | zero => simp [zero_mul_model]
  | e a =>
    cases y with
    | zero => simp [zero_mul_model, mul_zero_model]
    | e b =>
      cases z with
      | zero => simp [mul_zero_model]
      | e c =>
        change eOf (a.val + b.val) * Model.e c = Model.e a * eOf (b.val + c.val)
        rw [← eOf_e a, ← eOf_e c]
        rw [eOf_mul_eOf _ _ (by simpa using Nat.add_pos_left a.property.1 b.val.card)
          c.property.1, eOf_mul_eOf _ _ a.property.1
          (by simpa using Nat.add_pos_left b.property.1 c.val.card)]
        rw [add_assoc]
      | f c =>
        change eOf (a.val + b.val) * Model.f c = Model.e a * act b.val c
        rw [eOf_mul_f _ (by simpa using Nat.add_pos_left a.property.1 b.val.card), mul_act]
    | f b =>
      cases z with
      | zero => simp [mul_zero_model]
      | e c =>
        change act a.val b * Model.e c = Model.e a * act c.val b
        rw [mul_comm_model, mul_act, mul_act, add_comm]
      | f c =>
        change act a.val b * Model.f c = Model.e a * 0
        simp only [act]
        split <;> simp [HMul.hMul, Mul.mul, modelMul, mul_zero_model, zero_mul_model]
  | f a =>
    cases y with
    | zero => simp [zero_mul_model, mul_zero_model]
    | e b =>
      cases z with
      | zero => simp [mul_zero_model]
      | e c =>
        rw [mul_comm_model (Model.f a) (Model.e b),
          mul_comm_model (Model.f a) (Model.e b * Model.e c)]
        change act b.val a * Model.e c = eOf (b.val + c.val) * Model.f a
        rw [mul_comm_model, mul_act,
          eOf_mul_f _ (by simpa using Nat.add_pos_left b.property.1 c.val.card), add_comm]
      | f c =>
        change act b.val a * Model.f c = Model.f a * act b.val c
        simp only [act]
        split <;> split <;> rfl
    | f b =>
      cases z with
      | zero => rfl
      | e c =>
        change 0 = Model.f a * act c.val b
        simp only [act]
        split <;> rfl
      | f c => rfl

instance {m t : ℕ} : SemigroupWithZero (Model m t) where
  zero_mul := zero_mul_model
  mul_zero := mul_zero_model
  mul_assoc := mul_assoc_model

instance {m t : ℕ} : IsMulCommutative (Model m t) := ⟨⟨mul_comm_model⟩⟩

/-- The positive ideal of the truncated idealization, over an arbitrary field. -/
abbrev Ambient (F : Type*) [Field F] (m t : ℕ) := Contracted F (Model m t)

end D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
