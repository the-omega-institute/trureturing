/- GID: D5/S0/Certificates/Algebra/BergmanQuestion23Refutation
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanQuestion23Refutation
   mirror-E: none(waiver:noncomputational)
   anchors: [D5/S0/Certificates/Algebra/BergmanQuestion15Refutation, mathlib/module/Mathlib.Data.Sym.Card, mathlib/module/Mathlib.Data.Finsupp.Multiset]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.claim; result=D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.result; claim=D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.claim
   digest: A generic truncated idealization refutes Bergman's Question 23. -/

import D5.S0.Certificates.Algebra.BergmanQuestion15Refutation
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.Order.Monoid.Multiset
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Bilinear
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # The truncated monomial idealization for Bergman's Question 23 -/

noncomputable section

namespace D5.S0.Certificates.Algebra.BergmanQuestion23Refutation

open scoped IsMulCommutative
open BergmanQuestion15Refutation

section Question

variable {F R : Type*} [Field F] [AddCommGroup R] [Module F R]

/-- Index `k` means exactly `k+1` factors from `V`; the span includes mixed products. -/
def mixedPower (μ : R →ₗ[F] R →ₗ[F] R) (V : Submodule F R) : ℕ → Submodule F R
  | 0 => V
  | k + 1 => Submodule.map₂ μ V (mixedPower μ V k)

private theorem mixedPower_finite (μ : R →ₗ[F] R →ₗ[F] R)
    (V : Submodule F R) [FiniteDimensional F V] (k : ℕ) :
    FiniteDimensional F (mixedPower μ V k) := by
  induction k with
  | zero => change FiniteDimensional F V; infer_instance
  | succ k ih =>
    exact (Submodule.fg_iff_finiteDimensional _).mp
      (((Submodule.fg_iff_finiteDimensional V).mpr inferInstance).map₂ μ
        ((Submodule.fg_iff_finiteDimensional _).mpr ih))

/-- The annihilator is a subspace of `V`, so its quotient is literally the source quotient. -/
def relativeAnnihilator (μ : R →ₗ[F] R →ₗ[F] R)
    (V W : Submodule F R) : Submodule F V where
  carrier := {x | ∀ w ∈ W, μ x.val w = 0}
  zero_mem' := by intro w hw; simp
  add_mem' hx hy := by intro w hw; simp [map_add, hx w hw, hy w hw]
  smul_mem' a x hx := by intro w hw; simp [map_smul, hx w hw]

/-- The complete universal assertion in Bergman's Question 23.
No identity, characteristic, finiteness of the ambient algebra, or nilpotence is assumed.
The index `k : ℕ` ranges over all positive exponents `k+1`. -/
def claim : Prop :=
  ∀ (F R : Type) [Field F] [AddCommGroup R] [Module F R]
    (μ : R →ₗ[F] R →ₗ[F] R),
    (∀ x y z, μ (μ x y) z = μ x (μ y z)) →
    (∀ x y, μ x y = μ y x) →
    ∀ (V : Submodule F R), FiniteDimensional F V → ∀ k : ℕ,
      Module.finrank F (V ⧸ relativeAnnihilator μ V (mixedPower μ V k)) ≤
        Module.finrank F (mixedPower μ V k)

end Question

/-- A monomial in `m` variables, with multiplicities rather than divided powers. -/
abbrev Monomial (m : ℕ) := Multiset (Fin m)

/-- Nonconstant monomials below the truncation degree. -/
abbrev PositiveIndex (m t : ℕ) :=
  {a : Monomial m // 0 < a.card ∧ a.card ≤ t}

/-- Dual monomials include the constant coefficient functional. -/
abbrev DualIndex (m t : ℕ) := {a : Monomial m // a.card ≤ t}

private def boundedEquiv (m t : ℕ) :
    DualIndex m t ≃ (k : Fin (t + 1)) × Sym (Fin m) k.val where
  toFun a := ⟨⟨a.val.card, Nat.lt_succ_of_le a.property⟩, ⟨a.val, rfl⟩⟩
  invFun a := ⟨a.2.val, a.2.property.trans_le (Nat.le_of_lt_succ a.1.isLt)⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨k, hk⟩, ⟨a, ha⟩⟩
    cases ha
    rfl

noncomputable instance (m t : ℕ) : Fintype (DualIndex m t) :=
  Fintype.ofEquiv _ (boundedEquiv m t).symm

instance (m t : ℕ) : Finite (PositiveIndex m t) :=
  Finite.of_injective (fun a : PositiveIndex m t =>
    (⟨a.val, a.property.2⟩ : DualIndex m t)) (by
      intro a b h
      exact Subtype.ext (congrArg (fun x : DualIndex m t => x.val) h))

noncomputable instance (m t : ℕ) : Fintype (PositiveIndex m t) := Fintype.ofFinite _

/-- The absorbing zero and the two disjoint families of basis labels. -/
inductive Model (m t : ℕ) where
  | zero
  | e (a : PositiveIndex m t)
  | f (b : DualIndex m t)
  deriving DecidableEq, Fintype

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
      simp [eOf, ha, hb, hA, hB, mul_zero_model] <;> omega
  · have hAB : ¬ (a + b).card ≤ t := by simp only [Multiset.card_add]; omega
    simp [eOf, ha, hb, hA, zero_mul_model] <;> omega

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
  | zero =>
    change (0 * y) * z = (0 : Model m t) * (y * z)
    simp only [zero_mul_model]
  | e a =>
    cases y with
    | zero =>
      change (Model.e a * 0) * z = Model.e a * (0 * z)
      simp only [zero_mul_model, mul_zero_model]
    | e b =>
      cases z with
      | zero =>
        change (Model.e a * Model.e b) * 0 = Model.e a * (Model.e b * 0)
        simp only [mul_zero_model]
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
      | zero =>
        change (Model.e a * Model.f b) * 0 = Model.e a * (Model.f b * 0)
        simp only [mul_zero_model]
      | e c =>
        change act a.val b * Model.e c = Model.e a * act c.val b
        rw [mul_comm_model, mul_act, mul_act, add_comm]
      | f c =>
        change act a.val b * Model.f c = Model.e a * 0
        simp only [act]
        split <;> simp [HMul.hMul, Mul.mul, modelMul, mul_zero_model, zero_mul_model]
  | f a =>
    cases y with
    | zero =>
      change (Model.f a * 0) * z = Model.f a * (0 * z)
      simp only [zero_mul_model, mul_zero_model]
    | e b =>
      cases z with
      | zero =>
        change (Model.f a * Model.e b) * 0 = Model.f a * (Model.e b * 0)
        simp only [mul_zero_model]
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

/-- The dual summand has the reversed positive grading. -/
def labelDegree {m t : ℕ} : Model m t → ℕ
  | .zero => 0
  | .e a => a.val.card
  | .f b => t + 1 - b.val.card

/-- The actual degree-`d` subspace of the contracted algebra. -/
def layer (F : Type*) [Field F] (m t d : ℕ) : Submodule F (Ambient F m t) :=
  Finsupp.supported F F {s : {s : Model m t // s ≠ 0} | labelDegree s.val = d}

private theorem labelDegree_pos {m t : ℕ} (s : Model m t) (hs : s ≠ 0) :
    0 < labelDegree s := by
  cases s with
  | zero => exact False.elim (hs rfl)
  | e a => exact a.property.1
  | f b => dsimp [labelDegree]; have := b.property; omega

private theorem labelDegree_le {m t : ℕ} (s : Model m t) : labelDegree s ≤ t + 1 := by
  cases s with
  | zero => exact Nat.zero_le _
  | e a => exact a.property.2.trans (Nat.le_succ _)
  | f b => exact Nat.sub_le _ _

private theorem labelDegree_mul {m t : ℕ} (s r : Model m t) (h : s * r ≠ 0) :
    labelDegree (s * r) = labelDegree s + labelDegree r := by
  cases s with
  | zero => exact False.elim (h (zero_mul _))
  | e a =>
    cases r with
    | zero => exact False.elim (h (mul_zero _))
    | e b =>
      change labelDegree (eOf (a.val + b.val)) = _
      have h' : eOf (a.val + b.val) ≠ (0 : Model m t) := h
      simp only [eOf] at h' ⊢
      split <;> simp_all [labelDegree]
    | f b =>
      change labelDegree (act a.val b) = _
      have h' : act a.val b ≠ (0 : Model m t) := h
      simp only [act] at h' ⊢
      split
      · rename_i hab
        simp only [labelDegree, Multiset.card_sub hab]
        have hc := Multiset.card_le_card hab
        have hb := b.property
        omega
      · rename_i hbad
        exact False.elim (h' (by simp [hbad]))
  | f a =>
    cases r with
    | zero => exact False.elim (h (mul_zero _))
    | e b =>
      rw [mul_comm] at h ⊢
      have h' : act b.val a ≠ (0 : Model m t) := h
      change labelDegree (act b.val a) = _
      simp only [act] at h' ⊢
      split
      · rename_i hba
        simp only [labelDegree, Multiset.card_sub hba]
        have hc := Multiset.card_le_card hba
        have ha := a.property
        omega
      · rename_i hbad
        exact False.elim (h' (by simp [hbad]))
    | f b => exact False.elim (h rfl)

private theorem single_mul {F : Type*} [Field F] {m t : ℕ}
    (a b : {s : Model m t // s ≠ 0}) (r s : F) :
    (Finsupp.single a r : Ambient F m t) * Finsupp.single b s =
      (r * s) • delta F (Model m t) (a.val * b.val) := by
  classical
  simp [HMul.hMul, Mul.mul, product, Finsupp.llift, Finsupp.lift_apply, smul_smul]

private theorem layer_mul_le {F : Type*} [Field F] {m t i j : ℕ} :
    Submodule.map₂ (product F (Model m t)) (layer F m t i) (layer F m t j) ≤
      layer F m t (i + j) := by
  classical
  rw [layer, layer, Finsupp.supported_eq_span_single, Finsupp.supported_eq_span_single,
    Submodule.map₂_span_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  change Finsupp.single a (1 : F) * Finsupp.single b 1 ∈ _
  rw [single_mul]
  by_cases hab : a.val * b.val = 0
  · simp [hab, delta]
  · simp only [one_mul, one_smul, delta, dif_neg hab]
    apply Finsupp.single_mem_supported F 1
    change labelDegree (a.val * b.val) = i + j
    rw [labelDegree_mul _ _ hab, ha, hb]

private theorem delta_mul {F : Type*} [Field F] {m t : ℕ} (s r : Model m t) :
    delta F (Model m t) s * delta F (Model m t) r = delta F (Model m t) (s * r) := by
  classical
  by_cases hs : s = 0
  · simp [hs, delta]
  by_cases hr : r = 0
  · simp [hr, delta]
  by_cases hsr : s * r = 0
  · simp [delta, hs, hr, single_mul, hsr]
  · simp [delta, hs, hr, single_mul, hsr]

private theorem delta_mem_layer {F : Type*} [Field F] {m t d : ℕ}
    (s : Model m t) (hs : labelDegree s = d) :
    delta F (Model m t) s ∈ layer F m t d := by
  classical
  by_cases hz : s = 0
  · simp [hz, delta]
  · simp only [delta, dif_neg hz]
    exact Finsupp.single_mem_supported F 1 hs

private theorem layer_le {F : Type*} [Field F] {m t d : ℕ}
    (W : Submodule F (Ambient F m t))
    (h : ∀ s : Model m t, labelDegree s = d → delta F (Model m t) s ∈ W) :
    layer F m t d ≤ W := by
  classical
  rw [layer, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  rcases s with ⟨s, hs0⟩
  have H := h s hs
  have heq : delta F (Model m t) s = Finsupp.single ⟨s, hs0⟩ (1 : F) := by
    ext a
    simp [delta, hs0, Finsupp.single_apply]
  rwa [heq] at H

private theorem layer_le_mul {F : Type*} [Field F] {m t d : ℕ}
    (hm : 0 < m) (hd : 1 ≤ d) (hdt : d ≤ t) :
    layer F m t (d + 1) ≤
      Submodule.map₂ (product F (Model m t)) (layer F m t 1) (layer F m t d) := by
  classical
  apply layer_le
  intro s hs
  cases s with
  | zero =>
    change delta F (Model m t) (0 : Model m t) ∈ _
    simp [delta]
  | e a =>
    obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp a.property.1
    obtain ⟨b, hab⟩ := Multiset.exists_cons_of_mem hi
    have hcard : b.card = d := by
      change a.val.card = d + 1 at hs
      rw [hab, Multiset.card_cons] at hs
      omega
    let u : PositiveIndex m t := ⟨{i}, by simp only [Multiset.card_singleton]; omega⟩
    let v : PositiveIndex m t := ⟨b, by omega⟩
    have hu : labelDegree (Model.e u) = 1 := by simp [labelDegree, u]
    have hv : labelDegree (Model.e v) = d := hcard
    have huv : (Model.e u : Model m t) * Model.e v = Model.e a := by
      change eOf ({i} + b) = Model.e a
      rw [Multiset.singleton_add, ← hab, eOf_e]
    have H := Submodule.apply_mem_map₂ (product F (Model m t))
      (delta_mem_layer _ hu) (delta_mem_layer _ hv)
    change delta F (Model m t) (Model.e u) * delta F (Model m t) (Model.e v) ∈ _ at H
    rwa [delta_mul, huv] at H
  | f b =>
    let i : Fin m := ⟨0, hm⟩
    have hcard : b.val.card + d = t := by
      change t + 1 - b.val.card = d + 1 at hs
      have := b.property
      omega
    let u : PositiveIndex m t := ⟨{i}, by simp only [Multiset.card_singleton]; omega⟩
    let v : DualIndex m t := ⟨b.val + {i}, by
      simp only [Multiset.card_add, Multiset.card_singleton]
      omega⟩
    have hu : labelDegree (Model.e u) = 1 := by simp [labelDegree, u]
    have hv : labelDegree (Model.f v) = d := by
      simp only [labelDegree, v, Multiset.card_add, Multiset.card_singleton]
      omega
    have huv : (Model.e u : Model m t) * Model.f v = Model.f b := by
      change act {i} v = Model.f b
      have hle : ({i} : Monomial m) ≤ v.val := le_add_self
      simp only [act, dif_pos hle]
      congr 2
      exact add_tsub_cancel_right b.val {i}
    have H := Submodule.apply_mem_map₂ (product F (Model m t))
      (delta_mem_layer _ hu) (delta_mem_layer _ hv)
    change delta F (Model m t) (Model.e u) * delta F (Model m t) (Model.f v) ∈ _ at H
    rwa [delta_mul, huv] at H

private theorem mixedPower_layer_eq {F : Type*} [Field F] {m t : ℕ}
    (hm : 0 < m) (k : ℕ) (hkt : k + 1 ≤ t) :
    mixedPower (product F (Model m t)) (layer F m t 1) k = layer F m t (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mixedPower, ih (by omega)]
    apply le_antisymm
    · simpa only [Nat.add_comm 1] using (layer_mul_le (F := F) (i := 1) (j := k + 1))
    · exact layer_le_mul hm (by omega) (by omega)

private def layerIndexEquiv {m t d : ℕ} (hd : 1 ≤ d) (hdt : d ≤ t) :
    {s : {s : Model m t // s ≠ 0} // labelDegree s.val = d} ≃
      Sym (Fin m) d ⊕ Sym (Fin m) (t + 1 - d) where
  toFun := by
    rintro ⟨⟨s, hs0⟩, hs⟩
    cases s with
    | zero => exact False.elim (hs0 rfl)
    | e a => exact .inl ⟨a.val, hs⟩
    | f b =>
      apply Sum.inr
      refine ⟨b.val, ?_⟩
      change t + 1 - b.val.card = d at hs
      have := b.property
      omega
  invFun := by
    intro s
    cases s with
    | inl a =>
      let e : PositiveIndex m t := ⟨a.val, by rw [a.property]; omega⟩
      exact ⟨⟨Model.e e, by intro h; cases h⟩, a.property⟩
    | inr b =>
      let f : DualIndex m t := ⟨b.val, by rw [b.property]; omega⟩
      refine ⟨⟨Model.f f, by intro h; cases h⟩, ?_⟩
      change t + 1 - b.val.card = d
      rw [b.property]
      omega
  left_inv := by
    rintro ⟨⟨s, hs0⟩, hs⟩
    cases s with
    | zero => exact False.elim (hs0 rfl)
    | e a => rfl
    | f b => rfl
  right_inv := by
    intro s
    cases s <;> rfl

private theorem finrank_layer {F : Type*} [Field F] {m t d : ℕ}
    (hd : 1 ≤ d) (hdt : d ≤ t) :
    Module.finrank F (layer F m t d) =
      (m + d - 1).choose d + (m + (t + 1 - d) - 1).choose (t + 1 - d) := by
  classical
  change Module.finrank F (Finsupp.supported F F _) = _
  rw [(Finsupp.supportedEquivFinsupp (M := F) (R := F) _).finrank_eq,
    Module.finrank_finsupp_self]
  calc
    _ = Fintype.card (Sym (Fin m) d ⊕ Sym (Fin m) (t + 1 - d)) :=
      Fintype.card_congr (layerIndexEquiv hd hdt)
    _ = _ := by simp only [Fintype.card_sum, Sym.card_sym_eq_choose, Fintype.card_fin]

private def eKey {m t : ℕ} (a : PositiveIndex m t) : {s : Model m t // s ≠ 0} :=
  ⟨.e a, by intro h; cases h⟩

private def fKey {m t : ℕ} (b : DualIndex m t) : {s : Model m t // s ≠ 0} :=
  ⟨.f b, by intro h; cases h⟩

private theorem delta_apply {F : Type*} [Field F] {m t : ℕ}
    (s : Model m t) (a : {s : Model m t // s ≠ 0}) :
    delta F (Model m t) s a = if s = a.val then 1 else 0 := by
  classical
  by_cases hs : s = 0
  · subst s
    simp [delta, Ne.symm a.property]
  · simp [delta, hs, Finsupp.single_apply, Subtype.ext_iff]

private theorem coeff_mul_delta_of_fiber {F : Type*} [Field F] {m t : ℕ}
    (a q r : {s : Model m t // s ≠ 0})
    (hfiber : ∀ s : Model m t, s * a.val = q.val ↔ s = r.val)
    (x : Ambient F m t) : (x * delta F (Model m t) a.val) q = x r := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [add_mul, Finsupp.add_apply, hx, hy]
  | single b c =>
    have ha : delta F (Model m t) a.val = Finsupp.single a 1 := by
      simp only [delta, dif_neg a.property]
    rw [ha, single_mul]
    simp only [mul_one, Finsupp.smul_apply, smul_eq_mul, delta_apply, hfiber,
      Finsupp.single_apply]
    by_cases hb : b = r
    · subst b; simp
    · have hbr : b.val ≠ r.val := fun h => hb (Subtype.ext h)
      simp [hb, hbr, Ne.symm hb]

private theorem coeff_mul_e {F : Type*} [Field F] {m t : ℕ}
    (a c : PositiveIndex m t) (hca : (c.val + a.val).card ≤ t) (x : Ambient F m t) :
    (x * delta F (Model m t) (.e a))
      (eKey ⟨c.val + a.val, ⟨by simp only [Multiset.card_add]; have := c.property.1; omega,
        hca⟩⟩) =
        x (eKey c) := by
  classical
  apply coeff_mul_delta_of_fiber (eKey a)
  intro s
  cases s with
  | zero => constructor <;> intro h <;> cases h
  | e b =>
    change eOf (b.val + a.val) = Model.e _ ↔ Model.e b = Model.e c
    simp only [eOf]
    split
    · simp only [Model.e.injEq, Subtype.mk.injEq, Subtype.ext_iff]
      exact add_right_cancel_iff
    · rename_i hbad
      constructor
      · intro h; cases h
      · intro h
        cases h
        exact False.elim (hbad ⟨by simp only [Multiset.card_add]; have := c.property.1; omega,
          hca⟩)
  | f b =>
    change act a.val b = Model.e _ ↔ Model.f b = Model.e c
    simp only [act]
    split <;> constructor <;> intro h <;> cases h

private theorem coeff_mul_f {F : Type*} [Field F] {m t : ℕ}
    (a : PositiveIndex m t) (b : DualIndex m t)
    (hba : (b.val + a.val).card ≤ t) (x : Ambient F m t) :
    (x * delta F (Model m t) (.e a)) (fKey b) = x (fKey ⟨b.val + a.val, hba⟩) := by
  classical
  apply coeff_mul_delta_of_fiber (eKey a)
  intro s
  cases s with
  | zero => constructor <;> intro h <;> cases h
  | e c =>
    change eOf (c.val + a.val) = Model.f b ↔ Model.e c = Model.f _
    simp only [eOf]
    split <;> constructor <;> intro h <;> cases h
  | f c =>
    change act a.val c = Model.f b ↔ Model.f c = Model.f _
    simp only [act]
    split
    · rename_i hac
      simp only [Model.f.injEq, Subtype.mk.injEq, Subtype.ext_iff]
      constructor
      · intro h
        rw [← h, tsub_add_cancel_of_le hac]
      · intro h
        rw [h, add_tsub_cancel_right]
    · rename_i hbad
      constructor
      · intro h; cases h
      · intro h
        have hc : c.val = b.val + a.val := congrArg Subtype.val (Model.f.inj h)
        exact False.elim (hbad (by rw [hc]; exact le_add_self))

private theorem annihilator_layer_eq_bot {F : Type*} [Field F] {m n : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) :
    relativeAnnihilator (product F (Model m (n + 1)))
      (layer F m (n + 1) 1) (layer F m (n + 1) n) = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply Subtype.ext
  apply Finsupp.ext
  rintro ⟨s, hs0⟩
  have hnot (h : labelDegree s ≠ 1) : x.val ⟨s, hs0⟩ = 0 :=
    (Finsupp.mem_supported' F x.val).mp x.property _ h
  by_cases hs : labelDegree s = 1
  · have hzero (a : PositiveIndex m (n + 1)) (ha : a.val.card = n) :
        x.val * delta F (Model m (n + 1)) (.e a) = 0 := by
      exact hx _ (delta_mem_layer _ ha)
    cases s with
    | zero => exact False.elim (hs0 rfl)
    | e c =>
      let i : Fin m := ⟨0, hm⟩
      let a : PositiveIndex m (n + 1) := ⟨Multiset.replicate n i, by simp; omega⟩
      have ha : a.val.card = n := by simp [a]
      have hca : (c.val + a.val).card ≤ n + 1 := by
        change c.val.card = 1 at hs
        simp only [Multiset.card_add, ha, hs]
        omega
      have H := coeff_mul_e a c hca x.val
      rw [hzero a ha] at H
      exact H.symm
    | f b =>
      have hb : b.val.card = n + 1 := by
        change n + 1 + 1 - b.val.card = 1 at hs
        have := b.property
        omega
      obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < b.val.card)
      let a : PositiveIndex m (n + 1) := ⟨b.val.erase i, by
        have H := Multiset.card_erase_add_one hi
        omega⟩
      have ha : a.val.card = n := by
        have H := Multiset.card_erase_add_one hi
        dsimp [a]; omega
      let c : DualIndex m (n + 1) := ⟨{i}, by simp⟩
      have hsum : c.val + a.val = b.val := by
        dsimp [c, a]
        exact Multiset.cons_erase hi
      have H := coeff_mul_f a c (by rw [hsum]; exact b.property) x.val
      rw [hzero a ha] at H
      have hkey : fKey ⟨c.val + a.val, by rw [hsum]; exact b.property⟩ = fKey b := by
        congr 2
      rw [hkey] at H
      exact H.symm
  · exact hnot hs

private theorem family_power {F : Type*} [Field F] {m n : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) :
    mixedPower (product F (Model m (n + 1))) (layer F m (n + 1) 1) (n - 1) =
      layer F m (n + 1) n := by
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
    mixedPower_layer_eq (F := F) hm (n - 1) (by omega : n - 1 + 1 ≤ n + 1)

private theorem family_annihilator {F : Type*} [Field F] {m n : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) :
    relativeAnnihilator (product F (Model m (n + 1))) (layer F m (n + 1) 1)
      (mixedPower (product F (Model m (n + 1))) (layer F m (n + 1) 1) (n - 1)) = ⊥ := by
  rw [family_power hm hn]
  exact annihilator_layer_eq_bot hm hn

private theorem family_v_dimension {F : Type*} [Field F] {m n : ℕ} :
    Module.finrank F (layer F m (n + 1) 1) = m + (m + n).choose (n + 1) := by
  simpa using (finrank_layer (F := F) (m := m) (t := n + 1) (d := 1) (by omega) (by omega))

private theorem family_power_dimension {F : Type*} [Field F] {m n : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) :
    Module.finrank F
      (mixedPower (product F (Model m (n + 1))) (layer F m (n + 1) 1) (n - 1)) =
      (m + n - 1).choose n + (m + 1).choose 2 := by
  rw [family_power hm hn]
  have htwo : n + 1 + 1 - n = 2 := by omega
  simpa only [htwo, show m + 2 - 1 = m + 1 by omega] using
    (finrank_layer (F := F) (m := m) (t := n + 1) (d := n) (by omega) (by omega))

private theorem family_quotient_dimension {F : Type*} [Field F] {m n : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) :
    Module.finrank F ((layer F m (n + 1) 1) ⧸
      relativeAnnihilator (product F (Model m (n + 1))) (layer F m (n + 1) 1)
        (mixedPower (product F (Model m (n + 1))) (layer F m (n + 1) 1) (n - 1))) =
      m + (m + n).choose (n + 1) := by
  rw [(Submodule.quotEquivOfEqBot _ (family_annihilator hm hn)).finrank_eq]
  exact family_v_dimension

private theorem dimension_defect {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n) :
    (m + (m + n).choose (n + 1)) - ((m + n - 1).choose n + (m + 1).choose 2) =
      (m + n - 1).choose (n + 1) - m.choose 2 ∧
    m.choose 3 ≤ (m + n - 1).choose (n + 1) - m.choose 2 ∧
    ((m + n - 1).choose n + (m + 1).choose 2) < m + (m + n).choose (n + 1) := by
  have hA : (m + 1).choose 3 ≤ (m + n - 1).choose (n + 1) := by
    calc
      _ = (m + 1).choose (m - 2) := Nat.choose_symm_of_eq_add (by omega)
      _ ≤ (m + n - 1).choose (m - 2) := Nat.choose_le_choose _ (by omega)
      _ = _ := Nat.choose_symm_of_eq_add (by omega)
  have hP := Nat.choose_succ_succ (m + n - 1) n
  simp only [Nat.succ_eq_add_one] at hP
  have hsum : m + n - 1 + 1 = m + n := by omega
  rw [hsum] at hP
  have hB : (m + 1).choose 2 = m + m.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
  have hC : (m + 1).choose 3 = m.choose 2 + m.choose 3 :=
    Nat.choose_succ_succ m 2
  have hpos := Nat.choose_pos hm
  omega

private def nonzeroEquiv (m t : ℕ) :
    {s : Model m t // s ≠ 0} ≃ PositiveIndex m t ⊕ DualIndex m t where
  toFun := by
    rintro ⟨s, hs⟩
    cases s with
    | zero => exact False.elim (hs rfl)
    | e a => exact .inl a
    | f b => exact .inr b
  invFun s := s.elim eKey fKey
  left_inv := by rintro ⟨s, hs⟩; cases s <;> first | rfl | exact False.elim (hs rfl)
  right_inv := by intro s; cases s <;> rfl

private theorem card_dual (m t : ℕ) : Fintype.card (DualIndex m t) = (m + t).choose t := by
  calc
    _ = Fintype.card ((k : Fin (t + 1)) × Sym (Fin m) k.val) :=
      Fintype.card_congr (boundedEquiv m t)
    _ = ∑ k : Fin (t + 1), m.multichoose k.val := by
      simp only [Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
    _ = ∑ k ∈ Finset.range (t + 1), m.multichoose k := Fin.sum_univ_eq_sum_range _ _
    _ = (t + m).choose m := Nat.sum_range_multichoose t m
    _ = (m + t).choose t := by
      calc
        _ = (m + t).choose m := by rw [Nat.add_comm]
        _ = _ := Nat.choose_symm_add

private def positiveEquiv (m t : ℕ) : PositiveIndex m t ≃
    {b : DualIndex m t // b.val ≠ 0} where
  toFun a := ⟨⟨a.val, a.property.2⟩, by
    intro h
    have := a.property.1
    exact (Nat.ne_of_gt this) (congrArg Multiset.card h)⟩
  invFun b := ⟨b.val.val, ⟨Multiset.card_pos.mpr b.property, b.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem finrank_ambient {F : Type*} [Field F] (m t : ℕ) :
    Module.finrank F (Ambient F m t) = 2 * (m + t).choose t - 1 := by
  classical
  let ez : {b : DualIndex m t // b.val = 0} ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨⟨0, by simp⟩, rfl⟩
    left_inv := by intro b; apply Subtype.ext; exact Subtype.ext b.property.symm
    right_inv := fun _ => rfl }
  have hz : Fintype.card {b : DualIndex m t // b.val = 0} = 1 := by
    simpa only [Fintype.card_unit] using Fintype.card_congr ez
  have hp : Fintype.card (PositiveIndex m t) = (m + t).choose t - 1 := by
    calc
      _ = Fintype.card {b : DualIndex m t // b.val ≠ 0} :=
        Fintype.card_congr (positiveEquiv m t)
      _ = _ := by rw [Fintype.card_subtype_compl, hz, card_dual]
  change Module.finrank F ({s : Model m t // s ≠ 0} →₀ F) = _
  rw [Module.finrank_finsupp_self]
  have hc := Fintype.card_congr (nonzeroEquiv m t)
  simp only [Fintype.card_sum, hp, card_dual] at hc
  rw [hc]
  omega

private def filtration (F : Type*) [Field F] (m t d : ℕ) : Submodule F (Ambient F m t) :=
  Finsupp.supported F F {s : {s : Model m t // s ≠ 0} | d ≤ labelDegree s.val}

private theorem filtration_mul_le {F : Type*} [Field F] {m t i j : ℕ} :
    Submodule.map₂ (product F (Model m t)) (filtration F m t i) (filtration F m t j) ≤
      filtration F m t (i + j) := by
  classical
  rw [filtration, filtration, Finsupp.supported_eq_span_single,
    Finsupp.supported_eq_span_single, Submodule.map₂_span_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  change Finsupp.single a (1 : F) * Finsupp.single b 1 ∈ _
  rw [single_mul]
  by_cases hab : a.val * b.val = 0
  · simp [hab, delta]
  · simp only [one_mul, one_smul, delta, dif_neg hab]
    apply Finsupp.single_mem_supported F 1
    change i + j ≤ labelDegree (a.val * b.val)
    rw [labelDegree_mul _ _ hab]
    exact Nat.add_le_add ha hb

private theorem ambient_nilpotent {F : Type*} [Field F] (m t : ℕ) :
    mixedPower (product F (Model m t)) ⊤ (t + 1) = ⊥ := by
  classical
  have htop : (⊤ : Submodule F (Ambient F m t)) = filtration F m t 1 := by
    apply le_antisymm _ le_top
    intro x hx
    exact fun s hs => labelDegree_pos s.val s.property
  have hpow (k : ℕ) : mixedPower (product F (Model m t)) ⊤ k ≤ filtration F m t (k + 1) := by
    induction k with
    | zero => exact le_of_eq htop
    | succ k ih =>
      exact (Submodule.map₂_le_map₂ (le_of_eq htop) ih).trans
        (by simpa [Nat.add_comm] using
          (filtration_mul_le (F := F) (m := m) (t := t) (i := 1) (j := k + 1)))
  apply le_antisymm _ bot_le
  intro x hx
  apply Finsupp.ext
  intro a
  have hmem := (Finsupp.mem_supported' F x).mp (hpow _ hx)
  apply hmem a
  change ¬ t + 1 + 1 ≤ labelDegree a.val
  have := labelDegree_le a.val
  omega

private theorem ratio_bound {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n) :
    ((m + n : ℕ) : ℝ) / (2 * (n + 1 : ℕ)) ≤
      ((m + (m + n).choose (n + 1) : ℕ) : ℝ) /
        (((m + n - 1).choose n + (m + 1).choose 2 : ℕ) : ℝ) := by
  have hEB : (m + 1).choose 2 ≤ (m + n - 1).choose n := by
    calc
      _ = (m + 1).choose (m - 1) := Nat.choose_symm_of_eq_add (by omega)
      _ ≤ (m + n - 1).choose (m - 1) := Nat.choose_le_choose _ (by omega)
      _ = _ := Nat.choose_symm_of_eq_add (by omega)
  have hE := Nat.choose_pos (by omega : n ≤ m + n - 1)
  have hA := Nat.add_one_mul_choose_eq (m + n - 1) n
  have hsum : m + n - 1 + 1 = m + n := by omega
  rw [hsum] at hA
  have hAr : ((m + n : ℕ) : ℝ) * ((m + n - 1).choose n : ℝ) =
      ((m + n).choose (n + 1) : ℝ) * (n + 1 : ℕ) := by exact_mod_cast hA
  have hEr : (0 : ℝ) < ((m + n - 1).choose n : ℝ) := by exact_mod_cast hE
  have hEBr : ((m + 1).choose 2 : ℝ) ≤ ((m + n - 1).choose n : ℝ) := by exact_mod_cast hEB
  apply (div_le_div_iff₀ (by positivity) (by exact_mod_cast (by omega :
    0 < (m + n - 1).choose n + (m + 1).choose 2))).mpr
  push_cast at hAr ⊢
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ m + n by positivity) (sub_nonneg.mpr hEBr)]

/-- The ratio uses the actual quotient and actual mixed product space of the model. -/
def dimensionRatio (F : Type*) [Field F] (m n : ℕ) : ℝ :=
  let μ := product F (Model m (n + 1))
  let V := layer F m (n + 1) 1
  let W := mixedPower μ V (n - 1)
  (Module.finrank F (V ⧸ relativeAnnihilator μ V W) : ℝ) / Module.finrank F W

/-- The full nominated family, including finiteness rather than a finrank fallback. -/
def familyProperties (F : Type*) [Field F] (m n : ℕ) : Prop :=
  let R := Ambient F m (n + 1)
  let μ := product F (Model m (n + 1))
  let V := layer F m (n + 1) 1
  let W := mixedPower μ V (n - 1)
  let A := relativeAnnihilator μ V W
  FiniteDimensional F R ∧ FiniteDimensional F W ∧
  W = layer F m (n + 1) n ∧ A = ⊥ ∧
  Module.finrank F R = 2 * (m + n + 1).choose (n + 1) - 1 ∧
  Module.finrank F V = m + (m + n).choose (n + 1) ∧
  Module.finrank F W = (m + n - 1).choose n + (m + 1).choose 2 ∧
  Module.finrank F (V ⧸ A) = m + (m + n).choose (n + 1) ∧
  Module.finrank F (V ⧸ A) - Module.finrank F W =
    (m + n - 1).choose (n + 1) - m.choose 2 ∧
  m.choose 3 ≤ Module.finrank F (V ⧸ A) - Module.finrank F W ∧
  Module.finrank F W < Module.finrank F (V ⧸ A) ∧
  mixedPower μ ⊤ (n + 2) = ⊥ ∧
  ((m + n : ℕ) : ℝ) / (2 * (n + 1 : ℕ)) ≤ dimensionRatio F m n

/-- Every field and every `n≥2` have the full family and unbounded dimension ratios. -/
theorem family (F : Type*) [Field F] (n : ℕ) (hn : 2 ≤ n) :
    (∀ m : ℕ, 3 ≤ m → familyProperties F m n) ∧
    (∀ C : ℝ, ∃ m : ℕ, 3 ≤ m ∧ C < dimensionRatio F m n) := by
  have hratio (m : ℕ) (hm : 3 ≤ m) :
      ((m + n : ℕ) : ℝ) / (2 * (n + 1 : ℕ)) ≤ dimensionRatio F m n := by
    dsimp only [dimensionRatio]
    rw [family_quotient_dimension (F := F) (m := m) (by omega) hn,
      family_power_dimension (F := F) (m := m) (by omega) hn]
    exact ratio_bound hm hn
  constructor
  · intro m hm
    dsimp only [familyProperties]
    have hQ := family_quotient_dimension (F := F) (by omega : 0 < m) hn
    have hW := family_power_dimension (F := F) (by omega : 0 < m) hn
    have hdef := dimension_defect hm hn
    refine ⟨inferInstance, mixedPower_finite _ _ _, family_power (by omega) hn,
      family_annihilator (by omega) hn, ?_, family_v_dimension, hW, hQ, ?_, ?_, ?_, ?_,
      hratio m hm⟩
    · simpa only [Nat.add_assoc] using finrank_ambient (F := F) m (n + 1)
    · rw [hQ, hW]; exact hdef.1
    · rw [hQ, hW, hdef.1]; exact hdef.2.1
    · rw [hQ, hW]; exact hdef.2.2
    · simpa only [Nat.add_assoc] using ambient_nilpotent (F := F) m (n + 1)
  · intro C
    obtain ⟨m, hm⟩ := exists_nat_gt (max 3 (2 * (n + 1 : ℕ) * C))
    have hm3 : 3 ≤ m := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hm).le
    have hmC : 2 * (n + 1 : ℕ) * C < (m : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hm
    refine ⟨m, hm3, lt_of_lt_of_le ?_ (hratio m hm3)⟩
    apply (lt_div_iff₀ (by positivity)).mpr
    push_cast
    push_cast at hmC
    nlinarith

/-- The literal closed negation of the complete universal Question 23. -/
theorem result : ¬ claim := by
  intro H
  have hf := (family ℚ 2 (by decide)).1 3 (by decide)
  rcases hf with ⟨hR, hW, hpower, hann, hdimR, hdimV, hdimW, hdimQ,
    hdef, hlower, hstrict, hnil, hratio⟩
  have h := H ℚ (Ambient ℚ 3 3) (product ℚ (Model 3 3))
    (by intro x y z; exact mul_assoc x y z)
    (by intro x y; exact mul_comm x y)
    (layer ℚ 3 3 1) inferInstance 1
  exact (Nat.not_le_of_lt hstrict) h

end D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
