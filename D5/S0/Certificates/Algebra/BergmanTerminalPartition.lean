/- GID: D5/S0/Certificates/Algebra/BergmanTerminalPartition
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanTerminalPartition
   mirror-E: none(waiver:noncomputational)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Two terminal classes realize signed binomial partitions as actual semigroups. -/

import D5.S0.Certificates.Algebra.BergmanCyclicGrading
import Mathlib.Data.Nat.Choose.Sum

/-! # Two-terminal binomial partitions -/

noncomputable section
namespace D5.S0.Certificates.Algebra.BergmanTerminalPartition
open BergmanQuestion23Refutation (Monomial PositiveIndex DualIndex mixedPower)
open BergmanQuestion15Refutation (Contracted delta positivePower product)
open BergmanContractedAlgebra
open BergmanCyclicGrading (positiveProduct)
open private delta_power algebra_nilpotent from
  D5.S0.Certificates.Algebra.BergmanCyclicGrading
open scoped BigOperators IsMulCommutative

abbrev Exponent := Monomial 2
abbrev Lower (n : ℕ) := PositiveIndex 2 (n - 1)

/-- Distinct lower monomials, two distinct nonzero terminal classes, and zero. -/
inductive Model (n : ℕ) (I : Finset ℕ) where
  | zero
  | lower (a : Lower n)
  | terminal (b : Bool)
  deriving DecidableEq, Fintype
instance {n I} : Zero (Model n I) := ⟨.zero⟩

/-- The terminal label records membership of the y-exponent in I. -/
def normal (n : ℕ) (I : Finset ℕ) (a : Exponent) : Model n I :=
  if h : 0 < a.card ∧ a.card < n then .lower ⟨a, h.1, by omega⟩
  else if a.card = n ∧ 0 < n then .terminal (decide (a.count 1 ∈ I)) else 0

def modelMul {n I} : Model n I → Model n I → Model n I
  | .lower a, .lower b => normal n I (a.val + b.val)
  | _, _ => 0
instance {n I} : Mul (Model n I) := ⟨modelMul⟩
private theorem zero_mul_model {n I} (s : Model n I) : (0 : Model n I) * s = 0 := by
  cases s <;> rfl
private theorem mul_zero_model {n I} (s : Model n I) : s * (0 : Model n I) = 0 := by
  cases s <;> rfl
private theorem mul_comm_model {n I} (s t : Model n I) : s * t = t * s := by
  cases s <;> cases t <;> simp [HMul.hMul, Mul.mul, modelMul, add_comm]
private theorem normal_lower {n I} (a : Lower n) : normal n I a.val = .lower a := by
  simp [normal, a.property.1, show a.val.card < n by have := a.property.2; omega]
private theorem normal_large {n I} (a : Exponent) (h : n < a.card) : normal n I a = 0 := by
  simp [normal, show ¬ a.card < n by omega, show a.card ≠ n by omega]
private theorem normal_mul {n I} (a b : Exponent) (ha : 0 < a.card) (hb : 0 < b.card) :
    normal n I a * normal n I b = normal n I (a + b) := by
  by_cases hA : a.card < n
  · by_cases hB : b.card < n
    · simp [normal, ha, hb, hA, hB, HMul.hMul, Mul.mul, modelMul]
    · rw [normal_large (a + b) (by simp only [Multiset.card_add]; omega)]
      have ea : normal n I a = .lower ⟨a, ha, by omega⟩ := by simp [normal, ha, hA]
      rw [ea]
      unfold normal
      split
      · rename_i h; omega
      · split <;> rfl
  · rw [normal_large (a + b) (by simp only [Multiset.card_add]; omega)]
    unfold normal
    split
    · rename_i h; omega
    · split <;> rfl
private theorem normal_mul_lower {n I} (a : Exponent) (ha : 0 < a.card) (b : Lower n) :
    normal n I a * .lower b = normal n I (a + b.val) := by
  rw [← normal_lower b]
  exact normal_mul a b.val ha b.property.1
instance modelSemigroup {n I} : SemigroupWithZero (Model n I) where
  mul_assoc a b c := by
    cases a with
    | zero => cases b <;> cases c <;> rfl
    | terminal i => cases b <;> cases c <;> rfl
    | lower a =>
      cases b with
      | zero => cases c <;> rfl
      | terminal i => cases c <;> rfl
      | lower b =>
        cases c with
        | zero => exact mul_zero_model _
        | terminal i =>
          change normal n I (a.val + b.val) * .terminal i = 0
          generalize normal n I (a.val + b.val) = x
          cases x <;> rfl
        | lower c =>
          change normal n I (a.val + b.val) * .lower c =
            .lower a * normal n I (b.val + c.val)
          rw [normal_mul_lower _ (by simp; have := a.property.1; omega),
            mul_comm_model, normal_mul_lower _ (by simp; have := b.property.1; omega)]
          congr 1
          ac_rfl
  zero_mul := zero_mul_model
  mul_zero := mul_zero_model
instance modelCommutative {n I} : IsMulCommutative (Model n I) := ⟨⟨mul_comm_model⟩⟩

/-- The actual degree-one generators x and y. -/
def generator (n : ℕ) (I : Finset ℕ) (i : Fin 2) : Model n I := normal n I {i}
private theorem generator_power (n : ℕ) (I : Finset ℕ) (i : Fin 2) (k : ℕ) :
    positivePower (generator n I i) k = normal n I (Multiset.replicate (k + 1) i) := by
  induction k with
  | zero => simp [positivePower, generator]
  | succ k ih =>
    rw [positivePower, ih]
    change normal n I (Multiset.replicate (k + 1) i) * normal n I {i} = _
    rw [normal_mul _ _ (by simp) (by simp)]
    congr 1
    simpa using (Multiset.replicate_add (k + 1) 1 i).symm
private theorem terminal_powers (n : ℕ) (hn : 0 < n) (I : Finset ℕ)
    (h0 : 0 ∈ I) (hN : n ∉ I) :
    positivePower (generator n I 0) (n - 1) = .terminal true ∧
    positivePower (generator n I 1) (n - 1) = .terminal false := by
  simp [generator_power, Nat.sub_add_cancel hn, normal, hn, h0, hN, Multiset.count_replicate]
private theorem generated (n : ℕ) (hn : 0 < n) (I : Finset ℕ)
    (h0 : 0 ∈ I) (hN : n ∉ I) :
    Subsemigroup.closure (Set.range (generator n I)) = ⊤ := by
  have surj (s : Model n I) : ∃ a : Exponent, 0 < a.card ∧ normal n I a = s := by
    cases s with
    | zero => exact ⟨Multiset.replicate (n + 1) 0, by simp, normal_large _ (by simp)⟩
    | lower a => exact ⟨a.val, a.property.1, normal_lower a⟩
    | terminal b =>
      cases b
      · exact ⟨Multiset.replicate n 1, by simpa, by
          simpa [generator_power, Nat.sub_add_cancel hn] using (terminal_powers n hn I h0 hN).2⟩
      · exact ⟨Multiset.replicate n 0, by simpa, by
          simpa [generator_power, Nat.sub_add_cancel hn] using (terminal_powers n hn I h0 hN).1⟩
  apply top_unique
  intro s _
  obtain ⟨a, ha, rfl⟩ := surj s
  induction a using Multiset.induction_on with
  | empty => simp at ha
  | @cons i a ih =>
    by_cases he : a = 0
    · subst a; exact Subsemigroup.subset_closure ⟨i, rfl⟩
    · have hp := Multiset.card_pos.mpr he
      rw [show i ::ₘ a = {i} + a by rfl, ← normal_mul _ _ (by simp) hp]
      exact Subsemigroup.mul_mem _ (Subsemigroup.subset_closure ⟨i, rfl⟩) (ih hp trivial)

private def degree {n I} : Model n I → ℕ
  | .zero => 0
  | .lower a => a.val.card
  | .terminal _ => n

private theorem degree_le {n I} (s : Model n I) : degree s ≤ n := by
  cases s with
  | zero => exact Nat.zero_le _
  | terminal i => exact le_rfl
  | lower a => have := a.property.2; simp only [degree]; omega

private theorem degree_pos {n I} (hn : 0 < n) (s : Model n I) (hs : s ≠ 0) :
    0 < degree s := by
  cases s with
  | zero => exact False.elim (hs rfl)
  | lower a => exact a.property.1
  | terminal i => exact hn

private theorem degree_normal {n I} (a : Exponent) (h : normal n I a ≠ 0) :
    degree (normal n I a) = a.card := by
  unfold normal at h ⊢
  split_ifs at h ⊢ with hA hB
  · rfl
  · simp_all [degree]
  · exact False.elim (h rfl)

private theorem degree_mul {n I} (s t : Model n I) (h : s * t ≠ 0) :
    degree (s * t) = degree s + degree t := by
  cases s <;> cases t <;> try exact False.elim (h rfl)
  rename_i a b
  exact (degree_normal _ h).trans (Multiset.card_add _ _)

private theorem product_degree {n I} (hn : 0 < n) (k : ℕ)
    (a : Fin (k + 1) → Model n I) (h : positiveProduct k a ≠ 0) :
    k + 1 ≤ degree (positiveProduct k a) := by
  induction k with
  | zero => exact degree_pos hn _ h
  | succ k ih =>
    change a 0 * positiveProduct k (fun i => a i.succ) ≠ 0 at h
    rw [positiveProduct, degree_mul _ _ h]
    have h₁ : a 0 ≠ 0 := fun he => h (by rw [he, zero_mul])
    have h₂ : positiveProduct k (fun i => a i.succ) ≠ 0 :=
      fun he => h (by rw [he, mul_zero])
    have := degree_pos hn _ h₁
    have := ih (fun i => a i.succ) h₂
    omega

private theorem nilpotency (F : Type*) [Field F] (n : ℕ) (hn : 0 < n) (I : Finset ℕ)
    (h0 : 0 ∈ I) (hN : n ∉ I) :
    (∀ a : Fin (n + 1) → Model n I, positiveProduct n a = 0) ∧
    mixedPower (product F (Model n I)) ⊤ n = ⊥ ∧
    (∀ a : Fin (n + 1) → Contracted F (Model n I), positiveProduct n a = 0) ∧
    positivePower (delta F (Model n I) (generator n I 0)) (n - 1) ≠ 0 := by
  have hzero : ∀ a : Fin (n + 1) → Model n I, positiveProduct n a = 0 := by
    intro a
    by_contra h
    have := product_degree hn n a h
    have := degree_le (positiveProduct n a)
    omega
  have halg := algebra_nilpotent (F := F) n hzero
  refine ⟨hzero, halg.1, halg.2, ?_⟩
  classical
  rw [delta_power, (terminal_powers n hn I h0 hN).1]
  simp [delta, show (Model.terminal true : Model n I) ≠ 0 by intro h; cases h]

open private card_dual positiveEquiv from
  D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
private def modelEquiv (n : ℕ) (I : Finset ℕ) : Model n I ≃ Option (Lower n ⊕ Bool) where
  toFun s := match s with
    | .zero => none
    | .lower a => some (.inl a)
    | .terminal i => some (.inr i)
  invFun s := match s with
    | none => .zero
    | some (.inl a) => .lower a
    | some (.inr i) => .terminal i
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s with
    | none => rfl
    | some s => cases s <;> rfl

private theorem cardinalities (F : Type*) [Field F] (n : ℕ) (hn : 2 ≤ n) (I : Finset ℕ) :
    Fintype.card (Model n I) = n * (n + 1) / 2 + 2 ∧
    Module.finrank F (Contracted F (Model n I)) = n * (n + 1) / 2 + 1 := by
  classical
  let ez : {b : DualIndex 2 (n - 1) // b.val = 0} ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨⟨0, by simp⟩, rfl⟩
    left_inv := by intro b; apply Subtype.ext; exact Subtype.ext b.property.symm
    right_inv := fun _ => rfl }
  have hz : Fintype.card {b : DualIndex 2 (n - 1) // b.val = 0} = 1 := by
    simpa using Fintype.card_congr ez
  have hp : Fintype.card (Lower n) = (n + 1).choose 2 - 1 := by
    rw [Fintype.card_congr (positiveEquiv 2 (n - 1)), Fintype.card_subtype_compl, hz,
      card_dual, Nat.choose_symm_of_eq_add (show 2 + (n - 1) = (n - 1) + 2 by omega)]
    congr 2; omega
  have hc : Fintype.card (Model n I) = n * (n + 1) / 2 + 2 := by
    rw [Fintype.card_congr (modelEquiv n I)]
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_bool, hp]
    have hpos := Nat.choose_pos (show 2 ≤ n + 1 by omega)
    have hchoose : (n + 1).choose 2 = n * (n + 1) / 2 := by
      rw [Nat.choose_two_right]
      simp [Nat.mul_comm]
    rw [hchoose] at hpos ⊢
    omega
  refine ⟨hc, ?_⟩
  change Module.finrank F ({s : Model n I // s ≠ 0} →₀ F) = _
  rw [Module.finrank_finsupp_self, Fintype.card_subtype_compl, Fintype.card_subtype_eq, hc]
  omega



private abbrev Positive := {a : Exponent // 0 < a.card}
/-- Free nonempty commutative words with an absorbing zero. -/
inductive Word where
  | zero
  | monomial (a : Positive)
  deriving DecidableEq
instance : Zero Word := ⟨.zero⟩
private def wordMul : Word → Word → Word
  | .monomial a, .monomial b => .monomial ⟨a.val + b.val, by
      simp only [Multiset.card_add]; have := a.property; omega⟩
  | _, _ => 0
instance : Mul Word := ⟨wordMul⟩
instance : SemigroupWithZero Word where
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> try rfl
    simp only [HMul.hMul, Mul.mul, wordMul, add_assoc]
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
private def reduce (n : ℕ) (I : Finset ℕ) : Word → Model n I
  | .zero => 0
  | .monomial a => normal n I a.val
private theorem reduce_mul (n : ℕ) (I : Finset ℕ) (s t : Word) :
    reduce n I (s * t) = reduce n I s * reduce n I t := by
  cases s with
  | zero => change 0 = 0 * reduce n I t; rw [zero_mul]
  | monomial a =>
    cases t with
    | zero => change 0 = normal n I a.val * 0; rw [mul_zero]
    | monomial b => exact (normal_mul a.val b.val a.property b.property).symm

/-- Only the specified degree-n identifications and degree-(n+1) truncations. -/
inductive Relations (n : ℕ) (I : Finset ℕ) : Word → Word → Prop
  | terminal (a b : Positive) (ha : a.val.card = n) (hb : b.val.card = n)
      (label : (a.val.count 1 ∈ I) ↔ (b.val.count 1 ∈ I)) :
      Relations n I (.monomial a) (.monomial b)
  | truncation (a : Positive) (degree : a.val.card = n + 1) :
      Relations n I (.monomial a) 0
/-- Congruence generated by the two terminal lists and truncation. -/
def presentation (n : ℕ) (I : Finset ℕ) : Con Word := conGen (Relations n I)
private theorem relation_sound (n : ℕ) (hn : 0 < n) (I : Finset ℕ) {s t : Word}
    (h : Relations n I s t) : reduce n I s = reduce n I t := by
  cases h with
  | terminal a b ha hb hl => simp [reduce, normal, ha, hb, hn, hl]
  | truncation a hd => simp [reduce, normal, hd]
private theorem presentation_sound (n : ℕ) (hn : 0 < n) (I : Finset ℕ) {s t : Word}
    (h : presentation n I s t) : reduce n I s = reduce n I t := by
  induction h with
  | of s t h => exact relation_sound n hn I h
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | mul h₁ h₂ ih₁ ih₂ => simp only [reduce_mul, ih₁, ih₂]
private theorem large_zero (n : ℕ) (I : Finset ℕ) (a : Exponent)
    (ha : 0 < a.card) (hd : n < a.card) :
    presentation n I (.monomial ⟨a, ha⟩) 0 := by
  induction a using Multiset.induction_on with
  | empty => simp at ha
  | @cons i a ih =>
    by_cases ht : n < a.card
    · have hp : 0 < a.card := by omega
      exact ConGen.Rel.mul
        (ConGen.Rel.refl (r := Relations n I) (Word.monomial ⟨{i}, by simp⟩)) (ih hp ht)
    · apply ConGen.Rel.of
      exact Relations.truncation _ (by simp only [Multiset.card_cons] at hd ⊢; omega)
private def representative (n : ℕ) (hn : 0 < n) {I} : Model n I → Word
  | .zero => 0
  | .lower a => .monomial ⟨a.val, a.property.1⟩
  | .terminal b => .monomial ⟨Multiset.replicate n (if b then 0 else 1), by simpa⟩
private theorem word_reduces (n : ℕ) (hn : 0 < n) (I : Finset ℕ)
    (h0 : 0 ∈ I) (hN : n ∉ I) (s : Word) :
    presentation n I s (representative n hn (reduce n I s)) := by
  cases s with
  | zero => exact ConGen.Rel.refl _
  | monomial a =>
    change presentation n I (.monomial a) (representative n hn (normal n I a.val))
    by_cases hd : a.val.card < n
    · unfold normal
      rw [dif_pos ⟨a.property, hd⟩]
      exact ConGen.Rel.refl _
    · by_cases he : a.val.card = n
      · rw [show normal n I a.val = .terminal (decide (a.val.count 1 ∈ I)) by
          simp [normal, he, hn]]
        apply ConGen.Rel.of
        apply Relations.terminal _ _ he (by simp [representative])
        by_cases hm : a.val.count 1 ∈ I <;>
          simp [representative, hm, h0, hN, Multiset.count_replicate]
      · rw [normal_large _ (by omega)]
        exact large_zero n I a.val a.property (by omega)

/-- Actual normal-form equality is precisely derivability from the written relations. -/
theorem normal_form_complete (n : ℕ) (hn : 0 < n) (I : Finset ℕ)
    (h0 : 0 ∈ I) (hN : n ∉ I) (s t : Word) :
    presentation n I s t ↔ reduce n I s = reduce n I t := by
  constructor
  · exact presentation_sound n hn I
  · intro h
    exact ConGen.Rel.trans (word_reduces n hn I h0 hN s)
      (h ▸ ConGen.Rel.symm (word_reduces n hn I h0 hN t))

/-- Integral signed binomial coefficient sum, independent of the field. -/
def signedSum (n : ℕ) (I : Finset ℕ) : ℤ := ∑ j ∈ I, (-1 : ℤ) ^ j * n.choose j

variable {F : Type*} [Field F]
private abbrev Algebra (F : Type*) [Field F] (n : ℕ) (I : Finset ℕ) :=
  Contracted F (Model n I)
private def unitTerm (n : ℕ) (I : Finset ℕ) (a : Exponent) : Unitization F (Algebra F n I) :=
  if a = 0 then 1 else Unitization.inr (delta F (Model n I) (normal n I a))
private theorem unitTerm_mul (n : ℕ) (I : Finset ℕ) (a b : Exponent) :
    unitTerm (F := F) n I a * unitTerm n I b = unitTerm n I (a + b) := by
  by_cases ha : a = 0
  · subst a; simp [unitTerm]
  by_cases hb : b = 0
  · subst b; simp [unitTerm]
  have hab : a + b ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    have := Multiset.card_pos.mpr ha
    simp only [Multiset.card_add, Multiset.card_zero] at *
    omega
  simp only [unitTerm, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab, ← Unitization.inr_mul,
    delta_mul, normal_mul a b (Multiset.card_pos.mpr ha) (Multiset.card_pos.mpr hb)]
private theorem unit_generator_power (n : ℕ) (I : Finset ℕ) (i : Fin 2) (k : ℕ) :
    (Unitization.inr (delta F (Model n I) (generator n I i)) : Unitization F (Algebra F n I)) ^ k =
      unitTerm n I (Multiset.replicate k i) := by
  induction k with
  | zero => simp [unitTerm]
  | succ k ih =>
    rw [pow_succ, ih]
    have hg : (Unitization.inr (delta F (Model n I) (generator n I i)) :
        Unitization F (Algebra F n I)) = unitTerm n I {i} := by simp [unitTerm, generator]
    rw [hg, unitTerm_mul]
    congr 1
    simpa using (Multiset.replicate_add k 1 i).symm
private theorem inr_positivePower (n : ℕ) (I : Finset ℕ) (v : Algebra F n I) (k : ℕ) :
    (Unitization.inr (positivePower v k) : Unitization F (Algebra F n I)) =
      (Unitization.inr v) ^ (k + 1) := by
  induction k with
  | zero => simp [positivePower]
  | succ k ih => rw [positivePower, Unitization.inr_mul, ih]; exact (pow_succ _ _).symm
private theorem power_expansion (n : ℕ) (hn : 0 < n) (I : Finset ℕ) :
    positivePower (delta F (Model n I) (generator n I 0) -
      delta F (Model n I) (generator n I 1)) (n - 1) =
    ∑ j ∈ Finset.range (n + 1), ((-1 : F) ^ j * n.choose j) •
      delta F (Model n I) (normal n I
        (Multiset.replicate (n - j) 0 + Multiset.replicate j 1)) := by
  apply Unitization.inr_injective (R := F)
  rw [inr_positivePower, Nat.sub_add_cancel hn, Unitization.inr_sub]
  rw [show (Unitization.inr (delta F (Model n I) (generator n I 0)) -
      Unitization.inr (delta F (Model n I) (generator n I 1)) : Unitization F (Algebra F n I)) =
      -Unitization.inr (delta F (Model n I) (generator n I 1)) +
       Unitization.inr (delta F (Model n I) (generator n I 0)) by abel, add_pow]
  change _ = (Unitization.inrHom F F (Algebra F n I)) _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  have hcard : (Multiset.replicate (n - j) (0 : Fin 2) + Multiset.replicate j 1).card = n := by
    simp; omega
  have hne : Multiset.replicate (n - j) (0 : Fin 2) + Multiset.replicate j 1 ≠ 0 := by
    intro h; have := congrArg Multiset.card h; simp [hcard] at this; omega
  rw [show (-Unitization.inr (delta F (Model n I) (generator n I 1)) :
      Unitization F (Algebra F n I)) = (-1 : F) • Unitization.inr
        (delta F (Model n I) (generator n I 1)) by simp,
    smul_pow, unit_generator_power, unit_generator_power]
  rw [smul_mul_assoc, unitTerm_mul, add_comm (Multiset.replicate j 1)]
  simp only [unitTerm, ite_eq_right hne]
  rw [show (n.choose j : Unitization F (Algebra F n I)) = (n.choose j : F) • 1 by
      rw [Algebra.smul_def, mul_one, map_natCast],
    mul_smul_comm, mul_one, smul_smul, ← Unitization.inr_smul]
  congr 2
  ring

private theorem terminal_coefficients (n : ℕ) (hn : 0 < n) (I : Finset ℕ) :
    positivePower (delta F (Model n I) (generator n I 0) -
      delta F (Model n I) (generator n I 1)) (n - 1) =
      (signedSum n I : F) • delta F (Model n I) (.terminal true) -
      (signedSum n I : F) • delta F (Model n I) (.terminal false) := by
  classical
  rw [power_expansion n hn]
  have hn0 : n ≠ 0 := by omega
  have htot : (∑ j ∈ Finset.range (n + 1), (-1 : F) ^ j * n.choose j) = 0 := by
    have h := congrArg (Int.castRingHom F) (Int.alternating_sum_range_choose_of_ne hn0)
    simpa using h
  have hI : (∑ j ∈ Finset.range (n + 1) with j ∈ I, (-1 : F) ^ j * n.choose j) =
      (signedSum n I : F) := by
    simp only [signedSum, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast]
    apply Finset.sum_subset (by intro j hj; exact (Finset.mem_filter.mp hj).2)
    intro j hj hnot
    have hjn : n < j := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj⟩)
    simp [Nat.choose_eq_zero_of_lt hjn]
  have hs (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      normal n I (Multiset.replicate (n - j) 0 + Multiset.replicate j 1) =
        .terminal (decide (j ∈ I)) := by
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    have hd : (Multiset.replicate (n - j) (0 : Fin 2) + Multiset.replicate j 1).card = n := by
      simp; omega
    simp [normal, hd, hn, Multiset.count_replicate]
  rw [Finset.sum_congr rfl (fun j hj => by rw [hs j hj])]
  have hsplit (j : ℕ) :
      ((-1 : F) ^ j * n.choose j) • delta F (Model n I) (.terminal (decide (j ∈ I))) =
      (if j ∈ I then (-1 : F) ^ j * n.choose j else 0) • delta F (Model n I) (.terminal true) +
      (((-1 : F) ^ j * n.choose j) - (if j ∈ I then (-1 : F) ^ j * n.choose j else 0)) •
        delta F (Model n I) (.terminal false) := by
    split_ifs <;> simp_all
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
    Finset.sum_sub_distrib, ← Finset.sum_filter, hI, htot]
  simp [neg_smul, sub_eq_add_neg]


/-- The actual contracted x-y, with semigroup zero mapped to the zero vector. -/
def difference (F : Type*) [Field F] (n : ℕ) (I : Finset ℕ) : Contracted F (Model n I) :=
  delta F (Model n I) (generator n I 0) - delta F (Model n I) (generator n I 1)

/-- Every signed-binomial-zero partition realizes the full two-generator family.
The identities hold over every field; in particular over all characteristic-zero fields. -/
theorem partition_family (F : Type*) [Field F] (I : Finset ℕ) (n : ℕ) (hn : 2 ≤ n)
    (h0 : 0 ∈ I) (hN : n ∉ I) (hsum : signedSum n I = 0) :
    Fintype.card (Model n I) = n * (n + 1) / 2 + 2 ∧
    Module.finrank F (Contracted F (Model n I)) = n * (n + 1) / 2 + 1 ∧
    Subsemigroup.closure (Set.range (generator n I)) = ⊤ ∧
    positivePower (generator n I 0) (n - 1) ≠ 0 ∧
    positivePower (generator n I 1) (n - 1) ≠ 0 ∧
    positivePower (generator n I 0) (n - 1) ≠ positivePower (generator n I 1) (n - 1) ∧
    difference F n I ≠ 0 ∧
    difference F n I ∈ Submodule.span F
      (Set.range (fun i => delta F (Model n I) (generator n I i))) ∧
    positivePower (difference F n I) (n - 1) = 0 ∧
    (∀ a : Fin (n + 1) → Model n I, positiveProduct n a = 0) ∧
    mixedPower (product F (Model n I)) ⊤ n = ⊥ ∧
    (∀ a : Fin (n + 1) → Contracted F (Model n I), positiveProduct n a = 0) ∧
    positivePower (delta F (Model n I) (generator n I 0)) (n - 1) ≠ 0 := by
  classical
  have hp := terminal_powers n (by omega) I h0 hN
  have hc := cardinalities F n hn I
  have hnil := nilpotency F n (by omega) I h0 hN
  have hg (i : Fin 2) : generator n I i ≠ 0 := by
    simp [generator, normal, show 1 < n by omega]
  have hxy : generator n I 0 ≠ generator n I 1 := by
    simp [generator, normal, show 1 < n by omega]
  refine ⟨hc.1, hc.2, generated n (by omega) I h0 hN, ?_, ?_, ?_, ?_, ?_, ?_,
    hnil.1, hnil.2.1, hnil.2.2.1, hnil.2.2.2⟩
  · rw [hp.1]; intro h; cases h
  · rw [hp.2]; intro h; cases h
  · rw [hp.1, hp.2]; intro h; cases h
  · intro hz
    have h := congrArg (fun v : Contracted F (Model n I) => v ⟨generator n I 0, hg 0⟩) hz
    simp [difference, delta, hg, hxy] at h
  · exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩)
      (Submodule.subset_span ⟨1, rfl⟩)
  · simpa [difference, hsum] using (terminal_coefficients (F := F) n (by omega) I)

end D5.S0.Certificates.Algebra.BergmanTerminalPartition
