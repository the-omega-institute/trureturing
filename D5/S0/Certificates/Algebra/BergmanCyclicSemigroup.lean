/- GID: D5/S0/Certificates/Algebra/BergmanCyclicSemigroup
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanCyclicSemigroup
   mirror-E: none(waiver:noncomputational)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Subsemigroup.Basic, mathlib/module/Mathlib.GroupTheory.Congruence.Defs]
   utility: none
   digest: Cyclic terminal monomials and their xyz-zero quotient have complete normal forms. -/

import D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.GroupTheory.Congruence.Defs

/-! # Cyclic terminal monomial semigroups -/

noncomputable section

namespace D5.S0.Certificates.Algebra.BergmanCyclicSemigroup

open BergmanQuestion23Refutation (Monomial PositiveIndex)
open BergmanQuestion15Refutation (positivePower)
open scoped IsMulCommutative

abbrev Exponent := Monomial 3

/-- All three generators occur. -/
def mixed (a : Exponent) : Prop := 0 ∈ a ∧ 1 ∈ a ∧ 2 ∈ a

instance (a : Exponent) : Decidable (mixed a) := by unfold mixed; infer_instance

/-- The optional additional relation kills precisely multiples of xyz. -/
def survives (q : Bool) (a : Exponent) : Prop := q = false ∨ ¬ mixed a

instance (q : Bool) (a : Exponent) : Decidable (survives q a) := by
  unfold survives; infer_instance

abbrev Lower (n : ℕ) (q : Bool) := {a : PositiveIndex 3 (n - 1) // survives q a.val}

/-- Zero, the distinct surviving lower monomials, and three distinct terminal classes. -/
inductive Model (n : ℕ) (q : Bool) where
  | zero
  | lower (a : Lower n q)
  | terminal (i : Fin 3)
  deriving DecidableEq, Fintype

instance {n q} : Zero (Model n q) := ⟨.zero⟩

/-- The cyclic lists are x-positive xy, y-positive yz, and z-positive zx. -/
def terminalLabel (a : Exponent) : Option (Fin 3) :=
  if 2 ∉ a ∧ 0 ∈ a then some 0 else
  if 0 ∉ a ∧ 1 ∈ a then some 1 else
  if 1 ∉ a ∧ 2 ∈ a then some 2 else none

/-- Reduce a monomial. The empty monomial is excluded: there is no identity. -/
def normal (n : ℕ) (q : Bool) (a : Exponent) : Model n q :=
  if h : 0 < a.card ∧ a.card < n ∧ survives q a then
    .lower ⟨⟨a, h.1, by omega⟩, h.2.2⟩
  else if a.card = n ∧ 0 < n then
    match terminalLabel a with
    | some i => .terminal i
    | none => 0
  else 0

/-- Only two lower monomials can have a nonzero product. -/
def modelMul {n q} : Model n q → Model n q → Model n q
  | .lower a, .lower b => normal n q (a.val.val + b.val.val)
  | _, _ => 0

instance {n q} : Mul (Model n q) := ⟨modelMul⟩

private theorem zero_mul_model {n q} (s : Model n q) : (0 : Model n q) * s = 0 := by
  cases s <;> rfl

private theorem mul_zero_model {n q} (s : Model n q) : s * (0 : Model n q) = 0 := by
  cases s <;> rfl

private theorem mul_comm_model {n q} (s t : Model n q) : s * t = t * s := by
  cases s <;> cases t <;> simp [HMul.hMul, Mul.mul, modelMul, add_comm]

private theorem mixed_add_left {a b : Exponent} (h : mixed a) : mixed (a + b) := by
  exact ⟨Multiset.mem_add.mpr (Or.inl h.1),
    Multiset.mem_add.mpr (Or.inl h.2.1), Multiset.mem_add.mpr (Or.inl h.2.2)⟩

private theorem mixed_label {a : Exponent} (h : mixed a) : terminalLabel a = none := by
  simp [terminalLabel, h.1, h.2.1, h.2.2]

private theorem normal_of_large {n q} (a : Exponent) (h : n < a.card) :
    normal n q a = 0 := by
  simp [normal, show ¬ a.card < n by omega, show a.card ≠ n by omega]

private theorem normal_of_mixed {n} (a : Exponent) (h : mixed a) :
    normal n true a = 0 := by
  simp [normal, survives, h, mixed_label h]

private theorem normal_lower {n q} (a : Lower n q) : normal n q a.val.val = .lower a := by
  have h := a.val.property
  have hs := a.property
  simp [normal, h.1, show a.val.val.card < n by omega, hs]

/-- Reduction respects multiplication for every pair of positive monomials. -/
theorem normal_mul {n q} (a b : Exponent) (ha : 0 < a.card) (hb : 0 < b.card) :
    normal n q a * normal n q b = normal n q (a + b) := by
  by_cases hA : a.card < n ∧ survives q a
  · by_cases hB : b.card < n ∧ survives q b
    · simp [normal, ha, hb, hA.1, hA.2, hB.1, hB.2,
        HMul.hMul, Mul.mul, modelMul]
    · by_cases hbN : b.card < n
      · have hbad : ¬ survives q b := fun hs => hB ⟨hbN, hs⟩
        have hq : q = true := by cases q <;> simp_all [survives]
        subst q
        have hm : mixed b := by simpa [survives] using hbad
        have hab : mixed (a + b) := by simpa [add_comm] using mixed_add_left (b := a) hm
        rw [normal_of_mixed b hm, mul_zero_model, normal_of_mixed (a + b) hab]
      · have hab : n < (a + b).card := by simp only [Multiset.card_add]; omega
        rw [normal_of_large (a + b) hab]
        have ea : normal n q a =
            .lower ⟨⟨a, ha, by omega⟩, hA.2⟩ := by
          simp [normal, ha, hA.1, hA.2]
        rw [ea]
        unfold normal
        split
        · rename_i h; omega
        · split
          · split <;> rfl
          · rfl
  · by_cases haN : a.card < n
    · have hbad : ¬ survives q a := fun hs => hA ⟨haN, hs⟩
      have hq : q = true := by cases q <;> simp_all [survives]
      subst q
      have hm : mixed a := by simpa [survives] using hbad
      rw [normal_of_mixed a hm, zero_mul_model,
        normal_of_mixed (a + b) (mixed_add_left hm)]
    · have hab : n < (a + b).card := by simp only [Multiset.card_add]; omega
      rw [normal_of_large (a + b) hab]
      unfold normal
      split <;> rename_i h
      · simp only [Multiset.card_add] at *; omega
      · split <;> split <;> rfl

private theorem normal_mul_lower {n q} (a : Exponent) (ha : 0 < a.card)
    (b : Lower n q) : normal n q a * .lower b = normal n q (a + b.val.val) := by
  rw [← normal_lower b]
  exact normal_mul a b.val.val ha b.val.property.1

/-- Associativity follows from the same reduction of the sum of three monomials. -/
instance modelSemigroup {n q} : SemigroupWithZero (Model n q) where
  mul_assoc a b c := by
    cases a with
    | zero => cases b <;> cases c <;> rfl
    | terminal i => cases b <;> cases c <;> rfl
    | lower a =>
      cases b with
      | zero => cases c <;> rfl
      | terminal i =>
        cases c <;> rfl
      | lower b =>
        cases c with
        | zero =>
          change normal n q (a.val.val + b.val.val) * 0 = 0
          exact mul_zero_model _
        | terminal i =>
          change normal n q (a.val.val + b.val.val) * .terminal i = 0
          generalize normal n q (a.val.val + b.val.val) = x
          cases x <;> rfl
        | lower c =>
          change normal n q (a.val.val + b.val.val) * .lower c =
            .lower a * normal n q (b.val.val + c.val.val)
          rw [normal_mul_lower _ (by simp; have := a.val.property.1; omega),
            mul_comm_model, normal_mul_lower _ (by simp; have := b.val.property.1; omega)]
          congr 1
          ac_rfl
  zero_mul := zero_mul_model
  mul_zero := mul_zero_model

instance modelCommutative {n q} : IsMulCommutative (Model n q) := ⟨⟨mul_comm_model⟩⟩

/-- The three degree-one generators. -/
def generator (n : ℕ) (q : Bool) (i : Fin 3) : Model n q := normal n q {i}

private theorem pure_label (n : ℕ) (hn : 0 < n) (i : Fin 3) :
    terminalLabel (Multiset.replicate n i) = some i := by
  fin_cases i <;> simp [terminalLabel, Multiset.mem_replicate, Nat.ne_of_gt hn]

private theorem normal_pure_terminal (n : ℕ) (hn : 0 < n) (q : Bool) (i : Fin 3) :
    normal n q (Multiset.replicate n i) = .terminal i := by
  simp [normal, pure_label n hn i, hn]

/-- All positive generator powers are reductions of their actual pure monomials. -/
theorem generator_power (n : ℕ) (q : Bool) (i : Fin 3) (k : ℕ) :
    positivePower (generator n q i) k = normal n q (Multiset.replicate (k + 1) i) := by
  induction k with
  | zero => simp [positivePower, generator]
  | succ k ih =>
    rw [positivePower, ih]
    change normal n q (Multiset.replicate (k + 1) i) * normal n q {i} = _
    rw [normal_mul _ _ (by simp) (by simp)]
    congr 1
    simpa using (Multiset.replicate_add (k + 1) 1 i).symm

/-- The nth powers are exactly the three distinct nonzero terminal constructors. -/
theorem terminal_powers (n : ℕ) (hn : 0 < n) (q : Bool) (i : Fin 3) :
    positivePower (generator n q i) (n - 1) = .terminal i := by
  rw [generator_power, Nat.sub_add_cancel hn, normal_pure_terminal n hn]

/-- Every element has a positive monomial representative, including zero. -/
theorem normal_surjective (n : ℕ) (hn : 0 < n) (q : Bool) (s : Model n q) :
    ∃ a : Exponent, 0 < a.card ∧ normal n q a = s := by
  cases s with
  | zero => exact ⟨Multiset.replicate (n + 1) 0, by simp,
      normal_of_large _ (by simp)⟩
  | lower a => exact ⟨a.val.val, a.val.property.1, normal_lower a⟩
  | terminal i => exact ⟨Multiset.replicate n i, by simpa,
      by simpa only [generator_power, Nat.sub_add_cancel hn] using terminal_powers n hn q i⟩

/-- Generation is by genuine nonempty products of the three degree-one elements. -/
theorem generated (n : ℕ) (hn : 0 < n) (q : Bool) :
    Subsemigroup.closure (Set.range (generator n q)) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨a, ha, rfl⟩ := normal_surjective n hn q s
  induction a using Multiset.induction_on with
  | empty => simp at ha
  | @cons i a ih =>
    by_cases he : a = 0
    · subst a
      exact Subsemigroup.subset_closure ⟨i, rfl⟩
    · have hp : 0 < a.card := Multiset.card_pos.mpr he
      have hmul := normal_mul (n := n) (q := q) ({i} : Exponent) a (by simp) hp
      rw [show i ::ₘ a = {i} + a by rfl, ← hmul]
      exact Subsemigroup.mul_mem _ (Subsemigroup.subset_closure ⟨i, rfl⟩) (ih hp trivial)

/-- Collapse precisely the lower monomials divisible by xyz. -/
def quotient {n} : Model n false → Model n true
  | .zero => 0
  | .terminal i => .terminal i
  | .lower a => if h : survives true a.val.val then .lower ⟨a.val, h⟩ else 0

private theorem quotient_normal (n : ℕ) (a : Exponent) :
    quotient (normal n false a) = normal n true a := by
  by_cases h : 0 < a.card ∧ a.card < n
  · have ht : ¬ (a.card = n ∧ 0 < n) := by omega
    simp only [normal, survives, Bool.false_eq_true, false_or, true_or,
      and_true, dif_pos h, quotient]
    by_cases hm : mixed a <;> simp [hm, h.1, h.2, ht]
  · have hF : ¬ (0 < a.card ∧ a.card < n ∧ survives false a) := by tauto
    have hT : ¬ (0 < a.card ∧ a.card < n ∧ survives true a) := by tauto
    simp only [normal, dif_neg hF, dif_neg hT]
    split
    · split <;> rfl
    · rfl

/-- The actual quotient is multiplicative on the entire cyclic carrier. -/
theorem quotient_mul {n} (s t : Model n false) :
    quotient (s * t) = quotient s * quotient t := by
  cases s with
  | zero =>
    change quotient (0 * t) = 0 * quotient t
    rw [zero_mul, zero_mul]; rfl
  | terminal i =>
    cases t <;> simp [quotient, HMul.hMul, Mul.mul, modelMul]
  | lower a =>
    cases t with
    | zero =>
      change quotient (.lower a * 0) = quotient (.lower a) * 0
      rw [mul_zero, mul_zero]; rfl
    | terminal i =>
      change 0 = quotient (.lower a) * .terminal i
      generalize quotient (.lower a) = x
      cases x <;> rfl
    | lower b =>
      change quotient (normal n false (a.val.val + b.val.val)) = _
      rw [quotient_normal, ← normal_mul _ _ a.val.property.1 b.val.property.1,
        ← quotient_normal, ← quotient_normal, normal_lower a, normal_lower b]

/-- Exactly the indicated ideal is collapsed; every other fiber is a singleton. -/
theorem quotient_fibers {n} (s t : Model n false) :
    quotient s = quotient t ↔ s = t ∨
      (s = 0 ∨ ∃ a, s = .lower a ∧ mixed a.val.val) ∧
      (t = 0 ∨ ∃ a, t = .lower a ∧ mixed a.val.val) := by
  have props (a : Lower n false) : survives false a.val.val ∧
      0 < a.val.val.card ∧ a.val.val.card ≤ n - 1 := ⟨a.property, a.val.property⟩
  cases s <;> cases t <;>
    simp only [quotient, survives, Bool.true_eq_false, false_or]
  all_goals (try split_ifs) <;>
    simp_all [show (0 : Model n false) = .zero from rfl,
      show (0 : Model n true) = .zero from rfl, Model.lower.injEq, Subtype.ext_iff]
  all_goals grind

/-- Every quotient normal form has a preimage in the original cyclic carrier. -/
theorem quotient_surjective (n : ℕ) : Function.Surjective (@quotient n) := by
  intro s
  cases s with
  | zero => exact ⟨0, rfl⟩
  | terminal i => exact ⟨.terminal i, rfl⟩
  | lower a =>
    exact ⟨.lower ⟨a.val, Or.inl rfl⟩, by simp [quotient, a.property]⟩

end D5.S0.Certificates.Algebra.BergmanCyclicSemigroup

namespace D5.S0.Certificates.Algebra.BergmanCyclicSemigroup

open BergmanCyclicSemigroup

abbrev Positive := {a : Exponent // 0 < a.card}

/-- The free commutative semigroup with an absorbing zero, with no empty word. -/
inductive Word where
  | zero
  | monomial (a : Positive)
  deriving DecidableEq

instance : Zero Word := ⟨.zero⟩

def wordMul : Word → Word → Word
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

instance : IsMulCommutative Word := ⟨⟨by
  intro a b; cases a <;> cases b <;> simp [HMul.hMul, Mul.mul, wordMul, add_comm]⟩⟩

def reduce (n : ℕ) (q : Bool) : Word → Model n q
  | .zero => 0
  | .monomial a => normal n q a.val

private theorem reduce_mul (n : ℕ) (q : Bool) (s t : Word) :
    reduce n q (s * t) = reduce n q s * reduce n q t := by
  cases s with
  | zero =>
    change 0 = 0 * reduce n q t
    rw [zero_mul]
  | monomial a =>
    cases t with
    | zero =>
      change 0 = normal n q a.val * 0
      rw [mul_zero]
    | monomial b => exact (normal_mul a.val b.val a.property b.property).symm

/-- Exactly the cyclic terminal lists, terminal xyz relations, degree n+1 relations,
and the optional single relation xyz=0. Congruence closure supplies their multiples. -/
inductive Relations (n : ℕ) (hn : 0 < n) (q : Bool) : Word → Word → Prop
  | terminal (a : Positive) (i : Fin 3) (degree : a.val.card = n)
      (label : terminalLabel a.val = some i) :
      Relations n hn q (.monomial a)
        (.monomial ⟨Multiset.replicate n i, by simpa⟩)
  | mixed (a : Positive) (degree : a.val.card = n) (all : mixed a.val) :
      Relations n hn q (.monomial a) 0
  | truncation (a : Positive) (degree : a.val.card = n + 1) :
      Relations n hn q (.monomial a) 0
  | xyz (extra : q = true) :
      Relations n hn q (.monomial ⟨{0, 1, 2}, by simp⟩) 0

/-- The actual congruence generated by the written relations. -/
def presentation (n : ℕ) (hn : 0 < n) (q : Bool) : Con Word :=
  conGen (Relations n hn q)

private theorem relation_sound (n : ℕ) (hn : 0 < n) (q : Bool) {s t : Word}
    (h : Relations n hn q s t) : reduce n q s = reduce n q t := by
  cases h with
  | terminal a i hd hl =>
    simp [reduce, normal, hd, hn, hl, BergmanCyclicSemigroup.pure_label n hn i]
  | mixed a hd hm =>
    simp [reduce, normal, hd, hn, BergmanCyclicSemigroup.mixed_label hm]
  | truncation a hd =>
    simp [reduce, normal, hd]
  | xyz hq =>
    subst q
    exact BergmanCyclicSemigroup.normal_of_mixed _ (by simp [mixed])

private theorem presentation_sound (n : ℕ) (hn : 0 < n) (q : Bool) {s t : Word}
    (h : presentation n hn q s t) : reduce n q s = reduce n q t := by
  induction h with
  | of s t h => exact relation_sound n hn q h
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | mul h₁ h₂ ih₁ ih₂ => simp only [reduce_mul, ih₁, ih₂]

private theorem large_zero (n : ℕ) (hn : 0 < n) (q : Bool) (a : Exponent)
    (ha : 0 < a.card) (hd : n < a.card) :
    presentation n hn q (.monomial ⟨a, ha⟩) 0 := by
  induction a using Multiset.induction_on with
  | empty => simp at ha
  | @cons i a ih =>
    by_cases ht : n < a.card
    · have hp : 0 < a.card := by omega
      have hh := ConGen.Rel.mul
        (ConGen.Rel.refl (r := Relations n hn q) (Word.monomial ⟨{i}, by simp⟩))
        (ih hp ht)
      exact hh
    · apply ConGen.Rel.of
      exact Relations.truncation _ (by simp only [Multiset.card_cons] at hd ⊢; omega)

private theorem xyz_zero (n : ℕ) (hn : 0 < n) (a : Exponent)
    (ha : 0 < a.card) (hm : mixed a) :
    presentation n hn true (.monomial ⟨a, ha⟩) 0 := by
  have hle : ({0, 1, 2} : Exponent) ≤ a := by
    apply Multiset.le_iff_count.mpr
    intro i
    fin_cases i
    · simpa using Nat.succ_le_of_lt (Multiset.count_pos.mpr hm.1)
    · simpa using Nat.succ_le_of_lt (Multiset.count_pos.mpr hm.2.1)
    · simpa using Nat.succ_le_of_lt (Multiset.count_pos.mpr hm.2.2)
  obtain ⟨b, hb⟩ := Multiset.le_iff_exists_add.mp hle
  by_cases he : b = 0
  · subst b
    have heq : a = {0, 1, 2} := by simpa using hb
    subst a
    exact ConGen.Rel.of _ _ (Relations.xyz rfl)
  · have hp : 0 < b.card := Multiset.card_pos.mpr he
    have hh := ConGen.Rel.mul
      (ConGen.Rel.of _ _ (Relations.xyz (n := n) (hn := hn) rfl))
      (ConGen.Rel.refl (r := Relations n hn true) (Word.monomial ⟨b, hp⟩))
    change ConGen.Rel (Relations n hn true) (.monomial ⟨a, ha⟩) 0
    simpa only [HMul.hMul, Mul.mul, wordMul, ← hb] using hh

/-- Choose a free positive monomial for each normal form; zero stays zero. -/
def representative (n : ℕ) (hn : 0 < n) {q} : Model n q → Word
  | .zero => 0
  | .lower a => .monomial ⟨a.val.val, a.val.property.1⟩
  | .terminal i => .monomial ⟨Multiset.replicate n i, by simpa⟩

private theorem word_reduces (n : ℕ) (hn : 0 < n) (q : Bool) (s : Word) :
    presentation n hn q s (representative n hn (reduce n q s)) := by
  cases s with
  | zero => exact ConGen.Rel.refl _
  | monomial a =>
    change presentation n hn q (.monomial a) (representative n hn (normal n q a.val))
    by_cases hs : survives q a.val
    · by_cases hd : a.val.card < n
      · unfold normal
        rw [dif_pos (show 0 < a.val.card ∧ a.val.card < n ∧ survives q a.val from
          ⟨a.property, hd, hs⟩)]
        exact ConGen.Rel.refl _
      · by_cases he : a.val.card = n
        · have hnorm : normal n q a.val =
              match terminalLabel a.val with
              | some i => Model.terminal i
              | none => 0 := by simp [normal, he, hn]
          rw [hnorm]
          cases hl : terminalLabel a.val with
          | some i => exact ConGen.Rel.of _ _ (Relations.terminal a i he hl)
          | none =>
            have hm : mixed a.val := by
              obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp a.property
              fin_cases i <;> simp only [terminalLabel] at hl <;>
                split_ifs at hl <;> simp_all [mixed]
              all_goals tauto
            exact ConGen.Rel.of _ _ (Relations.mixed a he hm)
        · rw [BergmanCyclicSemigroup.normal_of_large _ (by omega)]
          exact large_zero n hn q a.val a.property (by omega)
    · have hq : q = true := by cases q <;> simp_all [survives]
      subst q
      have hm : mixed a.val := by simpa [survives] using hs
      rw [BergmanCyclicSemigroup.normal_of_mixed _ hm]
      exact xyz_zero n hn a.val a.property hm

/-- Equality of normal forms is exactly derivability from the written presentation. -/
theorem normal_form_complete (n : ℕ) (hn : 0 < n) (q : Bool) (s t : Word) :
    presentation n hn q s t ↔ reduce n q s = reduce n q t := by
  constructor
  · exact presentation_sound n hn q
  · intro h
    exact ConGen.Rel.trans (word_reduces n hn q s)
      (h ▸ ConGen.Rel.symm (word_reduces n hn q t))

end D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
