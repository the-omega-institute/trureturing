/- GID: D5/S0/Certificates/Algebra/BergmanCyclicGrading
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanCyclicGrading
   mirror-E: none(waiver:noncomputational)
   anchors: [mathlib/module/Mathlib.Data.Sym.Card, mathlib/module/Mathlib.Data.Finsupp.Multiset, mathlib/module/Mathlib.LinearAlgebra.Dimension.Constructions]
   utility: none
   digest: Actual cyclic semigroup products have exact graded sizes and nilpotency. -/

import D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
import Batteries.Tactic.OpenPrivate

/-! # Grading, cardinalities and nilpotency of the actual cyclic algebras -/

noncomputable section

namespace D5.S0.Certificates.Algebra.BergmanCyclicGrading

open BergmanCyclicSemigroup
open BergmanQuestion15Refutation (Contracted delta positivePower product)
open BergmanQuestion23Refutation (Monomial PositiveIndex DualIndex mixedPower)
open BergmanContractedAlgebra
open scoped BigOperators IsMulCommutative

open private normal_lower normal_pure_terminal from
  D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
open private card_dual positiveEquiv from
  D5.S0.Certificates.Algebra.BergmanQuestion23Refutation

/-- A right associated product of exactly k+1 arbitrary factors; no unit is adjoined. -/
def positiveProduct {R : Type*} [Mul R] : (k : ℕ) → (Fin (k + 1) → R) → R
  | 0, a => a 0
  | k + 1, a => a 0 * positiveProduct k (fun i => a i.succ)

section Products
variable {F S : Type*} [Field F] [SemigroupWithZero S]

private theorem delta_power (s : S) (k : ℕ) :
    positivePower (delta F S s) k = delta F S (positivePower s k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [positivePower, ih, delta_mul]; rfl

private theorem delta_span : Submodule.span F (Set.range (delta F S)) = ⊤ := by
  apply top_unique
  intro x _
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single s r =>
    have h := Submodule.smul_mem (Submodule.span F (Set.range (delta F S))) r
      (Submodule.subset_span (Set.mem_range_self s.val))
    simpa [delta, s.property, Finsupp.smul_single] using h

private theorem mixed_span (k : ℕ) :
    mixedPower (product F S) ⊤ k = Submodule.span F
      (Set.range (fun a : Fin (k + 1) → S => delta F S (positiveProduct k a))) := by
  induction k with
  | zero =>
    simp only [mixedPower, positiveProduct]
    rw [show (Set.range fun a : Fin 1 → S => delta F S (a 0)) =
      Set.range (delta F S) by
        ext x; constructor
        · rintro ⟨a, rfl⟩; exact ⟨a 0, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨fun _ => s, rfl⟩]
    exact delta_span.symm
  | succ k ih =>
    rw [mixedPower, ih, ← delta_span (F := F) (S := S), Submodule.map₂_span_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, _, ⟨a, rfl⟩, rfl⟩
      refine ⟨Fin.cons s a, ?_⟩
      exact (delta_mul _ _).symm
    · rintro ⟨a, rfl⟩
      refine ⟨delta F S (a 0), ⟨a 0, rfl⟩,
        delta F S (positiveProduct k (fun i => a i.succ)),
        ⟨fun i => a i.succ, rfl⟩, ?_⟩
      exact delta_mul _ _

private theorem algebra_nilpotent (k : ℕ)
    (h : ∀ a : Fin (k + 1) → S, positiveProduct k a = 0) :
    mixedPower (product F S) ⊤ k = ⊥ ∧
    ∀ a : Fin (k + 1) → Contracted F S, positiveProduct k a = 0 := by
  have hz : mixedPower (product F S) ⊤ k = ⊥ := by
    rw [mixed_span]
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    simp [h a, delta]
  refine ⟨hz, ?_⟩
  intro a
  have hm (j : ℕ) (b : Fin (j + 1) → Contracted F S) :
      positiveProduct j b ∈ mixedPower (product F S) ⊤ j := by
    induction j with
    | zero => trivial
    | succ j ih =>
      exact Submodule.apply_mem_map₂ _ (Submodule.mem_top) (ih (fun i => b i.succ))
  have hh := hm k a
  rwa [hz, Submodule.mem_bot] at hh

end Products

/-- Degree of the actual normal form, with zero assigned degree zero. -/
def degree {n q} : Model n q → ℕ
  | .zero => 0
  | .lower a => a.val.val.card
  | .terminal _ => n

private theorem degree_le {n q} (s : Model n q) : degree s ≤ n := by
  cases s with
  | zero => exact Nat.zero_le _
  | terminal i => exact le_rfl
  | lower a => have := a.val.property.2; simp only [degree]; omega

private theorem degree_pos {n q} (hn : 0 < n) (s : Model n q) (hs : s ≠ 0) :
    0 < degree s := by
  cases s with
  | zero => exact False.elim (hs rfl)
  | lower a => exact a.val.property.1
  | terminal i => exact hn

private theorem degree_normal {n q} (a : Exponent) (h : normal n q a ≠ 0) :
    degree (normal n q a) = a.card := by
  unfold normal at h ⊢
  split_ifs at h ⊢ with hA hB
  · rfl
  · cases hl : terminalLabel a <;> simp_all [degree]
  · exact False.elim (h rfl)

private theorem degree_mul {n q} (s t : Model n q) (h : s * t ≠ 0) :
    degree (s * t) = degree s + degree t := by
  cases s <;> cases t <;> try exact False.elim (h rfl)
  rename_i a b
  exact (degree_normal _ h).trans (Multiset.card_add _ _)

private theorem product_degree {n q} (hn : 0 < n) (k : ℕ)
    (a : Fin (k + 1) → Model n q) (h : positiveProduct k a ≠ 0) :
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

/-- All n+1-fold products vanish in both actual objects, while a generator's nth power survives. -/
theorem nilpotency (F : Type*) [Field F] (n : ℕ) (hn : 0 < n) (q : Bool) :
    (∀ a : Fin (n + 1) → Model n q, positiveProduct n a = 0) ∧
    positivePower (generator n q 0) (n - 1) ≠ 0 ∧
    mixedPower (product F (Model n q)) ⊤ n = ⊥ ∧
    (∀ a : Fin (n + 1) → Contracted F (Model n q), positiveProduct n a = 0) ∧
    positivePower (delta F (Model n q) (generator n q 0)) (n - 1) ≠ 0 := by
  have hzero : ∀ a : Fin (n + 1) → Model n q, positiveProduct n a = 0 := by
    intro a
    by_contra h
    have := product_degree hn n a h
    have := degree_le (positiveProduct n a)
    omega
  have halg := algebra_nilpotent (F := F) n hzero
  refine ⟨hzero, ?_, halg.1, halg.2, ?_⟩
  · rw [terminal_powers n hn]; intro h; cases h
  · classical
    rw [delta_power, terminal_powers n hn]
    simp [delta, show (Model.terminal (0 : Fin 3) : Model n q) ≠ 0 by
      intro h; cases h]

private abbrev xyz : Exponent := {0, 1, 2}

private theorem xyz_le {a : Exponent} (hm : mixed a) : xyz ≤ a := by
  apply Multiset.le_iff_count.mpr
  intro i
  fin_cases i
  · simpa [xyz] using Nat.succ_le_of_lt (Multiset.count_pos.mpr hm.1)
  · simpa [xyz] using Nat.succ_le_of_lt (Multiset.count_pos.mpr hm.2.1)
  · simpa [xyz] using Nat.succ_le_of_lt (Multiset.count_pos.mpr hm.2.2)

private def mixedLowerEquiv (t : ℕ) (ht : 3 ≤ t) :
    {a : PositiveIndex 3 t // mixed a.val} ≃ DualIndex 3 (t - 3) where
  toFun a := ⟨a.val.val - xyz, by
    rw [Multiset.card_sub (xyz_le a.property), show xyz.card = 3 by decide]
    have := a.val.property.2; omega⟩
  invFun b := ⟨⟨xyz + b.val, by simp [xyz], by
    simp only [Multiset.card_add, show xyz.card = 3 by decide]
    have := b.property; omega⟩, by simp [xyz, mixed]⟩
  left_inv a := by
    apply Subtype.ext; apply Subtype.ext
    exact (add_comm xyz (a.val.val - xyz)).trans
      (Multiset.sub_add_cancel (xyz_le a.property))
  right_inv b := by
    apply Subtype.ext
    exact (congrArg (fun x : Exponent => x - xyz) (add_comm xyz b.val)).trans
      Multiset.add_sub_cancel_right

private theorem positive_card (t : ℕ) :
    Fintype.card (PositiveIndex 3 t) = (t + 3).choose 3 - 1 := by
  classical
  let ez : {b : DualIndex 3 t // b.val = 0} ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨⟨0, by simp⟩, rfl⟩
    left_inv := by intro b; apply Subtype.ext; exact Subtype.ext b.property.symm
    right_inv := fun _ => rfl }
  have hz : Fintype.card {b : DualIndex 3 t // b.val = 0} = 1 := by
    simpa using Fintype.card_congr ez
  rw [Fintype.card_congr (positiveEquiv 3 t), Fintype.card_subtype_compl, hz, card_dual]
  rw [Nat.choose_symm_of_eq_add (show 3 + t = t + 3 by omega), Nat.add_comm 3 t]

private def modelEquiv (n : ℕ) (q : Bool) : Model n q ≃ Option (Lower n q ⊕ Fin 3) where
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

private theorem lower_cards (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (Lower n false) = (n + 2).choose 3 - 1 ∧
    Fintype.card (Lower n true) = 3 * n * (n - 1) / 2 := by
  classical
  let ef : Lower n false ≃ PositiveIndex 3 (n - 1) := {
    toFun := Subtype.val
    invFun := fun a => ⟨a, Or.inl rfl⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let et : Lower n true ≃ {a : PositiveIndex 3 (n - 1) // ¬ mixed a.val} := {
    toFun := fun a => ⟨a.val, by simpa [survives] using a.property⟩
    invFun := fun a => ⟨a.val, by simpa [survives] using a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hp : Fintype.card (PositiveIndex 3 (n - 1)) = (n + 2).choose 3 - 1 := by
    rw [positive_card, show n - 1 + 3 = n + 2 by omega]
  have hm : Fintype.card {a : PositiveIndex 3 (n - 1) // mixed a.val} =
      (n - 1).choose 3 := by
    by_cases h4 : 4 ≤ n
    · rw [Fintype.card_congr (mixedLowerEquiv (n - 1) (by omega)), card_dual,
        Nat.choose_symm_of_eq_add (show 3 + (n - 1 - 3) = (n - 1 - 3) + 3 by omega)]
      congr 1; omega
    · haveI : IsEmpty {a : PositiveIndex 3 (n - 1) // mixed a.val} := ⟨by
        intro a
        have hc := Multiset.card_le_card (xyz_le a.property)
        have hb := a.val.property.2
        change 3 ≤ a.val.val.card at hc
        omega⟩
      rw [Fintype.card_eq_zero, Nat.choose_eq_zero_of_lt (by omega)]
  refine ⟨(Fintype.card_congr ef).trans hp, ?_⟩
  rw [Fintype.card_congr et, Fintype.card_subtype_compl, hp, hm]
  have h₁ : (n + 2).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 := by
    simpa [Nat.add_assoc] using Nat.choose_succ_succ (n + 1) 2
  have h₂ : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ n 2
  have h₃ : n.choose 3 = (n - 1).choose 2 + (n - 1).choose 3 := by
    simpa [show n - 1 + 1 = n by omega] using Nat.choose_succ_succ (n - 1) 2
  have h₄ : (n + 1).choose 2 = n + n.choose 2 := by
    simpa using Nat.choose_succ_succ n 1
  have h₅ : n.choose 2 = n - 1 + (n - 1).choose 2 := by
    simpa [show n - 1 + 1 = n by omega] using Nat.choose_succ_succ (n - 1) 1
  have hmul := Nat.add_one_mul_choose_eq (n - 1) 1
  simp only [Nat.choose_one_right, show n - 1 + 1 = n by omega] at h₁ h₂ h₃ h₄ h₅ hmul
  have he : 3 * n * (n - 1) = 2 * (3 * n.choose 2) := by nlinarith [hmul]
  rw [he]
  omega

/-- The exact carrier sizes and dimensions count the actual nonzero normal-form bases. -/
theorem cardinalities (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (Model n false) = (n + 2).choose 3 + 3 ∧
    Fintype.card (Model n true) = 3 * n * (n - 1) / 2 + 4 ∧
    ∀ (F : Type*) [Field F],
      Module.finrank F (Contracted F (Model n false)) = (n + 2).choose 3 + 2 ∧
      Module.finrank F (Contracted F (Model n true)) = 3 * n * (n - 1) / 2 + 3 := by
  classical
  have h := lower_cards n hn
  have hc (q : Bool) : Fintype.card (Model n q) = Fintype.card (Lower n q) + 4 := by
    rw [Fintype.card_congr (modelEquiv n q)]
    simp
  have hf : Fintype.card (Model n false) = (n + 2).choose 3 + 3 := by
    rw [hc, h.1]
    have := Nat.choose_pos (show 3 ≤ n + 2 by omega)
    omega
  have ht : Fintype.card (Model n true) = 3 * n * (n - 1) / 2 + 4 := by rw [hc, h.2]
  refine ⟨hf, ht, ?_⟩
  intro F inst
  have hd (q : Bool) : Module.finrank F (Contracted F (Model n q)) =
      Fintype.card (Model n q) - 1 := by
    change Module.finrank F ({s : Model n q // s ≠ 0} →₀ F) = _
    rw [Module.finrank_finsupp_self, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  rw [hd, hd, hf, ht]
  omega

/-- The set of all products of k+1 generators, including any products equal to zero. -/
def generatorProducts (n : ℕ) (q : Bool) (k : ℕ) : Set (Model n q) :=
  Set.range (fun f : Fin (k + 1) → Fin 3 => positiveProduct k (fun i => generator n q (f i)))

private theorem generator_product (n : ℕ) (q : Bool) (k : ℕ)
    (f : Fin (k + 1) → Fin 3) :
    positiveProduct k (fun i => generator n q (f i)) =
      normal n q (List.ofFn f : Exponent) := by
  induction k with
  | zero => simp [positiveProduct, generator, List.ofFn_succ]
  | succ k ih =>
    rw [positiveProduct, ih]
    change normal n q {f 0} * normal n q (List.ofFn (fun i => f i.succ) : Exponent) = _
    rw [normal_mul _ _ (by simp) (by simp)]
    simp [List.ofFn_succ]

private theorem sym_word (d : ℕ) (a : Sym (Fin 3) d) :
    ∃ f : Fin d → Fin 3, (List.ofFn f : Exponent) = a.val := by
  induction d with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    have ha : a.val = 0 := Multiset.card_eq_zero.mp a.property
    simpa only [List.ofFn_zero, Multiset.coe_nil] using ha.symm
  | succ d ih =>
    obtain ⟨i, b, rfl⟩ := Sym.exists_eq_cons_of_succ a
    obtain ⟨f, hf⟩ := ih b
    refine ⟨Fin.cons i f, ?_⟩
    change (List.ofFn (Fin.cons i f) : Exponent) = i ::ₘ (b : Exponent)
    rw [List.ofFn_succ]
    change i ::ₘ (List.ofFn f : Exponent) = i ::ₘ b.val
    exact congrArg (Multiset.cons i) hf

/-- Actual products are precisely the reductions of all monomials of that degree. -/
theorem product_sets (n : ℕ) (q : Bool) (k : ℕ) :
    generatorProducts n q k = Set.range (fun a : Sym (Fin 3) (k + 1) => normal n q a.val) := by
  ext s
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨⟨List.ofFn f, by simp⟩, (generator_product n q k f).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨f, hf⟩ := sym_word (k + 1) a
    refine ⟨f, ?_⟩
    change positiveProduct k (fun i => generator n q (f i)) = normal n q a.val
    exact (generator_product n q k f).trans (congrArg (normal n q) hf)

private def mixedSliceEquiv (d : ℕ) (hd : 3 ≤ d) :
    {a : Sym (Fin 3) d // mixed a.val} ≃ Sym (Fin 3) (d - 3) where
  toFun a := ⟨a.val.val - xyz, by
    rw [Multiset.card_sub (xyz_le a.property), a.val.property]
    rfl⟩
  invFun b := ⟨⟨xyz + b.val, by
    simp only [Multiset.card_add, b.property]
    change 3 + (d - 3) = d
    omega⟩,
    by simp [xyz, mixed]⟩
  left_inv a := by
    apply Subtype.ext; apply Subtype.ext
    exact (add_comm xyz (a.val.val - xyz)).trans (Multiset.sub_add_cancel (xyz_le a.property))
  right_inv b := by
    apply Subtype.ext
    exact (congrArg (fun x : Exponent => x - xyz) (add_comm xyz b.val)).trans
      Multiset.add_sub_cancel_right

private theorem slice_card (d : ℕ) : Fintype.card (Sym (Fin 3) d) = (d + 2).choose 2 := by
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  rw [Nat.choose_symm_of_eq_add (show 3 + d - 1 = d + 2 by omega)]
  congr 1; omega

private theorem surviving_slice_card (d : ℕ) (hd : 0 < d) :
    Fintype.card {a : Sym (Fin 3) d // survives true a.val} = 3 * d := by
  classical
  simp only [survives, Bool.true_eq_false, false_or]
  rw [Fintype.card_subtype_compl, slice_card]
  by_cases h : 3 ≤ d
  · have hm : Fintype.card {a : Sym (Fin 3) d // mixed a.val} = (d - 1).choose 2 := by
      rw [Fintype.card_congr (mixedSliceEquiv d h), slice_card]
      congr 1; omega
    rw [hm]
    have h₁ : (d + 2).choose 2 = d + 1 + (d + 1).choose 2 := by
      simpa [Nat.add_assoc] using Nat.choose_succ_succ (d + 1) 1
    have h₂ : (d + 1).choose 2 = d + d.choose 2 := by
      simpa using Nat.choose_succ_succ d 1
    have h₃ : d.choose 2 = d - 1 + (d - 1).choose 2 := by
      simpa [show d - 1 + 1 = d by omega] using Nat.choose_succ_succ (d - 1) 1
    omega
  · have hm : IsEmpty {a : Sym (Fin 3) d // mixed a.val} := ⟨by
      intro a
      have := Multiset.card_le_card (xyz_le a.property)
      rw [a.val.property] at this
      change 3 ≤ d at this
      omega⟩
    have he := Fintype.card_eq_zero (α := {a : Sym (Fin 3) d // mixed a.val})
    have cases : d = 1 ∨ d = 2 := by omega
    rcases cases with rfl | rfl <;> norm_num [he, Nat.choose]

private def lowerProductEquiv (n : ℕ) (q : Bool) (d : ℕ) (hd : 0 < d) (hdn : d < n) :
    {a : Sym (Fin 3) d // survives q a.val} ≃
      {s : Model n q // s ∈ generatorProducts n q (d - 1) ∧ s ≠ 0} := by
  let f (a : {a : Sym (Fin 3) d // survives q a.val}) :
      {s : Model n q // s ∈ generatorProducts n q (d - 1) ∧ s ≠ 0} :=
    ⟨.lower ⟨⟨a.val.val, by rw [a.val.property]; exact ⟨hd, by omega⟩⟩, a.property⟩, by
      constructor
      · rw [product_sets]
        refine ⟨⟨a.val.val, by rw [a.val.property]; omega⟩, ?_⟩
        change normal n q a.val.val = _
        exact normal_lower ⟨⟨a.val.val, by rw [a.val.property]; exact ⟨hd, by omega⟩⟩,
          a.property⟩
      · intro h; cases h⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have he := congrArg (fun x => match x.val with
      | Model.lower a => a.val.val
      | _ => 0) h
    exact Subtype.ext (Subtype.ext he)
  · rintro ⟨s, hs, hnz⟩
    rw [product_sets] at hs
    obtain ⟨a, rfl⟩ := hs
    change normal n q a.val ≠ 0 at hnz
    have ha : a.val.card = d := by have := a.property; omega
    have hsurv : survives q a.val := by
      by_contra hh
      apply hnz
      unfold normal
      rw [dite_eq_right (by rintro ⟨_, _, hs⟩; exact hh hs),
        ite_eq_right (by rintro ⟨he, _⟩; omega)]
    refine ⟨⟨⟨a.val, ha⟩, hsurv⟩, ?_⟩
    apply Subtype.ext
    change Model.lower _ = normal n q a.val
    symm
    exact normal_lower ⟨⟨a.val, by rw [ha]; exact ⟨hd, by omega⟩⟩, hsurv⟩

/-- Below n, count actual generator products after excluding zero. -/
theorem lower_product_counts (n d : ℕ) (hd : 0 < d) (hdn : d < n) :
    Nat.card {s : Model n false // s ∈ generatorProducts n false (d - 1) ∧ s ≠ 0} =
      (d + 2).choose 2 ∧
    Nat.card {s : Model n true // s ∈ generatorProducts n true (d - 1) ∧ s ≠ 0} = 3 * d := by
  have h (q : Bool) := Nat.card_congr (lowerProductEquiv n q d hd hdn)
  constructor
  · rw [← h false, Nat.card_eq_fintype_card]
    simpa [survives] using slice_card d
  · rw [← h true, Nat.card_eq_fintype_card]
    exact surviving_slice_card d hd

private theorem terminal_mem (n : ℕ) (hn : 0 < n) (q : Bool) (i : Fin 3) :
    (Model.terminal i : Model n q) ∈ generatorProducts n q (n - 1) := by
  rw [product_sets]
  refine ⟨⟨Multiset.replicate n i, by simp; omega⟩, ?_⟩
  exact normal_pure_terminal n hn q i

/-- In degree n the nonzero products are exactly the three terminals, and zero also occurs. -/
theorem terminal_products (n : ℕ) (hn : 3 ≤ n) (q : Bool) :
    {s : Model n q | s ∈ generatorProducts n q (n - 1) ∧ s ≠ 0} =
      Set.range (Model.terminal : Fin 3 → Model n q) ∧
    Nat.card {s : Model n q // s ∈ generatorProducts n q (n - 1) ∧ s ≠ 0} = 3 ∧
    (0 : Model n q) ∈ generatorProducts n q (n - 1) := by
  have heq : {s : Model n q | s ∈ generatorProducts n q (n - 1) ∧ s ≠ 0} =
      Set.range (Model.terminal : Fin 3 → Model n q) := by
    ext s
    constructor
    · rintro ⟨hs, hne⟩
      rw [product_sets] at hs
      obtain ⟨a, rfl⟩ := hs
      have hd : a.val.card = n := by have := a.property; omega
      change normal n q a.val ≠ 0 at hne
      change normal n q a.val ∈ Set.range (Model.terminal : Fin 3 → Model n q)
      unfold normal at hne ⊢
      rw [dite_eq_right (by rintro ⟨_, hh, _⟩; omega),
        ite_eq_left ⟨hd, by omega⟩] at hne ⊢
      cases hl : terminalLabel a.val with
      | none => exact (hne (by rw [hl])).elim
      | some i => exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨terminal_mem n (by omega) q i, by intro h; cases h⟩
  refine ⟨heq, ?_, ?_⟩
  · change Nat.card ({s : Model n q | s ∈ generatorProducts n q (n - 1) ∧ s ≠ 0}) = 3
    rw [heq]
    let f : Fin 3 ↪ Model n q := ⟨Model.terminal, by intro i j h; cases h; rfl⟩
    exact (Nat.card_congr (Equiv.ofInjective f f.injective)).symm.trans (by simp)
  · rw [product_sets]
    let a : Exponent := xyz + Multiset.replicate (n - 3) 0
    have hd : a.card = n := by simp [a, xyz]; omega
    have hm : mixed a := by simp [a, xyz, mixed]
    refine ⟨⟨a, by omega⟩, ?_⟩
    have hl : terminalLabel a = none := by
      simp [terminalLabel, hm.1, hm.2.1, hm.2.2]
    simp [normal, hd, show 0 < n by omega, hl]

end D5.S0.Certificates.Algebra.BergmanCyclicGrading
