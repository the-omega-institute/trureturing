/- GID: D5/S3/Combinatorics/Latin/AlternatingSignMargins
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/AlternatingSignMargins
   mirror-E: none(waiver:general-existence)
   anchors: []
   utility: none
   digest: Alternating signed square matrices realize exactly the equal-total margins. -/

/-
result:
  proof_shape: content
  escape_witness: signed_matrix constructs a signed incidence difference with simultaneous
    margins; surplus positive and negative rows share distinct zero-margin columns.
  admission_basis: open-problem-resolution (#12576; Proved)
  Direct frozen dependencies: [] (Mathlib only).
signed_matrix (private):
  proof_shape: content
  escape_witness: finite sign-class equivalences and the zero-column capacity count produce
    the placement matrix, whose row and column margins and alternation are verified.
  Direct frozen dependencies: [] (Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
The predicates and private constructions express an all-order existence theorem; no bounded
computation, checker, numerical reduction or certified finite instance is exported.
-/

import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Latin.AlternatingSignMargins

open scoped BigOperators

noncomputable section

/-- Consecutive nonzero entries in the natural order have different signs. -/
def Alternates {n : ℕ} (v : Fin n → ℤ) : Prop :=
  ∀ a b, a < b → v a ≠ 0 → v b ≠ 0 →
    (∀ c, a < c → c < b → v c = 0) → v a ≠ v b

def Signed (x : ℤ) : Prop := x = -1 ∨ x = 0 ∨ x = 1

/-- The source class, without imposing a particular first or last sign. -/
def W (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℤ) :=
  {X | (∀ i j, Signed (X i j)) ∧
    (∀ i, Alternates (X i)) ∧
    (∀ j, Alternates (fun i => X i j)) ∧
    (∀ i, Signed (∑ j, X i j)) ∧ (∀ j, Signed (∑ i, X i j))}

def claim : Prop := ∀ n : ℕ, ∀ R S : Fin n → ℤ,
  (∀ i, Signed (R i)) → (∀ j, Signed (S j)) →
  ((∃ X ∈ W n, (∀ i, ∑ j, X i j = R i) ∧
    (∀ j, ∑ i, X i j = S j)) ↔ ∑ i, R i = ∑ j, S j)

private noncomputable def incidence {α β A : Type*}
    (r : A ↪ α) (c : A ↪ β) (i : α) (j : β) : ℤ := by
  classical
  exact if ∃ a, r a = i ∧ c a = j then 1 else 0

private theorem signed_matrix {n : ℕ} (R S : Fin n → ℤ)
    (hR : ∀ i, Signed (R i)) (hS : ∀ j, Signed (S j))
    (hsum : ∑ i, R i = ∑ j, S j) (hle : (Fintype.card {i : Fin n // S i = 1}) ≤ (Fintype.card {i : Fin n // R i = 1})) :
    ∃ X ∈ W n, (∀ i, ∑ j, X i j = R i) ∧ (∀ j, ∑ i, X i j = S j) := by
  classical
  let merge {n d : ℕ} (S : Fin n → ℤ) (s : ℤ) (hs : s ≠ 0)
      (z : Fin d ↪ {j // S j = 0}) : ({j // S j = s} ⊕ Fin d) ↪ Fin n :=
    ((Function.Embedding.refl {j // S j = s}).sumMap z).trans
      (Function.Embedding.sumSet (s := {j | S j = s}) (t := {j | S j = 0}) (by
        rw [Set.disjoint_left]
        intro j hj hj0
        exact hs (hj.symm.trans hj0)))
  have sum_indicator {α : Type} [Fintype α] (p : α → Prop)
      [DecidablePred p] :
      (∑ i, if p i then (1 : ℤ) else 0) = Fintype.card {i // p i} := by
    classical
    simp [Finset.sum_boole, Fintype.card_subtype]
  have sum_signed {n : ℕ} (v : Fin n → ℤ) (hv : ∀ i, Signed (v i)) :
      (∑ i, v i) = ((Fintype.card {i : Fin n // v i = 1}) : ℤ) - (Fintype.card {i : Fin n // v i = (-1)}) := by
    classical
    have h : ∀ i, v i = (if v i = 1 then (1 : ℤ) else 0) -
        (if v i = -1 then 1 else 0) := by
      intro i
      rcases hv i with h | h | h <;> simp [h]
    calc
      (∑ i, v i) = ∑ i, ((if v i = 1 then (1 : ℤ) else 0) -
          (if v i = -1 then 1 else 0)) := Finset.sum_congr rfl (fun i _ => h i)
      _ = _ := by rw [Finset.sum_sub_distrib, sum_indicator, sum_indicator]
  have counts_total {n : ℕ} (v : Fin n → ℤ) (hv : ∀ i, Signed (v i)) :
      (Fintype.card {i : Fin n // v i = 1}) + (Fintype.card {i : Fin n // v i = (-1)}) + (Fintype.card {i : Fin n // v i = 0}) = n := by
    classical
    have h : ∀ i, (if v i = 1 then (1 : ℤ) else 0) +
        (if v i = -1 then 1 else 0) + (if v i = 0 then 1 else 0) = 1 := by
      intro i
      rcases hv i with h | h | h <;> simp [h]
    have hs := congrArg (fun f : Fin n → ℤ => ∑ i, f i) (funext h)
    simp only [Finset.sum_add_distrib, sum_indicator, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
    change ((Fintype.card {i : Fin n // v i = 1}) : ℤ) + (Fintype.card {i : Fin n // v i = (-1)}) + (Fintype.card {i : Fin n // v i = 0}) = n at hs
    omega
  have incidence_row {α β A : Type} [Fintype β]
      (r : A ↪ α) (c : A ↪ β) (i : α) :
      (∑ j, incidence r c i j) = if ∃ a, r a = i then 1 else 0 := by
    classical
    by_cases hi : ∃ a, r a = i
    · obtain ⟨a, ha⟩ := hi
      have hp : ∀ j, (∃ a', r a' = i ∧ c a' = j) ↔ c a = j := by
        intro j
        constructor
        · rintro ⟨a', h, hj⟩
          have : a' = a := r.injective (h.trans ha.symm)
          simpa [this] using hj
        · intro hj
          exact ⟨a, ha, hj⟩
      simp only [incidence, hp]
      simp [show ∃ a, r a = i from ⟨a, ha⟩]
    · have hp : ∀ j, ¬ ∃ a, r a = i ∧ c a = j := by
        rintro j ⟨a, ha, _⟩
        exact hi ⟨a, ha⟩
      simp [incidence, hp, hi]
  have incidence_col {α β A : Type} [Fintype α]
      (r : A ↪ α) (c : A ↪ β) (j : β) :
      (∑ i, incidence r c i j) = if ∃ a, c a = j then 1 else 0 := by
    have h : ∀ i, incidence r c i j = incidence c r j i := by
      classical
      intro i
      simp only [incidence, and_comm]
    simp_rw [h]
    exact incidence_row c r j
  have incidence_values {α β A : Type}
      (r : A ↪ α) (c : A ↪ β) (i : α) (j : β) :
      incidence r c i j = 0 ∨ incidence r c i j = 1 := by
    classical
    unfold incidence
    split_ifs <;> simp
  have incidence_row_unique {α β A : Type}
      (r : A ↪ α) (c : A ↪ β) {i : α} {j k : β}
      (hj : incidence r c i j ≠ 0) (hk : incidence r c i k ≠ 0) : j = k := by
    classical
    have hj' : ∃ a, r a = i ∧ c a = j := by
      by_contra h
      exact hj (by simp [incidence, h])
    have hk' : ∃ a, r a = i ∧ c a = k := by
      by_contra h
      exact hk (by simp [incidence, h])
    obtain ⟨a, hai, haj⟩ := hj'
    obtain ⟨b, hbi, hbk⟩ := hk'
    have : a = b := r.injective (hai.trans hbi.symm)
    exact haj.symm.trans (this ▸ hbk)
  have incidence_col_unique {α β A : Type}
      (r : A ↪ α) (c : A ↪ β) {i k : α} {j : β}
      (hi : incidence r c i j ≠ 0) (hk : incidence r c k j ≠ 0) : i = k := by
    classical
    apply incidence_row_unique c r
    · simpa only [incidence, and_comm] using hi
    · simpa only [incidence, and_comm] using hk
  have merge_range {n d : ℕ} (S : Fin n → ℤ) (s : ℤ) (hs : s ≠ 0)
      (z : Fin d ↪ {j // S j = 0}) (j : Fin n) :
      (∃ a, merge S s hs z a = j) ↔ S j = s ∨ ∃ k, (z k).val = j := by
    constructor
    · rintro ⟨a, ha⟩
      cases a with
      | inl a =>
        left
        change a.val = j at ha
        exact ha ▸ a.property
      | inr k => exact Or.inr ⟨k, ha⟩
    · rintro (h | ⟨k, hk⟩)
      · exact ⟨Sum.inl ⟨j, h⟩, rfl⟩
      · exact ⟨Sum.inr k, hk⟩
  let d := (Fintype.card {i : Fin n // R i = 1}) - (Fintype.card {i : Fin n // S i = 1})
  have hp : (Fintype.card {i : Fin n // R i = 1}) = (Fintype.card {i : Fin n // S i = 1}) + d := by dsimp [d]; omega
  have hq : (Fintype.card {i : Fin n // R i = (-1)}) = (Fintype.card {i : Fin n // S i = (-1)}) + d := by
    rw [sum_signed R hR, sum_signed S hS] at hsum
    omega
  have htR := counts_total R hR
  have htS := counts_total S hS
  have capacity : 2 * d ≤ (Fintype.card {i : Fin n // S i = 0}) := by omega
  have hd : d ≤ (Fintype.card {i : Fin n // S i = 0}) := by omega
  let eP : {i // R i = 1} ≃ ({j // S j = 1} ⊕ Fin d) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sum, Fintype.card_fin] using hp)
  let eN : {i // R i = -1} ≃ ({j // S j = -1} ⊕ Fin d) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sum, Fintype.card_fin] using hq)
  obtain ⟨z⟩ : Nonempty (Fin d ↪ {j // S j = 0}) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hd)
  let rP : {i // R i = 1} ↪ Fin n := Function.Embedding.subtype _
  let rN : {i // R i = -1} ↪ Fin n := Function.Embedding.subtype _
  let cP := eP.toEmbedding.trans (merge S 1 (by decide) z)
  let cN := eN.toEmbedding.trans (merge S (-1) (by decide) z)
  let X : Matrix (Fin n) (Fin n) ℤ :=
    fun i j => incidence rP cP i j - incidence rN cN i j
  have rPeq : ∀ i, (∃ a, rP a = i) ↔ R i = 1 := by
    intro i
    constructor
    · rintro ⟨a, ha⟩
      exact ha ▸ a.property
    · intro h
      exact ⟨⟨i, h⟩, rfl⟩
  have rNeq : ∀ i, (∃ a, rN a = i) ↔ R i = -1 := by
    intro i
    constructor
    · rintro ⟨a, ha⟩
      exact ha ▸ a.property
    · intro h
      exact ⟨⟨i, h⟩, rfl⟩
  have cPeq : ∀ j, (∃ a, cP a = j) ↔ S j = 1 ∨ ∃ k, (z k).val = j := by
    intro j
    rw [← merge_range S 1 (by decide) z j]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨eP a, ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨eP.symm a, by simpa [cP] using ha⟩
  have cNeq : ∀ j, (∃ a, cN a = j) ↔ S j = -1 ∨ ∃ k, (z k).val = j := by
    intro j
    rw [← merge_range S (-1) (by decide) z j]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨eN a, ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨eN.symm a, by simpa [cN] using ha⟩
  have hz0 : ∀ j, (∃ k, (z k).val = j) → S j = 0 := by
    rintro j ⟨k, hk⟩
    exact hk ▸ (z k).property
  have rows : ∀ i, ∑ j, X i j = R i := by
    intro i
    dsimp only [X]
    rw [Finset.sum_sub_distrib, incidence_row, incidence_row, rPeq, rNeq]
    rcases hR i with h | h | h <;> simp [h]
  have cols : ∀ j, ∑ i, X i j = S j := by
    intro j
    dsimp only [X]
    rw [Finset.sum_sub_distrib, incidence_col, incidence_col, cPeq, cNeq]
    by_cases hz : ∃ k, (z k).val = j
    · simp [hz, hz0 j hz]
    · rcases hS j with h | h | h <;> simp [h, hz]
  have entries : ∀ i j, Signed (X i j) := by
    intro i j
    have hpv := incidence_values rP cP i j
    have hnv := incidence_values rN cN i j
    dsimp only [X]
    rcases hpv with h | h <;> rcases hnv with h' | h' <;> simp [Signed, h, h']
  have row_alt : ∀ i, Alternates (X i) := by
    intro i a b hab ha hb _
    have one : ∀ j, X i j ≠ 0 →
        (incidence rP cP i j ≠ 0 ∨ incidence rN cN i j ≠ 0) := by
      intro j hj
      by_cases hpj : incidence rP cP i j = 0
      · right
        intro hnj
        exact hj (by simp [X, hpj, hnj])
      · exact Or.inl hpj
    rcases one a ha with hpa | hna <;> rcases one b hb with hpb | hnb
    · exact (ne_of_lt hab (incidence_row_unique rP cP hpa hpb)).elim
    · have hpi : R i = 1 := (rPeq i).mp (by
        by_contra h
        have h0 : incidence rP cP i a = 0 := by
          simp [incidence, show ¬ ∃ x, rP x = i ∧ cP x = a from fun ⟨x,hx,_⟩ => h ⟨x,hx⟩]
        exact hpa h0)
      have hni : R i = -1 := (rNeq i).mp (by
        by_contra h
        have h0 : incidence rN cN i b = 0 := by
          simp [incidence, show ¬ ∃ x, rN x = i ∧ cN x = b from fun ⟨x,hx,_⟩ => h ⟨x,hx⟩]
        exact hnb h0)
      omega
    · have hpi : R i = 1 := (rPeq i).mp (by
        by_contra h
        have h0 : incidence rP cP i b = 0 := by
          simp [incidence, show ¬ ∃ x, rP x = i ∧ cP x = b from fun ⟨x,hx,_⟩ => h ⟨x,hx⟩]
        exact hpb h0)
      have hni : R i = -1 := (rNeq i).mp (by
        by_contra h
        have h0 : incidence rN cN i a = 0 := by
          simp [incidence, show ¬ ∃ x, rN x = i ∧ cN x = a from fun ⟨x,hx,_⟩ => h ⟨x,hx⟩]
        exact hna h0)
      omega
    · exact (ne_of_lt hab (incidence_row_unique rN cN hna hnb)).elim
  have col_alt : ∀ j, Alternates (fun i => X i j) := by
    intro j a b hab ha hb _ heq
    have hpv := incidence_values rP cP a j
    have hnv := incidence_values rN cN a j
    have hpv' := incidence_values rP cP b j
    have hnv' := incidence_values rN cN b j
    rcases hpv with hp | hp <;> rcases hnv with hn | hn <;>
      rcases hpv' with hp' | hp' <;> rcases hnv' with hn' | hn'
    all_goals try { exfalso; simp [X, hp, hn] at ha }
    all_goals try { exfalso; simp [X, hp', hn'] at hb }
    all_goals try { exfalso; simp [X, hp, hn, hp', hn'] at heq }
    · exact ne_of_lt hab (incidence_col_unique rN cN (j := j) (by omega) (by omega))
    · exact ne_of_lt hab (incidence_col_unique rP cP (j := j) (by omega) (by omega))
  exact ⟨X, ⟨entries, row_alt, col_alt, fun i => (rows i).symm ▸ hR i,
    fun j => (cols j).symm ▸ hS j⟩, rows, cols⟩

theorem result : claim := by
  classical
  intro n R S hR hS
  constructor
  · rintro ⟨X, _, rows, cols⟩
    calc
      (∑ i, R i) = ∑ i, ∑ j, X i j := Finset.sum_congr rfl (fun i _ => (rows i).symm)
      _ = ∑ j, ∑ i, X i j := Finset.sum_comm
      _ = ∑ j, S j := Finset.sum_congr rfl (fun j _ => cols j)
  · intro hsum
    by_cases hle : (Fintype.card {i : Fin n // S i = 1}) ≤ (Fintype.card {i : Fin n // R i = 1})
    · exact signed_matrix R S hR hS hsum hle
    · obtain ⟨X, hX, rows, cols⟩ := signed_matrix S R hS hR hsum.symm (by omega)
      refine ⟨X.transpose, ?_, cols, rows⟩
      exact ⟨fun i j => hX.1 j i, hX.2.2.1, hX.2.1, hX.2.2.2.2, hX.2.2.2.1⟩

#check Fintype.card
#check incidence
#print axioms signed_matrix
#print axioms result

end

end D5.S3.Combinatorics.Latin.AlternatingSignMargins
