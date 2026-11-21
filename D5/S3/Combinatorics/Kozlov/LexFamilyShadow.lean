/- GID: D5/S3/Combinatorics/Kozlov/LexFamilyShadow
   generality: G
   mirror-B: none(waiver:probe-support)
   mirror-E: none(waiver:finite-lex-shadow-theory)
   anchors: [mathlib/module/Mathlib.Combinatorics.SetFamily.KruskalKatona]
   utility: none
   digest: Finite lex families attain the greedy bound for upper shadows. -/

import D5.S3.Combinatorics.Kozlov.LexGreedySplit
import Mathlib.Combinatorics.SetFamily.KruskalKatona

-- Source: https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/ModuleKK/LexShadow.lean
/-
Upstream pins: Lean v4.34.0-rc2, Mathlib 3a8a89422e16d67b7ae57698f6d96e389e4d4202.
Retire these declarations when the project's pinned Mathlib supplies equivalent results.

MIT License

Copyright (c) 2026 Jan Snellman

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

open Finset
open scoped FinsetFamily

namespace D5.S3.Combinatorics.Kozlov.LexCompression

/-! ### The lex order and lex-initial families -/

section Lex
variable {n : ℕ}

/-- `s` precedes `t` in lex (the note's `s >_lex t`): the smallest element of `s ∆ t` is in `s`. -/
def LexLT (s t : Finset (Fin n)) : Prop := ∃ a ∈ s, a ∉ t ∧ ∀ b ∈ t, b ∉ s → a < b

/-- `𝒜` is a lex-initial family of `k`-sets: all members have size `k`, and every `k`-set
lex-preceding a member is a member. -/
def IsLexInit (𝒜 : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  (𝒜 : Set (Finset (Fin n))).Sized k ∧
    ∀ ⦃s t : Finset (Fin n)⦄, s ∈ 𝒜 → LexLT t s → #t = k → t ∈ 𝒜

lemma lexLT_irrefl (s : Finset (Fin n)) : ¬ LexLT s s := by
  rintro ⟨a, ha, ha', -⟩; exact ha' ha

lemma isLexInit_empty (k : ℕ) : IsLexInit (∅ : Finset (Finset (Fin n))) k :=
  ⟨by simp, by simp⟩

lemma isLexInit_of_sized_zero {𝒜 : Finset (Finset (Fin n))}
    (h : (𝒜 : Set (Finset (Fin n))).Sized 0) : IsLexInit 𝒜 0 := by
  refine ⟨h, fun s t hs hts ht => ?_⟩
  have hs0 : s = ∅ := Finset.card_eq_zero.mp (h hs)
  have ht0 : t = ∅ := Finset.card_eq_zero.mp ht
  subst hs0; subst ht0; exact absurd hts (lexLT_irrefl _)

lemma isLexInit_powersetCard (k : ℕ) :
    IsLexInit (powersetCard k (univ : Finset (Fin n))) k :=
  ⟨fun _ hs => (mem_powersetCard.mp hs).2,
    fun _ _ _ _ ht => mem_powersetCard.mpr ⟨subset_univ _, ht⟩⟩

lemma upShadow_powersetCard (k : ℕ) :
    ∂⁺ (powersetCard k (univ : Finset (Fin n))) = powersetCard (k+1) univ := by
  ext t
  simp only [mem_upShadow_iff_erase_mem, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [card_erase_of_mem ha] at h
    have := card_pos.mpr ⟨a, ha⟩
    omega
  · intro h
    obtain ⟨a, ha⟩ : t.Nonempty := card_pos.mp (by omega)
    exact ⟨a, ha, by rw [card_erase_of_mem ha]; omega⟩

end Lex

/-! ### Splitting families on `Fin (n+1)` at the smallest element `0` -/

section Decomp
variable {n : ℕ}

/-- The note's `1 ∗ B`: `{0} ∪ (B + 1)`. -/
def c0 (B : Finset (Fin n)) : Finset (Fin (n+1)) := insert 0 (B.map (Fin.succEmb n))

/-- `B + 1`, a subset of `Fin (n+1)` avoiding `0`. -/
def lift (B : Finset (Fin n)) : Finset (Fin (n+1)) := B.map (Fin.succEmb n)

@[simp] lemma zero_mem_c0 (B : Finset (Fin n)) : (0 : Fin (n+1)) ∈ c0 B := mem_insert_self _ _

@[simp] lemma succ_mem_c0 {B : Finset (Fin n)} {i : Fin n} : i.succ ∈ c0 B ↔ i ∈ B := by
  simp [c0, Fin.succ_ne_zero]

@[simp] lemma zero_notMem_lift (B : Finset (Fin n)) : (0 : Fin (n+1)) ∉ lift B := by
  simp [lift, Fin.succ_ne_zero]

@[simp] lemma succ_mem_lift {B : Finset (Fin n)} {i : Fin n} : i.succ ∈ lift B ↔ i ∈ B := by
  simp [lift]

lemma c0_injective : Function.Injective (c0 (n := n)) := by
  intro A B h; ext i; rw [← succ_mem_c0 (B := A), h, succ_mem_c0]

lemma lift_injective : Function.Injective (lift (n := n)) := by
  intro A B h; ext i; rw [← succ_mem_lift (B := A), h, succ_mem_lift]

@[simp] lemma c0_ne_lift (A B : Finset (Fin n)) : c0 A ≠ lift B :=
  fun h => zero_notMem_lift B (h ▸ zero_mem_c0 A)

@[simp] lemma lift_ne_c0 (A B : Finset (Fin n)) : lift A ≠ c0 B := fun h => c0_ne_lift B A h.symm

@[simp] lemma card_c0 (B : Finset (Fin n)) : #(c0 B) = #B + 1 := by
  rw [c0, card_insert_of_notMem (by simp [Fin.succ_ne_zero]), card_map]

@[simp] lemma card_lift (B : Finset (Fin n)) : #(lift B) = #B := card_map _

lemma cases_c0_lift (S : Finset (Fin (n+1))) : (∃ B, S = c0 B) ∨ (∃ B, S = lift B) := by
  by_cases h : (0 : Fin (n+1)) ∈ S
  · refine Or.inl ⟨univ.filter (fun i => i.succ ∈ S), ?_⟩
    ext j; cases j using Fin.cases <;> simp [h]
  · refine Or.inr ⟨univ.filter (fun i => i.succ ∈ S), ?_⟩
    ext j; cases j using Fin.cases <;> simp [h]

lemma c0_erase_zero (B : Finset (Fin n)) : (c0 B).erase 0 = lift B := by
  ext j; cases j using Fin.cases <;> simp [Fin.succ_ne_zero]

lemma c0_erase_succ (B : Finset (Fin n)) (i : Fin n) : (c0 B).erase i.succ = c0 (B.erase i) := by
  ext j; cases j using Fin.cases <;> simp [(Fin.succ_ne_zero _).symm]

lemma lift_erase_succ (B : Finset (Fin n)) (i : Fin n) :
    (lift B).erase i.succ = lift (B.erase i) := by
  ext j; cases j using Fin.cases <;> simp

/-- Sets of `𝒜` containing `0`, with `0` removed and shifted down. -/
def top (𝒜 : Finset (Finset (Fin (n+1)))) : Finset (Finset (Fin n)) := univ.filter (c0 · ∈ 𝒜)

/-- Sets of `𝒜` avoiding `0`, shifted down. -/
def bot (𝒜 : Finset (Finset (Fin (n+1)))) : Finset (Finset (Fin n)) := univ.filter (lift · ∈ 𝒜)

@[simp] lemma mem_top {𝒜 : Finset (Finset (Fin (n+1)))} {B : Finset (Fin n)} :
    B ∈ top 𝒜 ↔ c0 B ∈ 𝒜 := by simp [top]

@[simp] lemma mem_bot {𝒜 : Finset (Finset (Fin (n+1)))} {B : Finset (Fin n)} :
    B ∈ bot 𝒜 ↔ lift B ∈ 𝒜 := by simp [bot]

/-- `c0` as an embedding of families. -/
def c0Emb : Finset (Fin n) ↪ Finset (Fin (n+1)) := ⟨c0, c0_injective⟩

/-- `lift` as an embedding of families. -/
def liftEmb : Finset (Fin n) ↪ Finset (Fin (n+1)) := ⟨lift, lift_injective⟩

lemma eq_glue (𝒜 : Finset (Finset (Fin (n+1)))) :
    𝒜 = (top 𝒜).map c0Emb ∪ (bot 𝒜).map liftEmb := by
  ext S
  rcases cases_c0_lift S with ⟨B, rfl⟩ | ⟨B, rfl⟩ <;> simp [c0Emb, liftEmb]

lemma top_glue (X Y : Finset (Finset (Fin n))) : top (X.map c0Emb ∪ Y.map liftEmb) = X := by
  ext B; simp [c0Emb, liftEmb]

lemma bot_glue (X Y : Finset (Finset (Fin n))) : bot (X.map c0Emb ∪ Y.map liftEmb) = Y := by
  ext B; simp [c0Emb, liftEmb]

lemma card_glue (X Y : Finset (Finset (Fin n))) :
    #(X.map c0Emb ∪ Y.map liftEmb) = #X + #Y := by
  rw [card_union_of_disjoint, card_map, card_map]
  rw [disjoint_left]
  intro S h1 h2
  simp only [mem_map, c0Emb, liftEmb, Function.Embedding.coeFn_mk] at h1 h2
  obtain ⟨A, -, rfl⟩ := h1
  obtain ⟨B, -, hB⟩ := h2
  exact lift_ne_c0 _ _ hB

lemma card_top_add_bot (𝒜 : Finset (Finset (Fin (n+1)))) : #𝒜 = #(top 𝒜) + #(bot 𝒜) := by
  conv_lhs => rw [eq_glue 𝒜]
  exact card_glue _ _

lemma top_upShadow (𝒜 : Finset (Finset (Fin (n+1)))) : top (∂⁺ 𝒜) = bot 𝒜 ∪ ∂⁺ (top 𝒜) := by
  ext B
  simp only [mem_top, mem_union, mem_bot, mem_upShadow_iff_erase_mem, Fin.exists_fin_succ,
    zero_mem_c0, true_and, c0_erase_zero, succ_mem_c0, c0_erase_succ]

lemma bot_upShadow (𝒜 : Finset (Finset (Fin (n+1)))) : bot (∂⁺ 𝒜) = ∂⁺ (bot 𝒜) := by
  ext B
  simp only [mem_bot, mem_upShadow_iff_erase_mem, Fin.exists_fin_succ, zero_notMem_lift,
    false_and, false_or, succ_mem_lift, lift_erase_succ]

lemma lexLT_c0_c0 {A B : Finset (Fin n)} : LexLT (c0 A) (c0 B) ↔ LexLT A B := by
  simp [LexLT, Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.succ_lt_succ_iff]

lemma lexLT_lift_lift {A B : Finset (Fin n)} : LexLT (lift A) (lift B) ↔ LexLT A B := by
  simp [LexLT, Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.succ_lt_succ_iff]

lemma lexLT_c0_lift (A B : Finset (Fin n)) : LexLT (c0 A) (lift B) :=
  ⟨0, zero_mem_c0 A, zero_notMem_lift B, fun b hb _ => by
    cases b using Fin.cases with
    | zero => exact absurd hb (zero_notMem_lift B)
    | succ j => exact Fin.succ_pos j⟩

lemma not_lexLT_lift_c0 (A B : Finset (Fin n)) : ¬ LexLT (lift A) (c0 B) := by
  rintro ⟨a, -, -, h⟩
  exact Fin.not_lt_zero a (h 0 (zero_mem_c0 B) (zero_notMem_lift A))

/-- A family of `(k+1)`-sets on `Fin (n+1)` is lex-initial iff its two halves are, and the
`0`-avoiding half is nonempty only if the `0`-containing half is everything. -/
lemma isLexInit_succ_iff {𝒜 : Finset (Finset (Fin (n+1)))} {k : ℕ} :
    IsLexInit 𝒜 (k+1) ↔ IsLexInit (top 𝒜) k ∧ IsLexInit (bot 𝒜) (k+1) ∧
      ((bot 𝒜).Nonempty → powersetCard k univ ⊆ top 𝒜) := by
  constructor
  · rintro ⟨hs, hi⟩
    refine ⟨⟨fun B hB => ?_, fun A B hA hBA hB => ?_⟩,
      ⟨fun B hB => ?_, fun A B hA hBA hB => ?_⟩, ?_⟩
    · have := hs (mem_top.mp hB); simpa using this
    · rw [mem_top] at hA ⊢; exact hi hA (lexLT_c0_c0.mpr hBA) (by simp [hB])
    · have := hs (mem_bot.mp hB); simpa using this
    · rw [mem_bot] at hA ⊢; exact hi hA (lexLT_lift_lift.mpr hBA) (by simp [hB])
    · rintro ⟨A, hA⟩ B hB
      rw [mem_powersetCard] at hB; rw [mem_bot] at hA; rw [mem_top]
      exact hi hA (lexLT_c0_lift _ _) (by simp [hB.2])
  · rintro ⟨⟨ts, ti⟩, ⟨bs, bi⟩, hfull⟩
    refine ⟨fun S hS => ?_, fun S T hS hTS hT => ?_⟩
    · rcases cases_c0_lift S with ⟨B, rfl⟩ | ⟨B, rfl⟩
      · have := ts (mem_top.mpr hS); simp [this]
      · have := bs (mem_bot.mpr hS); simp [this]
    · rcases cases_c0_lift S with ⟨A, rfl⟩ | ⟨A, rfl⟩ <;>
        rcases cases_c0_lift T with ⟨B, rfl⟩ | ⟨B, rfl⟩
      · rw [← mem_top]; exact ti (mem_top.mpr hS) (lexLT_c0_c0.mp hTS) (by simpa using hT)
      · exact absurd hTS (not_lexLT_lift_c0 _ _)
      · rw [← mem_top]
        exact hfull ⟨A, mem_bot.mpr hS⟩
          (mem_powersetCard.mpr ⟨subset_univ _, by simpa using hT⟩)
      · rw [← mem_bot]; exact bi (mem_bot.mpr hS) (lexLT_lift_lift.mp hTS) (by simpa using hT)

end Decomp

/-! ### Lemma 2 (F2), (F4): `sig` is the lex upper-shadow size -/

/-- **Lemma 2 (F2) + (F4)** (`lem-lex-rank1`). The upper shadow of a lex-initial family `𝒜` of
`k`-subsets of `Fin n` has `sig n k #𝒜` elements and is a lex-initial family of `(k+1)`-sets. -/
theorem lexInit_upShadow : ∀ (n k : ℕ) (𝒜 : Finset (Finset (Fin n))), IsLexInit 𝒜 k →
    #(∂⁺ 𝒜) = sig n k #𝒜 ∧ IsLexInit (∂⁺ 𝒜) (k+1)
  | 0, k, 𝒜, _ => by
    have : ∂⁺ 𝒜 = ∅ := by
      ext t
      simp only [mem_upShadow_iff, notMem_empty, iff_false]
      rintro ⟨s, -, a, -, -⟩; exact a.elim0
    rw [this]
    exact ⟨by simp [sig], isLexInit_empty _⟩
  | n+1, k, 𝒜, h𝒜 => by
    have IH := lexInit_upShadow n
    have hcard : #(∂⁺ 𝒜) = #(bot 𝒜 ∪ ∂⁺ (top 𝒜)) + #(∂⁺ (bot 𝒜)) := by
      rw [card_top_add_bot (∂⁺ 𝒜), top_upShadow, bot_upShadow]
    have hA := card_top_add_bot 𝒜
    rcases k with _ | k
    · -- degree 0: `𝒜 ⊆ {∅}`
      have htop : top 𝒜 = ∅ := by
        ext B; simp only [mem_top, notMem_empty, iff_false]
        intro hB; have := h𝒜.1 hB; simp at this
      have hbs : ((bot 𝒜 : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Sized 0 :=
        fun B hB => by have := h𝒜.1 (mem_bot.mp hB); simpa using this
      obtain ⟨hb1, hb2⟩ := IH 0 (bot 𝒜) (isLexInit_of_sized_zero hbs)
      rw [htop, upShadow_empty, union_empty] at hcard
      rw [htop, card_empty, zero_add] at hA
      have htop' : top (∂⁺ 𝒜) = bot 𝒜 := by rw [top_upShadow, htop, upShadow_empty, union_empty]
      refine ⟨?_, isLexInit_succ_iff.mpr ⟨?_, ?_, ?_⟩⟩
      · rw [hcard, hA, hb1]
        have : #(bot 𝒜) ≤ 1 := by have := hbs.card_le; simpa using this
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> simp [sig, sig_zero]
      · rw [htop']; exact isLexInit_of_sized_zero hbs
      · rw [bot_upShadow]; exact hb2
      · intro hne B hB
        rw [htop']
        rw [bot_upShadow] at hne
        have hB0 : B = ∅ := by simpa using hB
        obtain ⟨X, hX⟩ := hne
        obtain ⟨Y, hY, -⟩ := exists_subset_of_mem_upShadow hX
        have : Y = ∅ := card_eq_zero.mp (hbs hY)
        subst hB0; subst this; exact hY
    · obtain ⟨ht, hb, hfull⟩ := isLexInit_succ_iff.mp h𝒜
      obtain ⟨ht1, ht2⟩ := IH k (top 𝒜) ht
      obtain ⟨hb1, hb2⟩ := IH (k+1) (bot 𝒜) hb
      rcases (bot 𝒜).eq_empty_or_nonempty with hbe | hbne
      · have hle : #(top 𝒜) ≤ n.choose k := by have := ht.1.card_le; simpa using this
        rw [hbe, empty_union, upShadow_empty, card_empty, add_zero] at hcard
        rw [hbe, card_empty, add_zero] at hA
        refine ⟨by rw [hcard, ht1, hA, sig_R1 hle], isLexInit_succ_iff.mpr ⟨?_, ?_, ?_⟩⟩
        · rw [top_upShadow, hbe, empty_union]; exact ht2
        · rw [bot_upShadow, hbe, upShadow_empty]; exact isLexInit_empty _
        · rw [bot_upShadow, hbe, upShadow_empty]; intro h; exact absurd h not_nonempty_empty
      · have htop : top 𝒜 = powersetCard k univ := by
          refine subset_antisymm (fun B hB => ?_) (hfull hbne)
          exact mem_powersetCard.mpr ⟨subset_univ _, ht.1 hB⟩
        have hunion : bot 𝒜 ∪ ∂⁺ (top 𝒜) = powersetCard (k+1) univ := by
          rw [htop, upShadow_powersetCard]
          apply union_eq_right.mpr
          intro B hB; exact mem_powersetCard.mpr ⟨subset_univ _, hb.1 hB⟩
        have htc : #(top 𝒜) = n.choose k := by
          rw [htop, card_powersetCard, card_univ, Fintype.card_fin]
        refine ⟨?_, isLexInit_succ_iff.mpr ⟨?_, ?_, ?_⟩⟩
        · rw [hcard, hunion, card_powersetCard, card_univ, Fintype.card_fin, hb1, hA, htc,
            sig_R2' rfl]
        · rw [top_upShadow, hunion]; exact isLexInit_powersetCard _
        · rw [bot_upShadow]; exact hb2
        · intro _; rw [top_upShadow, hunion]

/-- Lex-initial families of every size `t ≤ C(n,k)` exist (so `Lₙ(k,t)` is defined). -/
theorem exists_isLexInit : ∀ (n k t : ℕ), t ≤ n.choose k →
    ∃ 𝒜 : Finset (Finset (Fin n)), IsLexInit 𝒜 k ∧ #𝒜 = t
  | n, 0, t, ht => by
    rw [Nat.choose_zero_right] at ht
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
    · exact ⟨∅, isLexInit_empty _, rfl⟩
    · exact ⟨{∅}, isLexInit_of_sized_zero (by simp), rfl⟩
  | 0, k+1, t, ht => by
    rw [Nat.choose_zero_succ, Nat.le_zero] at ht
    subst ht; exact ⟨∅, isLexInit_empty _, rfl⟩
  | n+1, k+1, t, ht => by
    rw [Nat.choose_succ_succ'] at ht
    rcases le_or_gt t (n.choose k) with h | h
    · obtain ⟨X, hX, hXc⟩ := exists_isLexInit n k t h
      refine ⟨X.map c0Emb ∪ (∅ : Finset (Finset (Fin n))).map liftEmb,
        isLexInit_succ_iff.mpr ?_, by rw [card_glue, hXc, card_empty, add_zero]⟩
      rw [top_glue, bot_glue]
      exact ⟨hX, isLexInit_empty _, fun h => absurd h not_nonempty_empty⟩
    · obtain ⟨Y, hY, hYc⟩ := exists_isLexInit n (k+1) (t - n.choose k) (by omega)
      refine ⟨(powersetCard k univ).map c0Emb ∪ Y.map liftEmb, isLexInit_succ_iff.mpr ?_, ?_⟩
      · rw [top_glue, bot_glue]
        exact ⟨isLexInit_powersetCard _, hY, fun _ => subset_refl _⟩
      · rw [card_glue, hYc, card_powersetCard, card_univ, Fintype.card_fin]; omega

/-! ### Translation to colex (note §3.3) and Theorem KK -/

section Translate
variable {n : ℕ}

/-- The note's §3.3 map `S ↦ ρ([n] ∖ S)`: here `φ s = {a : rev a ∉ s}`. -/
def phi (s : Finset (Fin n)) : Finset (Fin n) := univ.filter (fun a => a.rev ∉ s)

@[simp] lemma mem_phi {s : Finset (Fin n)} {a : Fin n} : a ∈ phi s ↔ a.rev ∉ s := by simp [phi]

@[simp] lemma phi_phi (s : Finset (Fin n)) : phi (phi s) = s := by ext a; simp

lemma phi_injective : Function.Injective (phi (n := n)) :=
  Function.LeftInverse.injective phi_phi

lemma card_phi (s : Finset (Fin n)) : #(phi s) = n - #s := by
  have : phi s = (s.image Fin.rev)ᶜ := by
    ext a; simp only [mem_phi, mem_compl, mem_image, not_exists, not_and]
    constructor
    · rintro h b hb rfl; rw [Fin.rev_rev] at h; exact h hb
    · intro h ha; exact h _ ha (Fin.rev_rev a)
  rw [this, card_compl, card_image_of_injective _ Fin.rev_injective, Fintype.card_fin]

lemma lexLT_iff_colex {s t : Finset (Fin n)} :
    LexLT s t ↔ toColex (phi s) < toColex (phi t) := by
  rw [Colex.toColex_lt_toColex_iff_exists_forall_lt]
  simp only [mem_phi, not_not]
  constructor
  · rintro ⟨a, has, hat, h⟩
    refine ⟨a.rev, by rwa [Fin.rev_rev], by rwa [Fin.rev_rev], fun b hbs hbt => ?_⟩
    have := h b.rev hbt hbs
    rw [← Fin.rev_lt_rev, Fin.rev_rev]; exact this
  · rintro ⟨a, hat, has, h⟩
    refine ⟨a.rev, has, hat, fun b hbt hbs => ?_⟩
    have := h b.rev (by rwa [Fin.rev_rev]) (by rwa [Fin.rev_rev])
    rw [← Fin.rev_lt_rev, Fin.rev_rev]; exact this

lemma mem_image_phi {𝒜 : Finset (Finset (Fin n))} {u : Finset (Fin n)} :
    u ∈ 𝒜.image phi ↔ phi u ∈ 𝒜 := by
  constructor
  · intro h; obtain ⟨s, hs, rfl⟩ := mem_image.mp h; rwa [phi_phi]
  · intro h; exact mem_image.mpr ⟨phi u, h, phi_phi u⟩

lemma phi_insert (a : Fin n) (u : Finset (Fin n)) : phi (insert a u) = (phi u).erase a.rev := by
  ext b
  simp only [mem_phi, mem_insert, not_or, mem_erase]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [h, Fin.rev_rev]), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [← h, Fin.rev_rev]), h2⟩

/-- Complement-reversal turns upper shadows into lower shadows. -/
lemma shadow_image_phi (𝒜 : Finset (Finset (Fin n))) :
    ∂ (𝒜.image phi) = (∂⁺ 𝒜).image phi := by
  ext u
  rw [mem_shadow_iff_insert_mem, mem_image_phi, mem_upShadow_iff_erase_mem]
  simp only [mem_image_phi, phi_insert, mem_phi]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a.rev, by rwa [Fin.rev_rev], h⟩
  · rintro ⟨b, hb, h⟩; exact ⟨b.rev, hb, by rwa [Fin.rev_rev]⟩

lemma isInitSeg_image_phi {𝒜 : Finset (Finset (Fin n))} {k : ℕ} (hk : k ≤ n)
    (h : IsLexInit 𝒜 k) : Colex.IsInitSeg (𝒜.image phi) (n - k) := by
  refine ⟨fun u hu => ?_, fun S T hS hT => ?_⟩
  · rw [mem_coe, mem_image_phi] at hu
    have := card_phi (phi u); rw [phi_phi, h.1 hu] at this; omega
  · rw [mem_image_phi] at hS ⊢
    refine h.2 hS ?_ ?_
    · rw [lexLT_iff_colex, phi_phi, phi_phi]; exact hT.1
    · rw [card_phi, hT.2]; omega
/-- **Theorem KK, comparison form.** A lex-initial family has the smallest upper shadow among all
families of `k`-sets of at least its size. -/
theorem kk_lex {𝒜 ℒ : Finset (Finset (Fin n))} {k : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized k) (hℒ : IsLexInit ℒ k) (hc : #ℒ ≤ #𝒜) :
    #(∂⁺ ℒ) ≤ #(∂⁺ 𝒜) := by
  by_cases hk : k ≤ n
  · have himg : ∀ 𝒞 : Finset (Finset (Fin n)), #(𝒞.image phi) = #𝒞 :=
      fun 𝒞 => card_image_of_injective _ phi_injective
    have hsz : ((𝒜.image phi : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Sized (n - k) := by
      intro u hu
      rw [mem_coe, mem_image_phi] at hu
      have := card_phi (phi u); rw [phi_phi, h𝒜 hu] at this; omega
    have := kruskal_katona hsz (by rw [himg, himg]; exact hc) (isInitSeg_image_phi hk hℒ)
    rwa [shadow_image_phi, shadow_image_phi, himg, himg] at this
  · have := hℒ.1.card_le; rw [Fintype.card_fin, Nat.choose_eq_zero_of_lt (by omega)] at this
    rw [card_eq_zero.mp (by omega : #ℒ = 0), upShadow_empty, card_empty]
    exact Nat.zero_le _

/-- **Theorem KK** (`thm-kk-rank1`, Kruskal 1963, Katona 1968, in the note's lex/upper-shadow
form). For every family `𝒜` of `k`-subsets of `Fin n`, `|∇𝒜| ≥ σₙ(k, |𝒜|)`. -/
theorem thm_kk_rank1 {𝒜 : Finset (Finset (Fin n))} {k : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized k) : sig n k #𝒜 ≤ #(∂⁺ 𝒜) := by
  have hle : #𝒜 ≤ n.choose k := by have := h𝒜.card_le; simpa using this
  obtain ⟨ℒ, hℒ, hℒc⟩ := exists_isLexInit n k #𝒜 hle
  rw [← hℒc, ← (lexInit_upShadow n k ℒ hℒ).1]
  exact kk_lex h𝒜 hℒ hℒc.le

end Translate

/-! ### Greedy component shadow bounds -/

section Module
variable {n : ℕ}

/-- A component of exterior degree `k ∈ ℤ`: a family of `k`-sets, empty if `k < 0`. -/
def Component (k : ℤ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  (𝒜 : Set (Finset (Fin n))).Sized k.toNat ∧ (k < 0 → 𝒜 = ∅)

lemma Component.card_le {k : ℤ} {𝒜 : Finset (Finset (Fin n))} (h : Component k 𝒜) :
    #𝒜 ≤ capZ n k := by
  unfold capZ
  split_ifs with hk
  · have := h.1.card_le; simpa using this
  · rw [h.2 (by omega), card_empty]

lemma Component.costZ_le {k : ℤ} {𝒜 : Finset (Finset (Fin n))} (h : Component k 𝒜) :
    costZ n k #𝒜 ≤ #(∂⁺ 𝒜) := by
  unfold costZ
  split_ifs with hk
  · exact thm_kk_rank1 h.1
  · exact Nat.zero_le _

/-- **Module shadow bound** (combinatorial core of Theorem 6): for components with
`k₁ ≥ ⋯ ≥ k_r`, `∑ᵢ |∇𝒜ᵢ| ≥ ∑ᵢ cᵢ(t*ᵢ)`, `t*` the greedy split of `T = ∑ᵢ |𝒜ᵢ|`. -/
theorem module_shadow_ge_greedy (ks : List ℤ) (hks : ks.Pairwise (· ≥ ·))
    (𝒜s : List (Finset (Finset (Fin n)))) (h : List.Forall₂ Component ks 𝒜s) :
    cost (costZ n) ks (greedy (capZ n) ks (𝒜s.map card).sum) ≤
      (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum := by
  have hF : Feasible (capZ n) ks (𝒜s.map card) := by
    clear hks
    induction h with
    | nil => exact List.Forall₂.nil
    | cons h _ ih => exact List.Forall₂.cons h.card_le ih
  have hC : cost (costZ n) ks (𝒜s.map card) ≤ (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum := by
    clear hF hks
    induction h with
    | nil => simp
    | cons h _ ih => simp only [List.map_cons, cost_cons, List.sum_cons]; have := h.costZ_le; omega
  exact (prop_greedy n ks hks _ hF).trans hC

/-- Every feasible split is realised by lex-initial components, whose shadow sizes add up to its
cost; in particular (`ts = greedy …`) the bound of `module_shadow_ge_greedy` is attained by the
lex_F segment. -/
theorem exists_lexInit_components (ks : List ℤ) (ts : List ℕ) (h : Feasible (capZ n) ks ts) :
    ∃ 𝒜s : List (Finset (Finset (Fin n))),
      List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s ∧
      𝒜s.map card = ts ∧ (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum = cost (costZ n) ks ts := by
  induction h with
  | nil => exact ⟨[], List.Forall₂.nil, rfl, by simp⟩
  | @cons k t ks ts ht _ ih =>
    obtain ⟨𝒜s, h1, h2, h3⟩ := ih
    by_cases hk : 0 ≤ k
    · simp only [capZ, hk, ↓reduceIte] at ht
      obtain ⟨𝒜, h𝒜, h𝒜c⟩ := exists_isLexInit n k.toNat t ht
      refine ⟨𝒜 :: 𝒜s, List.Forall₂.cons ⟨⟨h𝒜.1, fun h => by omega⟩, h𝒜⟩ h1, by simp [h2, h𝒜c], ?_⟩
      simp only [List.map_cons, List.sum_cons, h3, cost_cons, costZ, hk, ↓reduceIte,
        (lexInit_upShadow n _ 𝒜 h𝒜).1, h𝒜c]
    · simp only [capZ, hk, ↓reduceIte, Nat.le_zero] at ht
      subst ht
      refine ⟨∅ :: 𝒜s, List.Forall₂.cons ⟨⟨by simp, fun _ => rfl⟩, isLexInit_empty _⟩ h1,
        by simp [h2], ?_⟩
      simp [h3, costZ, hk]

end Module

end D5.S3.Combinatorics.Kozlov.LexCompression
