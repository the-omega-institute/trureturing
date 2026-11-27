/- GID: D5/S3/Combinatorics/Kozlov/LexPositionShadow
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Kozlov/LexPositionShadow
   mirror-E: none(waiver:finite-lex-shadow-theory)
   anchors: []
   utility: none
   digest: Position-first lex segments are nested and closed under degreewise upper shadows. -/

import D5.S3.Combinatorics.Kozlov.LexFamilyShadow

-- Source: https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/ModuleKK/LexF.lean
/-
Upstream pins: Lean v4.34.0-rc2, Mathlib 3a8a89422e16d67b7ae57698f6d96e389e4d4202.
When the project's pinned Mathlib provides an equivalent declaration,
replace the transplanted declaration with a direct import and use that result.

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

/-! ### Greedy-shaped vectors -/

section Shape

variable {ι : Type*}

/-- `us` is *greedy-shaped* for the capacities `C` on the degree list `ks`: `uᵢ ≤ C kᵢ`, and
positive mass after position `i` forces `uᵢ = C kᵢ`. These are exactly the greedy vectors
(`greedyShape_greedy`, `GreedyShape.eq_greedy`). -/
def GreedyShape (C : ι → ℕ) : List ι → List ℕ → Prop
  | [], [] => True
  | k :: ks, u :: us => u ≤ C k ∧ (0 < us.sum → u = C k) ∧ GreedyShape C ks us
  | _, _ => False

lemma greedyShape_greedy (C : ι → ℕ) (ks : List ι) (T : ℕ) :
    GreedyShape C ks (greedy C ks T) := by
  induction ks generalizing T with
  | nil => simp [greedy, GreedyShape]
  | cons k ks ih =>
    simp only [greedy, GreedyShape]
    refine ⟨min_le_right _ _, fun h => ?_, ih _⟩
    rw [greedy_sum] at h
    omega

lemma GreedyShape.eq_greedy {C : ι → ℕ} : ∀ {ks : List ι} {us : List ℕ},
    GreedyShape C ks us → us = greedy C ks us.sum
  | [], [], _ => rfl
  | k :: ks, u :: us, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have hmin : min (u + us.sum) (C k) = u := by
      rcases Nat.eq_zero_or_pos us.sum with h | h
      · omega
      · have := h2 h; omega
    simp only [List.sum_cons, greedy, hmin, Nat.add_sub_cancel_left]
    exact congrArg _ h3.eq_greedy
  | [], _ :: _, h => by simp [GreedyShape] at h
  | _ :: _, [], h => by simp [GreedyShape] at h

lemma greedy_mono (C : ι → ℕ) (ks : List ι) {T T' : ℕ} (h : T ≤ T') :
    List.Forall₂ (· ≤ ·) (greedy C ks T) (greedy C ks T') := by
  induction ks generalizing T T' with
  | nil => exact List.Forall₂.nil
  | cons k ks ih =>
    simp only [greedy]
    exact List.Forall₂.cons (by omega) (ih (by omega))

end Shape

/-! ### Capacities and costs of integer degrees -/
section CapCost

/-- `T_ℓ(j)` of §`sec-setup`: the total capacity `∑_{i > ℓ} C(n, kᵢ)` of the components after
position `ℓ` (1-indexed in the paper; here the components `ks.drop ℓ`). `tailCap n ks 0` is
`dim F_j`, and `tailCap n (ks.map (· + 1)) ℓ` is `T_ℓ(j+1)`. -/
def tailCap (n : ℕ) (ks : List ℤ) (ℓ : ℕ) : ℕ := ((ks.drop ℓ).map (capZ n)).sum

variable {n : ℕ}
lemma tailCap_zero (ks : List ℤ) : tailCap n ks 0 = (ks.map (capZ n)).sum := by simp [tailCap]

lemma costZ_zero (k : ℤ) : costZ n k 0 = 0 := by
  unfold costZ; split_ifs <;> simp [sig_zero]

/-- `ωₙ(k,t) ≤ C(n,k+1)`: a lex shadow is a family of `(k+1)`-sets. -/
lemma sig_le_choose_succ (n k t : ℕ) (ht : t ≤ n.choose k) : sig n k t ≤ n.choose (k + 1) := by
  obtain ⟨𝒜, h𝒜, rfl⟩ := exists_isLexInit n k t ht
  rw [← (lexInit_upShadow n k 𝒜 h𝒜).1]
  have := (lexInit_upShadow n k 𝒜 h𝒜).2.1.card_le
  simpa using this

lemma capZ_succ_of_nonneg {k : ℤ} (hk : 0 ≤ k) : capZ n (k + 1) = n.choose (k.toNat + 1) := by
  have e : (k + 1).toNat = k.toNat + 1 := by omega
  simp only [capZ, show (0 : ℤ) ≤ k + 1 by omega, ↓reduceIte, e]

lemma costZ_le_capZ_succ {k : ℤ} {t : ℕ} (ht : t ≤ capZ n k) : costZ n k t ≤ capZ n (k + 1) := by
  by_cases hk : 0 ≤ k
  · rw [capZ_succ_of_nonneg hk]
    simp only [capZ, costZ, hk, ↓reduceIte] at ht ⊢
    exact sig_le_choose_succ n _ t ht
  · simp only [costZ, hk, ↓reduceIte]; exact Nat.zero_le _

/-- A full component of degree `k ≥ 0` has full shadow (`lem-lex-rank1`(1)). -/
lemma costZ_capZ {k : ℤ} (hk : 0 ≤ k) : costZ n k (capZ n k) = capZ n (k + 1) := by
  rw [capZ_succ_of_nonneg hk]
  simp only [capZ, costZ, hk, ↓reduceIte, sig_full]

lemma cost_pos : ∀ (ks : List ℤ) (us : List ℕ), 0 < cost (costZ n) ks us →
    (∃ k ∈ ks, 0 ≤ k) ∧ 0 < us.sum
  | [], _, h => by simp at h
  | _ :: _, [], h => by simp [cost] at h
  | k :: ks, u :: us, h => by
    rw [cost_cons] at h
    by_cases h0 : 0 < costZ n k u
    · have hk : 0 ≤ k := by
        by_contra hk; simp [costZ, hk] at h0
      have hu : 0 < u := by
        by_contra hu; rw [show u = 0 by omega, costZ_zero] at h0; exact lt_irrefl _ h0
      exact ⟨⟨k, List.mem_cons_self, hk⟩, by simp only [List.sum_cons]; omega⟩
    · obtain ⟨⟨k', hk', h'⟩, hs⟩ := cost_pos ks us (by omega)
      exact ⟨⟨k', List.mem_cons_of_mem _ hk', h'⟩, by simp only [List.sum_cons]; omega⟩
/-- The shadow sizes of the greedy vector, `(cᵢ(t*ᵢ))ᵢ`, are greedy-shaped for the capacities of
the next degree (the numerical half of `lem-lexF-shadow`). -/
lemma greedyShape_shadow (n : ℕ) : ∀ (ks : List ℤ), ks.Pairwise (· ≥ ·) → ∀ t,
    GreedyShape (capZ n) (ks.map (· + 1)) (List.zipWith (costZ n) ks (greedy (capZ n) ks t))
  | [], _, _ => by simp [greedy, GreedyShape]
  | k :: ks, hks, t => by
    rw [List.pairwise_cons] at hks
    simp only [greedy, List.map_cons, List.zipWith_cons_cons, GreedyShape]
    refine ⟨costZ_le_capZ_succ (min_le_right _ _), fun hpos => ?_,
      greedyShape_shadow n ks hks.2 _⟩
    obtain ⟨⟨k', hk', hk'0⟩, hs⟩ := cost_pos ks _ hpos
    rw [greedy_sum] at hs
    have hm : min t (capZ n k) = capZ n k := by omega
    rw [hm]
    exact costZ_capZ (le_trans hk'0 (hks.1 k' hk'))

end CapCost

/-! ### Target 1: `lexF` segments -/

section LexF

variable {n : ℕ}

/-- **`lexF` segment** (§`sec-lex`): the `lexF` segment of size `t` of `Mon_j(F)`, for the
exterior degrees `ks` (`kᵢ = j − dᵢ`, `k₁ ≥ ⋯ ≥ k_r`). In the paper's concrete form ("fills
components `1,…,ℓ−1`, takes a lex-initial segment of component `ℓ`, and leaves the rest empty"):
the component sizes are the greedy vector `greedy (capZ n) ks t` (capacities `Cᵢ = C(n,kᵢ)`), and
each component is a lex-initial family of `kᵢ`-sets (empty if `kᵢ < 0`). For `t ≥ dim F_j` it is
all of `Mon_j(F)` (`IsLexFSeg.card_sum`). -/
def IsLexFSeg (n : ℕ) (ks : List ℤ) (t : ℕ) (𝒜s : List (Finset (Finset (Fin n)))) : Prop :=
  List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s ∧
    𝒜s.map card = greedy (capZ n) ks t

/-- `lexF` segments of every size exist. -/
theorem exists_isLexFSeg (n : ℕ) (ks : List ℤ) (t : ℕ) : ∃ 𝒜s, IsLexFSeg n ks t 𝒜s := by
  obtain ⟨𝒜s, h1, h2, -⟩ :=
    exists_lexInit_components (n := n) ks _ (greedy_feasible (capZ n) ks t)
  exact ⟨𝒜s, h1, h2⟩
/-- The size of the `lexF` segment of size `t` is `min t (dim F_j)`. -/
lemma IsLexFSeg.card_sum {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) : (𝒜s.map card).sum = min t (tailCap n ks 0) := by
  rw [h.2, greedy_sum, tailCap_zero]
/-- A `lexF` segment is the `lexF` segment of its own size. -/
lemma IsLexFSeg.resize {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) : IsLexFSeg n ks (𝒜s.map card).sum 𝒜s := by
  refine ⟨h.1, ?_⟩
  have := (greedyShape_greedy (capZ n) ks t).eq_greedy
  rw [← h.2] at this
  exact this

/-- Lex-initial families of the same degree are nested by size. -/
lemma isLexInit_subset_of_card_le {𝒜 ℬ : Finset (Finset (Fin n))} {k : ℕ} (h𝒜 : IsLexInit 𝒜 k)
    (hℬ : IsLexInit ℬ k) (hc : #𝒜 ≤ #ℬ) : 𝒜 ⊆ ℬ := by
  by_cases hk : k ≤ n
  · have himg : ∀ 𝒞 : Finset (Finset (Fin n)), #(𝒞.image phi) = #𝒞 :=
      fun 𝒞 => card_image_of_injective _ phi_injective
    rcases (isInitSeg_image_phi hk h𝒜).total (isInitSeg_image_phi hk hℬ) with h | h
    · exact (image_subset_image_iff phi_injective).mp h
    · have e := eq_of_subset_of_card_le h (by rw [himg, himg]; exact hc)
      refine (image_subset_image_iff phi_injective).mp ?_
      rw [e]
  · have e : ∀ 𝒞 : Finset (Finset (Fin n)), IsLexInit 𝒞 k → 𝒞 = ∅ := fun 𝒞 h𝒞 => by
      have := h𝒞.1.card_le; rw [Fintype.card_fin, Nat.choose_eq_zero_of_lt (by omega)] at this
      exact card_eq_zero.mp (by omega)
    rw [e 𝒜 h𝒜]; exact empty_subset _

lemma forall2_subset_of_le {ks : List ℤ} {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h1 : List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s)
    (h2 : List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks ℬs)
    (hle : List.Forall₂ (· ≤ ·) (𝒜s.map card) (ℬs.map card)) :
    List.Forall₂ (· ⊆ ·) 𝒜s ℬs := by
  induction h1 generalizing ℬs with
  | nil => cases h2; exact List.Forall₂.nil
  | cons ha _ ih =>
    cases h2 with
    | cons hb h2' =>
      simp only [List.map_cons] at hle
      cases hle with
      | cons hc hle' => exact List.Forall₂.cons (isLexInit_subset_of_card_le ha.2 hb.2 hc) (ih h2' hle')

/-- `lexF` segments of one degree are nested by size ("Segments of one degree are nested by size",
proof of `lem-lexF-shadow`). -/
theorem IsLexFSeg.forall2_subset {ks : List ℤ} {t t' : ℕ}
    {𝒜s ℬs : List (Finset (Finset (Fin n)))} (h𝒜 : IsLexFSeg n ks t 𝒜s)
    (hℬ : IsLexFSeg n ks t' ℬs) (hle : (𝒜s.map card).sum ≤ (ℬs.map card).sum) :
    List.Forall₂ (· ⊆ ·) 𝒜s ℬs := by
  have hm := greedy_mono (capZ n) ks hle
  rw [← h𝒜.resize.2, ← hℬ.resize.2] at hm
  exact forall2_subset_of_le h𝒜.1 hℬ.1 hm

/-! #### The order-theoretic definition: initial segments of `Mon_j(F)` for `>_{lexF}` -/

/-- `𝒜s ⊆ Mon_j(F)` is an **initial segment of `Mon_j(F)` for the position-over-term order
`>_{lexF}`** (§`sec-lex`, the paper's definition of a `lexF` segment, following Amata–Crupi
Section 2). The monomials of `Mon_j(F)` are the pairs `(i, u)`, `u` a `kᵢ`-subset of `[n]` with
`kᵢ ≥ 0` (here `u ∈ 𝒜s.getD i ∅`, components indexed from `0`), and `u gᵢ >_{lexF} v g_l` iff
`i < l`, or `i = l` and `u >_lex v` (`LexLT u v`). `isLexFInitial_iff` shows that this is the
concrete form `IsLexFSeg` (the paper's "Concretely, a `lexF` segment fills components
`1,…,ℓ−1`, takes a lex-initial segment of component `ℓ`, and leaves the rest empty"). -/
def IsLexFInitial (n : ℕ) (ks : List ℤ) (𝒜s : List (Finset (Finset (Fin n)))) : Prop :=
  List.Forall₂ Component ks 𝒜s ∧
    ∀ ⦃i l : ℕ⦄ ⦃u v : Finset (Fin n)⦄, v ∈ 𝒜s.getD l ∅ →
      i < ks.length → 0 ≤ ks.getD i 0 → #u = (ks.getD i 0).toNat →
      (i < l ∨ (i = l ∧ LexLT u v)) → u ∈ 𝒜s.getD i ∅

lemma isLexFInitial_cons_iff {k : ℤ} {ks : List ℤ} {𝒜 : Finset (Finset (Fin n))}
    {𝒜s : List (Finset (Finset (Fin n)))} :
    IsLexFInitial n (k :: ks) (𝒜 :: 𝒜s) ↔
      (Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ∧
      ((∃ l, (𝒜s.getD l ∅).Nonempty) → ∀ u : Finset (Fin n), 0 ≤ k → #u = k.toNat → u ∈ 𝒜) ∧
      IsLexFInitial n ks 𝒜s := by
  constructor
  · rintro ⟨hF, hI⟩
    rw [List.forall₂_cons] at hF
    refine ⟨⟨hF.1, hF.1.1, fun s t hs hts ht => ?_⟩, fun ⟨l, v, hv⟩ u hk hu => ?_, ⟨hF.2, ?_⟩⟩
    · have hk : 0 ≤ k := by
        by_contra hk; rw [hF.1.2 (by omega)] at hs; simp at hs
      exact hI (i := 0) (l := 0) (v := s) (by simpa using hs) (by simp) (by simpa using hk)
        (by simpa using ht) (Or.inr ⟨rfl, hts⟩)
    · exact hI (i := 0) (l := l + 1) (v := v) (by simpa using hv) (by simp) (by simpa using hk)
        (by simpa using hu) (Or.inl (by omega))
    · intro i l u v hv hi hk hu hil
      exact hI (i := i + 1) (l := l + 1) (v := v) (by simpa using hv) (by simpa using hi)
        (by simpa using hk) (by simpa using hu)
        (hil.imp (fun h => by omega) (fun h => ⟨by omega, h.2⟩))
  · rintro ⟨⟨hC, hL⟩, hfull, hF, hI⟩
    refine ⟨List.Forall₂.cons hC hF, fun i l u v hv hi hk hu hil => ?_⟩
    rcases i with _ | i <;> rcases l with _ | l
    · simp only [List.getD_cons_zero] at hv hk hu ⊢
      rcases hil with h | ⟨-, h⟩
      · omega
      · exact hL.2 hv h hu
    · simp only [List.getD_cons_zero, List.getD_cons_succ] at hv hk hu ⊢
      exact hfull ⟨l, v, hv⟩ u hk hu
    · rcases hil with h | ⟨h, -⟩ <;> omega
    · simp only [List.getD_cons_succ, List.length_cons] at hv hi hk hu ⊢
      exact hI hv (by omega) hk hu (hil.imp (fun h => by omega) (fun h => ⟨by omega, h.2⟩))

lemma exists_getD_nonempty_iff : ∀ (𝒜s : List (Finset (Finset (Fin n)))),
    (∃ l, (𝒜s.getD l ∅).Nonempty) ↔ 0 < (𝒜s.map card).sum
  | [] => by simp
  | 𝒜 :: 𝒜s => by
    rw [List.map_cons, List.sum_cons]
    constructor
    · rintro ⟨l, hl⟩
      rcases l with _ | l
      · simp only [List.getD_cons_zero] at hl; have := hl.card_pos; omega
      · simp only [List.getD_cons_succ] at hl
        have := (exists_getD_nonempty_iff 𝒜s).mp ⟨l, hl⟩; omega
    · intro h
      by_cases h𝒜 : 0 < #𝒜
      · exact ⟨0, by simpa using card_pos.mp h𝒜⟩
      · obtain ⟨l, hl⟩ := (exists_getD_nonempty_iff 𝒜s).mpr (by omega)
        exact ⟨l + 1, by simpa using hl⟩

/-- A component is full (contains every monomial of its degree) iff it has `C(n,k)` elements. -/
lemma Component.full_iff {k : ℤ} {𝒜 : Finset (Finset (Fin n))} (h : Component k 𝒜) :
    (∀ u : Finset (Fin n), 0 ≤ k → #u = k.toNat → u ∈ 𝒜) ↔ #𝒜 = capZ n k := by
  by_cases hk : 0 ≤ k
  · have hsub : 𝒜 ⊆ powersetCard k.toNat univ :=
      fun s hs => mem_powersetCard.mpr ⟨subset_univ _, h.1 hs⟩
    simp only [capZ, hk, ↓reduceIte]
    constructor
    · intro hf
      have : 𝒜 = powersetCard k.toNat univ :=
        subset_antisymm hsub (fun u hu => hf u (by trivial) (mem_powersetCard.mp hu).2)
      rw [this, card_powersetCard, card_univ, Fintype.card_fin]
    · intro hc u _ hu
      have := eq_of_subset_of_card_le hsub
        (by rw [card_powersetCard, card_univ, Fintype.card_fin, hc])
      rw [this]; exact mem_powersetCard.mpr ⟨subset_univ _, hu⟩
  · simp [capZ, hk, h.2 (by omega)]

lemma isLexFInitial_iff_shape : ∀ (ks : List ℤ) (𝒜s : List (Finset (Finset (Fin n)))),
    IsLexFInitial n ks 𝒜s ↔
      List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s ∧
        GreedyShape (capZ n) ks (𝒜s.map card)
  | [], [] => by simp [IsLexFInitial, GreedyShape]
  | [], _ :: _ => by simp [IsLexFInitial]
  | _ :: _, [] => by simp [IsLexFInitial]
  | k :: ks, 𝒜 :: 𝒜s => by
    rw [isLexFInitial_cons_iff, isLexFInitial_iff_shape ks 𝒜s, List.forall₂_cons]
    simp only [List.map_cons, GreedyShape]
    constructor
    · rintro ⟨hCL, hfull, hF, hS⟩
      exact ⟨⟨hCL, hF⟩, hCL.1.card_le,
        fun hpos => hCL.1.full_iff.mp (hfull ((exists_getD_nonempty_iff 𝒜s).mpr hpos)), hS⟩
    · rintro ⟨⟨hCL, hF⟩, -, hpos, hS⟩
      exact ⟨hCL, fun hne => hCL.1.full_iff.mpr (hpos ((exists_getD_nonempty_iff 𝒜s).mp hne)),
        hF, hS⟩

/-- **The paper's definition of a `lexF` segment agrees with the concrete one**: `𝒜s` is an
initial segment of `Mon_j(F)` for `>_{lexF}` iff it is the `lexF` segment (`IsLexFSeg`) of its own
size. -/
theorem isLexFInitial_iff {ks : List ℤ} {𝒜s : List (Finset (Finset (Fin n)))} :
    IsLexFInitial n ks 𝒜s ↔ IsLexFSeg n ks (𝒜s.map card).sum 𝒜s := by
  rw [isLexFInitial_iff_shape]
  constructor
  · rintro ⟨hF, hS⟩; exact ⟨hF, hS.eq_greedy⟩
  · intro h
    refine ⟨h.1, ?_⟩
    rw [h.2]; exact greedyShape_greedy _ _ _
end LexF

/-! ### Target 2: `lem-lexF-shadow` -/

section Shadow

variable {n : ℕ}

lemma component_lexInit_upShadow {k : ℤ} {𝒜 : Finset (Finset (Fin n))}
    (h : Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) :
    (Component (k + 1) (∂⁺ 𝒜) ∧ IsLexInit (∂⁺ 𝒜) (k + 1).toNat) ∧ #(∂⁺ 𝒜) = costZ n k #𝒜 := by
  by_cases hk : 0 ≤ k
  · have e : (k + 1).toNat = k.toNat + 1 := by omega
    obtain ⟨h1, h2⟩ := lexInit_upShadow n k.toNat 𝒜 h.2
    refine ⟨⟨⟨by rw [e]; exact h2.1, fun h' => by omega⟩, by rw [e]; exact h2⟩, ?_⟩
    simp only [costZ, hk, ↓reduceIte, h1]
  · have h0 : 𝒜 = ∅ := h.1.2 (by omega)
    subst h0
    rw [upShadow_empty]
    exact ⟨⟨⟨by simp, fun _ => rfl⟩, isLexInit_empty _⟩, by simp [costZ_zero]⟩

/-- The shadow sizes of a `lexF` segment, component by component: `|∇ Lex(kᵢ, t*ᵢ)| = cᵢ(t*ᵢ)`. -/
lemma IsLexFSeg.shadow_card {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) :
    𝒜s.map (fun 𝒜 => #(∂⁺ 𝒜)) = List.zipWith (costZ n) ks (greedy (capZ n) ks t) := by
  rw [← h.2]
  obtain ⟨h1, -⟩ := h
  induction h1 with
  | nil => rfl
  | cons ha _ ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, ih, (component_lexInit_upShadow ha).2]

/-- `|Shad L| = ∑ᵢ cᵢ(t*ᵢ)` for the `lexF` segment `L` of size `t`. -/
lemma IsLexFSeg.shadow_sum {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) :
    (𝒜s.map (fun 𝒜 => #(∂⁺ 𝒜))).sum = cost (costZ n) ks (greedy (capZ n) ks t) := by
  rw [h.shadow_card]; rfl

/-- **Lemma `lem-lexF-shadow`**, first sentence. The componentwise upper shadow `Shad L` of the
`lexF` segment `L` of size `t` in degree `j` (exterior degrees `ks`) is the `lexF` segment of
size `∑ᵢ cᵢ(t*ᵢ)` in degree `j+1` (exterior degrees `ks.map (· + 1)`): its component sizes are the
greedy vector for the capacities `C(n, kᵢ+1)`, and every component is lex-initial. Components
with `kᵢ = −1` are empty in degree `j` and of capacity `1` in degree `j+1`; components with
`kᵢ > n` are empty in both degrees. -/
theorem lem_lexF_shadow {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t : ℕ}
    {𝒜s : List (Finset (Finset (Fin n)))} (h : IsLexFSeg n ks t 𝒜s) :
    IsLexFSeg n (ks.map (· + 1)) (cost (costZ n) ks (greedy (capZ n) ks t))
      (𝒜s.map upShadow) := by
  refine ⟨?_, ?_⟩
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.1.imp fun k 𝒜 h' => (component_lexInit_upShadow h').1
  · rw [List.map_map]
    have e : (card ∘ upShadow) = fun 𝒜 : Finset (Finset (Fin n)) => #(∂⁺ 𝒜) := rfl
    rw [e, h.shadow_card]
    exact (greedyShape_shadow n ks hks t).eq_greedy

/-- **Lemma `lem-lexF-shadow`**, second sentence. For `lexF` segments `L` of `Mon_j(F)` and `L'`
of `Mon_{j+1}(F)`, `|Shad L| ≤ |L'|` implies `Shad L ⊆ L'` (componentwise). -/
theorem lem_lexF_shadow_subset {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t t' : ℕ}
    {𝒜s ℬs : List (Finset (Finset (Fin n)))} (hL : IsLexFSeg n ks t 𝒜s)
    (hL' : IsLexFSeg n (ks.map (· + 1)) t' ℬs)
    (hle : (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum ≤ (ℬs.map card).sum) :
    List.Forall₂ (fun 𝒜 ℬ => ∂⁺ 𝒜 ⊆ ℬ) 𝒜s ℬs := by
  have h2 := (lem_lexF_shadow hks hL).forall2_subset hL' (by rw [List.map_map]; exact hle)
  rwa [List.forall₂_map_left_iff] at h2

end Shadow

end D5.S3.Combinatorics.Kozlov.LexCompression
