/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse]
   utility: none
   digest: The connected forcing polynomial of the star K_(1,n-1) is (n-1)x^(n-1) + x^n for n >= 4 and equals that of the path for n <= 3. -/

import D5.S3.Combinatorics.Graph.ZeroForcing.PathConnectedForcing

/-! The connected forcing polynomial of the star `K_{1,n-1}`, the unit-arm case of Proposition 7.11
of B. Brimkov, Graph Coloring, Zero Forcing, and Related Problems (PhD thesis, Rice University,
2017): for `n ≥ 4`, `Z_c(K_{1,n-1}; x) = (n - 1) x^(n-1) + x^n`, and for `n ≤ 3` the star
is a path and has the path's polynomial. The coefficients are the frozen
`ConnectedForcingCrossingRefutation.coefficient` for the star `starGraph n` on `Fin n` with
centre `0`.

`connected_forcing_iff` characterizes the connected forcing sets of the star, `n ≥ 1`: the sets
containing the centre and missing at most one leaf, and, when `n ≤ 3`, the single leaves. Two
white leaves block every force of the centre; without the centre a connected set is a single leaf.

admission_basis: escape-witness. Escape witnesses: stuck (two white leaves keep the closure inside
the set and the centre), eq_of_connected_no_center and connected_center (connected sets of the
star), forcing_center and forcing_leaf (the forcing chains), card_center_part and card_leaf_part
(the counts). -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.ZeroForcing.StarConnectedForcing

open SimpleGraph
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation

variable {n : ℕ}

/-- The star `K_{1,n-1}` on `Fin n` with centre `0`. -/
def starGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u.val = 0 ∨ v.val = 0)
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

private theorem star_adj {u v : Fin n} :
    (starGraph n).Adj u v ↔ u ≠ v ∧ (u.val = 0 ∨ v.val = 0) :=
  Iff.rfl

/-- With two leaves outside `S`, only `S` and the centre become black. -/
private theorem stuck (S : Set (Fin n)) (l₁ l₂ : Fin n) (h1 : l₁ ∉ S) (h2 : l₂ ∉ S)
    (h12 : l₁ ≠ l₂) (hl1 : l₁.val ≠ 0) (hl2 : l₂.val ≠ 0) :
    ∀ w, Black (starGraph n) S w → w ∈ S ∨ w.val = 0 := by
  intro w hw
  induction hw with
  | init h => exact Or.inl h
  | @force u w hu huw hall ihu ihall =>
    rcases (star_adj.mp huw).2 with hu0 | hw0
    · -- the centre forces a leaf `w`; some white leaf other than `w` would have to be black
      by_cases hw1 : w = l₁
      · have := ihall l₂ (star_adj.mpr ⟨fun h => hl2 (h ▸ hu0), Or.inl hu0⟩)
          (fun h => h12 (hw1 ▸ h).symm)
        rcases this with h | h
        · exact absurd h h2
        · exact absurd h hl2
      · have := ihall l₁ (star_adj.mpr ⟨fun h => hl1 (h ▸ hu0), Or.inl hu0⟩)
          (fun h => hw1 h.symm)
        rcases this with h | h
        · exact absurd h h1
        · exact absurd h hl1
    · exact Or.inr hw0

/-- A set containing the centre induces a connected subgraph. -/
private theorem connected_center (hn : 1 ≤ n) (S : Set (Fin n))
    (hc : (⟨0, hn⟩ : Fin n) ∈ S) :
    ((starGraph n).induce S).Connected := by
  have : Nonempty S := ⟨⟨_, hc⟩⟩
  have reach : ∀ x : S, ((starGraph n).induce S).Reachable ⟨_, hc⟩ x := by
    rintro ⟨x, hx⟩
    by_cases h : x = ⟨0, hn⟩
    · subst h; rfl
    · exact SimpleGraph.Adj.reachable (show (starGraph n).Adj ⟨0, hn⟩ x from
        star_adj.mpr ⟨fun h' => h h'.symm, Or.inl rfl⟩)
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

/-- Without the centre, a connected set is a single leaf. -/
private theorem eq_of_connected_no_center (hn : 1 ≤ n) (S : Set (Fin n))
    (hc : (⟨0, hn⟩ : Fin n) ∉ S) (hS : ((starGraph n).induce S).Connected) {x y : Fin n}
    (hx : x ∈ S) (hy : y ∈ S) : x = y := by
  obtain ⟨w⟩ := hS.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  cases w with
  | nil => rfl
  | cons h _ =>
    rename_i v _
    have h' := star_adj.mp (show (starGraph n).Adj x v.1 from h)
    rcases h'.2 with h0 | h0
    · exact absurd (show x = ⟨0, hn⟩ from Fin.ext h0) (fun e => hc (e ▸ hx))
    · exact absurd (show v.1 = ⟨0, hn⟩ from Fin.ext h0) (fun e => hc (e ▸ v.2))

/-- The centre with at most one leaf missing forces the star. -/
private theorem forcing_center (hn : 1 ≤ n) (S : Finset (Fin n))
    (hc : (⟨0, hn⟩ : Fin n) ∈ S) (hout : (Finset.univ \ S).card ≤ 1) :
    IsZeroForcing (starGraph n) (S : Set (Fin n)) := by
  intro w
  by_cases hw : w ∈ S
  · exact .init hw
  · have hwc : w ≠ ⟨0, hn⟩ := fun h => hw (h ▸ hc)
    refine .force (u := ⟨0, hn⟩) (.init hc) (star_adj.mpr ⟨fun h => hwc h.symm, Or.inl rfl⟩)
      fun x hx hxw => .init ?_
    by_contra hxS
    have hsub : ({x, w} : Finset (Fin n)) ⊆ Finset.univ \ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa using hxS
      · rw [Finset.mem_singleton.mp hz]; simpa using hw
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hxw] at this
    omega

/-- A single leaf forces the star when it has at most three vertices. -/
private theorem forcing_leaf (l : Fin n) (hl : l.val ≠ 0) (hn3 : n ≤ 3) :
    IsZeroForcing (starGraph n) ({l} : Set (Fin n)) := by
  have hn : 1 ≤ n := by have := l.isLt; omega
  set c : Fin n := ⟨0, hn⟩
  have hbc : Black (starGraph n) {l} c :=
    .force (u := l) (.init rfl) (star_adj.mpr ⟨fun h => hl (by rw [h]), Or.inr rfl⟩)
      fun x hx hxc => by
        rcases (star_adj.mp hx).2 with h | h
        · exact absurd h hl
        · exact absurd (Fin.ext h) hxc
  intro w
  by_cases hwl : w = l
  · exact hwl ▸ .init rfl
  by_cases hwc : w = c
  · exact hwc ▸ hbc
  refine .force (u := c) hbc (star_adj.mpr ⟨fun h => hwc h.symm, Or.inl rfl⟩) fun x hx hxw => ?_
  have hxc : x ≠ c := fun h => (star_adj.mp hx).1 h.symm
  have : x = l := by
    have hx0 : x.val ≠ 0 := fun h => hxc (Fin.ext h)
    have hw0 : w.val ≠ 0 := fun h => hwc (Fin.ext h)
    have := x.isLt; have := w.isLt; have := l.isLt
    have hxw' : x.val ≠ w.val := fun h => hxw (Fin.ext h)
    have hwl' : w.val ≠ l.val := fun h => hwl (Fin.ext h)
    exact Fin.ext (by omega)
  exact this ▸ .init rfl

/-- The connected forcing sets of the star `K_{1,n-1}`, `n ≥ 1`: the sets containing the centre
and missing at most one leaf, and, when `n ≤ 3`, the single leaves. -/
theorem connected_forcing_iff (hn : 1 ≤ n) (S : Finset (Fin n)) :
    connectedForcing (starGraph n) S ↔
      ((⟨0, by omega⟩ : Fin n) ∈ S ∧ (Finset.univ \ S).card ≤ 1) ∨
        (∃ l : Fin n, l.val ≠ 0 ∧ S = {l} ∧ n ≤ 3) := by
  have hn1 : 1 ≤ n := hn
  set c : Fin n := ⟨0, hn1⟩
  constructor
  · rintro ⟨hconn, hforce⟩
    by_cases hc : c ∈ S
    · left; refine ⟨hc, ?_⟩
      by_contra hcard; push Not at hcard
      obtain ⟨l₁, h1, l₂, h2, h12⟩ := Finset.one_lt_card.mp hcard
      have h1' : l₁ ∉ S := by simpa using h1
      have h2' : l₂ ∉ S := by simpa using h2
      have hl1 : l₁.val ≠ 0 := fun h => h1' ((Fin.ext h : l₁ = c) ▸ hc)
      have hl2 : l₂.val ≠ 0 := fun h => h2' ((Fin.ext h : l₂ = c) ▸ hc)
      rcases stuck (S : Set (Fin n)) l₁ l₂ h1' h2' h12 hl1 hl2 l₁ (hforce l₁) with h | h
      · exact h1' h
      · exact hl1 h
    · right
      obtain ⟨⟨l, hl⟩⟩ := hconn.nonempty
      have hlS : (l : Fin n) ∈ S := hl
      have hl0 : l.val ≠ 0 := fun h => hc ((Fin.ext h : l = c) ▸ hlS)
      have hS : S = {l} := by
        ext z; constructor
        · intro hz
          exact Finset.mem_singleton.mpr (eq_of_connected_no_center hn1 _ hc hconn hz hl)
        · intro hz; rw [Finset.mem_singleton.mp hz]; exact hlS
      refine ⟨l, hl0, hS, ?_⟩
      by_contra hn3; push Not at hn3
      obtain ⟨l₁, l₂, h12, h1, h2, hl1, hl2⟩ : ∃ l₁ l₂ : Fin n, l₁ ≠ l₂ ∧ l₁ ≠ l ∧ l₂ ≠ l ∧
          l₁.val ≠ 0 ∧ l₂.val ≠ 0 := by
        by_cases h1 : l.val = 1
        · exact ⟨⟨2, by omega⟩, ⟨3, by omega⟩, fun h => by simp [Fin.ext_iff] at h,
            fun h => by have := congrArg Fin.val h; simp at this; omega,
            fun h => by have := congrArg Fin.val h; simp at this; omega, by simp, by simp⟩
        · exact ⟨⟨1, by omega⟩, if l.val = 2 then ⟨3, by omega⟩ else ⟨2, by omega⟩,
            by split_ifs <;> simp [Fin.ext_iff],
            fun h => by have := congrArg Fin.val h; simp at this; omega,
            by split_ifs with h' <;> (intro h; have := congrArg Fin.val h; simp at this; omega),
            by simp, by split_ifs <;> simp⟩
      have hS' : ((S : Finset (Fin n)) : Set (Fin n)) = {l} := by rw [hS]; simp
      have h1S : l₁ ∉ (S : Set (Fin n)) := by rw [hS']; exact h1
      have h2S : l₂ ∉ (S : Set (Fin n)) := by rw [hS']; exact h2
      rcases stuck (S : Set (Fin n)) l₁ l₂ h1S h2S h12 hl1 hl2 l₁ (hforce l₁) with h | h
      · exact h1S h
      · exact hl1 h
  · rintro (⟨hc, hout⟩ | ⟨l, hl0, rfl, hn3⟩)
    · exact ⟨connected_center hn1 _ hc, forcing_center hn1 S hc hout⟩
    · refine ⟨?_, by rw [Finset.coe_singleton]; exact forcing_leaf l hl0 hn3⟩
      have : Nonempty ↥((({l} : Finset (Fin n))) : Set (Fin n)) := ⟨⟨l, by simp⟩⟩
      refine ⟨fun u v => ?_⟩
      have : u = v := Subtype.ext (by
        have hu := u.2; have hv := v.2; simp at hu hv; rw [hu, hv])
      rw [this]

private theorem card_center_part (hn : 1 ≤ n) (i : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n) => S.card = i ∧
      ((⟨0, by omega⟩ : Fin n) ∈ S ∧ (Finset.univ \ S).card ≤ 1)).card =
      (if i = n then 1 else 0) + (if i + 1 = n then n - 1 else 0) := by
  set c : Fin n := ⟨0, by omega⟩
  have hcomp : ∀ S : Finset (Fin n), (Finset.univ \ S).card = n - S.card := fun S => by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
  by_cases hi : i = n
  · subst hi
    have hnn : ¬ i + 1 = i := by omega
    simp only [↓reduceIte, hnn, add_zero]
    rw [Finset.card_eq_one]
    refine ⟨Finset.univ, ?_⟩
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, -⟩
      exact Finset.eq_univ_of_card S (by rw [hc, Fintype.card_fin])
    · rintro rfl; exact ⟨by simp, by simp, by simp⟩
  simp only [hi, ↓reduceIte, zero_add]
  by_cases hi1 : i + 1 = n
  · simp only [hi1, ↓reduceIte]
    have heq : (Finset.univ.filter fun S : Finset (Fin n) => S.card = i ∧
        (c ∈ S ∧ (Finset.univ \ S).card ≤ 1)) =
        (Finset.univ.erase c).image fun l => Finset.univ.erase l := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_erase, ne_eq, and_true]
      constructor
      · rintro ⟨hcard, hc, -⟩
        have h1 : (Finset.univ \ S).card = 1 := by rw [hcomp, hcard]; omega
        obtain ⟨l, hl⟩ := Finset.card_eq_one.mp h1
        refine ⟨l, fun h => ?_, ?_⟩
        · have : l ∈ Finset.univ \ S := by rw [hl]; simp
          exact (Finset.mem_sdiff.mp this).2 (h ▸ hc)
        · ext z
          simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
          constructor
          · intro hz; by_contra hzS
            have : z ∈ Finset.univ \ S := by simpa using hzS
            rw [hl, Finset.mem_singleton] at this; exact hz this
          · intro hz h; subst h
            have : z ∈ Finset.univ \ S := by rw [hl]; simp
            exact (Finset.mem_sdiff.mp this).2 hz
      · rintro ⟨l, hlc, rfl⟩
        refine ⟨?_, by simp [Ne.symm hlc], ?_⟩
        · rw [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
          omega
        · rw [hcomp, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
            Fintype.card_fin]; omega
    rw [heq, Finset.card_image_of_injective]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
    · intro l l' h
      have : l' ∉ Finset.univ.erase l := by
        rw [show Finset.univ.erase l = Finset.univ.erase l' from h]; simp
      exact (by simpa using this : l' = l).symm
  · simp only [hi1, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro S - ⟨hcard, -, hout⟩
    rw [hcomp, hcard] at hout
    have : S.card ≤ n := by
      calc S.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ S)
        _ = n := by simp
    omega

private theorem card_leaf_part (hn : 1 ≤ n) (i : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n) => S.card = i ∧
      (∃ l : Fin n, l.val ≠ 0 ∧ S = {l} ∧ n ≤ 3)).card =
      if i = 1 ∧ n ≤ 3 then n - 1 else 0 := by
  set c : Fin n := ⟨0, by omega⟩
  split_ifs with h
  · obtain ⟨rfl, hn3⟩ := h
    have heq : (Finset.univ.filter fun S : Finset (Fin n) => S.card = 1 ∧
        (∃ l : Fin n, l.val ≠ 0 ∧ S = {l} ∧ n ≤ 3)) =
        (Finset.univ.erase c).image fun l => {l} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_erase, ne_eq, and_true]
      constructor
      · rintro ⟨-, l, hl, rfl, -⟩
        exact ⟨l, fun h => hl (by rw [h]), rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨by simp, l, fun h => hl (Fin.ext h), rfl, hn3⟩
    rw [heq, Finset.card_image_of_injective _ Finset.singleton_injective,
      Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro S - ⟨hcard, l, -, rfl, hn3⟩
    simp at hcard
    exact h ⟨hcard.symm, hn3⟩

/-- The coefficients of the connected forcing polynomial of the star `K_{1,n-1}`, `n ≥ 1`. -/
private theorem coeff_formula (hn : 1 ≤ n) (i : ℕ) :
    coefficient (starGraph n) i =
      (if i = n then 1 else 0) + (if i + 1 = n then n - 1 else 0) +
        (if i = 1 ∧ n ≤ 3 then n - 1 else 0) := by
  classical
  unfold coefficient
  set c : Fin n := ⟨0, by omega⟩
  have hsplit : (Finset.univ.filter fun S : Finset (Fin n) =>
      S.card = i ∧ connectedForcing (starGraph n) S) =
      (Finset.univ.filter fun S : Finset (Fin n) => S.card = i ∧
        (c ∈ S ∧ (Finset.univ \ S).card ≤ 1)) ∪
      (Finset.univ.filter fun S : Finset (Fin n) => S.card = i ∧
        (∃ l : Fin n, l.val ≠ 0 ∧ S = {l} ∧ n ≤ 3)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      connected_forcing_iff hn S]
    tauto
  rw [hsplit, Finset.card_union_of_disjoint, card_center_part hn, card_leaf_part hn]
  rw [Finset.disjoint_filter]
  rintro S - ⟨-, hc, -⟩ ⟨-, l, hl, rfl, -⟩
  rw [Finset.mem_singleton] at hc
  exact hl (by rw [← hc])

/-- The connected forcing polynomial of the star `K_{1,n-1}`: the coefficients for `n ≥ 1`,
`Z_c = (n - 1) x^(n-1) + x^n` for `n ≥ 4`, and the path's coefficients for `n ≤ 3`. -/
theorem result :
    (1 ≤ n → ∀ i, coefficient (starGraph n) i =
      (if i = n then 1 else 0) + (if i + 1 = n then n - 1 else 0) +
        (if i = 1 ∧ n ≤ 3 then n - 1 else 0)) ∧
    (4 ≤ n → ∀ i, coefficient (starGraph n) i =
      if i = n then 1 else if i + 1 = n then n - 1 else 0) ∧
    (n ≤ 3 → ∀ i, coefficient (starGraph n) i = coefficient (pathGraph n) i) := by
  refine ⟨coeff_formula, fun h4 i => ?_, fun h3 i => ?_⟩
  · rw [coeff_formula (by omega)]
    have : ¬ (i = 1 ∧ n ≤ 3) := fun h => by omega
    simp only [this, ↓reduceIte, add_zero]
    split_ifs <;> omega
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · rcases Nat.lt_or_ge n 1 with hn1 | hn1
      · obtain rfl : n = 0 := by omega
        have : starGraph 0 = pathGraph 0 := by
          ext u
          exact u.elim0
        rw [this]
      obtain rfl : n = 1 := by omega
      have : starGraph 1 = pathGraph 1 := by
        ext u v
        obtain rfl : u = v := Subsingleton.elim u v
        simp
      rw [this]
    obtain ⟨h0, h1, hge⟩ :=
      D5.S3.Combinatorics.Graph.ZeroForcing.PathConnectedForcing.result hn2
    rw [coeff_formula (by omega)]
    rcases i with _ | _ | i
    · rw [h0]
      have e1 : ¬ (0 = n) := by omega
      have e2 : ¬ (0 + 1 = n) := by omega
      have e3 : ¬ (0 = 1 ∧ n ≤ 3) := by omega
      simp only [e1, e2, e3, ↓reduceIte, add_zero]
    · rw [h1]
      have h13 : (1 = 1 ∧ n ≤ 3) := ⟨rfl, h3⟩
      simp only [h13, and_self, ↓reduceIte]
      split_ifs <;> omega
    · rw [hge _ (by omega)]
      have : ¬ (i + 1 + 1 = 1 ∧ n ≤ 3) := fun h => by omega
      simp only [this, ↓reduceIte, add_zero]
      split_ifs <;> omega

end D5.S3.Combinatorics.Graph.ZeroForcing.StarConnectedForcing
