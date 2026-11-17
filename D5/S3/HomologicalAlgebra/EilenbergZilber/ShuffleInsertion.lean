/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Insertion of left and right shuffle steps and their face identities. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleBasic

@[expose] public section

noncomputable section

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace Shuffle

/-! ##### Insertion indices -/

/-- The vertex index in the `(p+1, q)`-shuffle's domain where the new left step
was inserted. Removing this vertex via `δ` recovers the original shuffle.
Equals the number of vertices of `ν` whose first coordinate is `< j`. -/
def insertLeftIndex {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Fin (p + q + 2) :=
  ⟨(Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).card, by
    exact Nat.lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

/-- The vertex index where the new right step was inserted.
Equals the number of vertices of `ν` whose second coordinate is `< k`. -/
def insertRightIndex {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Fin (p + q + 2) :=
  ⟨(Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card, by
    exact Nat.lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

/-! ##### Insertion helpers -/

/-- The insertion index satisfies `t ≤ j + q`: vertices with fst < j have
index ≤ (j-1) + q by `coordSum_eq`, so there are at most j + q of them. -/
lemma insertLeftIndex_le {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftIndex ν j).val ≤ j.val + q := by
  simp only [insertLeftIndex]
  -- Inject the filter into Finset.range (j+q) via Fin.val
  calc (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).card
      = ((Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).image
          Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (j.val + q)).card := by
          apply Finset.card_le_card; intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range] at hx ⊢
          obtain ⟨r, hr, rfl⟩ := hx
          have := coordSum_eq ν r; have := (ν.1 r).2.isLt; omega
    _ = j.val + q := Finset.card_range _

/-- Symmetric bound: the right insertion index satisfies `t ≤ p + k`. -/
private lemma insertRightIndex_le {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightIndex ν k).val ≤ p + k.val := by
  simp only [insertRightIndex]
  calc (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card
      = ((Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).image
          Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (p + k.val)).card := by
          apply Finset.card_le_card; intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range] at hx ⊢
          obtain ⟨r, hr, rfl⟩ := hx
          have := coordSum_eq ν r; have := (ν.1 r).1.isLt; omega
    _ = p + k.val := Finset.card_range _

/-- Lower bound: the left insertion index satisfies `j ≤ t`.
Proof: any r with r.val < j has fst(r) ≤ r < j, so the filter includes all r < j. -/
lemma insertLeftIndex_ge {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    j.val ≤ (insertLeftIndex ν j).val := by
  -- The set of indices where the first coordinate is less than $j$ contains at least the indices
  -- $0, 1, ..., j-1$.
  have h_filter : Finset.filter (fun r : Fin (p + q + 1) => (ν.1 r).1.val <
      j.val) Finset.univ ⊇ Finset.univ.filter (fun r : Fin (p + q + 1) => r.val < j.val) := by
    intro r hr;
    have := coordSum_eq ν r;
    grind;
  refine le_trans ?_ (Finset.card_mono h_filter)
  rw [Finset.card_eq_of_bijective]
  · exact fun i hi => ⟨i, by linarith [Fin.is_lt j]⟩
  · aesop;
  · aesop;
  · aesop

/-- Symmetric lower bound: the right insertion index satisfies `k ≤ t`. -/
private lemma insertRightIndex_ge {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    k.val ≤ (insertRightIndex ν k).val := by
  change k.val ≤ (Finset.univ.filter fun r : Fin (p + q + 1) =>
    (ν.1 r).2.val < k.val).card
  calc
    k.val = (Finset.univ.filter fun r : Fin (p + q + 1) =>
        r.val < k.val).card := by
      rw [Fin.card_filter_val_lt, min_eq_right (by have := k.isLt; omega)]
    _ ≤ _ := Finset.card_le_card fun r hr => by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hlt := (Finset.mem_filter.mp hr).2
      have hsum := coordSum_eq ν r
      omega

/-- The filter `{r | fst(r) < j}` is a downward-closed initial segment:
`fst(ν r) < j ↔ r.val < t` where `t = insertLeftIndex`. -/
lemma insertLeftIndex_iff {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (r : Fin (p + q + 1)) :
    (ν.1 r).1.val < j.val ↔ r.val < (insertLeftIndex ν j).val := by
  constructor <;> intro h;
  · -- Since ν is monotone, the set {x | x.val < t} is exactly the set of elements in the filter.
    -- Therefore, if r is in the filter, then r < t.
    have h_filter : {x : Fin (p + q + 1) | (ν.1 x).1.val < j.val} ⊇ Finset.Iio r := by
      intro x hx;
      exact lt_of_le_of_lt ( Nat.cast_le.mpr <| ν.1.monotone ( le_of_lt <| by aesop ) |> fun h =>
          h.1 ) h;
    have h_filter_card : Finset.card (Finset.filter (fun x => (ν.1 x).1.val < j.val)
        Finset.univ) ≥ Finset.card (Finset.Iio r) + 1 := by
      refine Finset.card_lt_card ?_
      simp_all +decide only [Finset.coe_Iio, ge_iff_le, Finset.ssubset_def, Finset.subset_iff,
          Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_lt];
      exact ⟨ fun x hx => h_filter hx, r, h, le_rfl ⟩;
    aesop;
  · contrapose! h;
    exact le_trans ( Finset.card_le_card <| show Finset.filter ( fun x : Fin ( p + q + 1 ) => ( ν.1
        x |>.1 : ℕ ) < j ) Finset.univ ⊆ Finset.Iio r from fun x hx => Finset.mem_Iio.mpr <|
        lt_of_not_ge fun hx' => by linarith [ Finset.mem_filter.mp hx,
                                    show ( ν.1 x |>.1 : ℕ ) ≥ ( ν.1 r |>.1 : ℕ )
                                    by exact ν.1.monotone hx' |>.1 ] ) <| by simp +decide [];

/-- Symmetric: `snd(ν r) < k ↔ r.val < insertRightIndex`. -/
lemma insertRightIndex_iff {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (r : Fin (p + q + 1)) :
    (ν.1 r).2.val < k.val ↔ r.val < (insertRightIndex ν k).val := by
  constructor <;> intro h
  · have h_filter :
        {x : Fin (p + q + 1) | (ν.1 x).2.val < k.val} ⊇ Finset.Iio r := by
      intro x hx
      exact lt_of_le_of_lt
        (Nat.cast_le.mpr ((ν.1.monotone (le_of_lt (by aesop))).2)) h
    have h_filter_card :
        Finset.card (Finset.filter (fun x => (ν.1 x).2.val < k.val) Finset.univ) ≥
          Finset.card (Finset.Iio r) + 1 := by
      refine Finset.card_lt_card ?_
      simp_all +decide only [Finset.coe_Iio, ge_iff_le, Finset.ssubset_def, Finset.subset_iff,
          Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_lt]
      exact ⟨fun x hx => h_filter hx, r, h, le_rfl⟩
    aesop
  · contrapose! h
    exact le_trans
      (Finset.card_le_card (show
        Finset.filter (fun x : Fin (p + q + 1) => (ν.1 x).2.val < k.val) Finset.univ ⊆
          Finset.Iio r from fun x hx => Finset.mem_Iio.mpr (lt_of_not_ge fun hx' => by
            have hmono : (ν.1 r).2.val ≤ (ν.1 x).2.val := (ν.1.monotone hx').2
            linarith [Finset.mem_filter.mp hx])))
      (by simp +decide [])

/-! ##### Insertion maps (RHS → LHS direction) -/

/-- The underlying piecewise map for `insertLeftStep`: before the insertion point,
embed the original vertex via `succAbove j`; at the insertion point, place `(j, t-j)`;
after the insertion point, embed the shifted-back vertex via `succAbove j`. -/
noncomputable def insertLeftStepFun {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Fin ((p + 1) + q + 1) → Index (p + 1) × Index q :=
  let t := (insertLeftIndex ν j).val
  have ht_lt : t < p + q + 2 := (insertLeftIndex ν j).isLt
  have ht_le : t ≤ j.val + q := insertLeftIndex_le ν j
  fun r =>
    -- Before insertion: embed original vertex via succAbove j (preserves value since fst < j)
    if h : r.val < t then
      (j.succAbove (ν.1 ⟨r, by omega⟩).1, (ν.1 ⟨r, by omega⟩).2)
    -- At insertion point: new left step with fst = j, snd = t - j
    else if h2 : r.val = t then
      (j, ⟨r.val - j.val, by omega⟩)
    -- After insertion: embed shifted-back vertex via succAbove j (adds 1 since fst ≥ j)
    else
      (j.succAbove (ν.1 ⟨r - 1, by omega⟩).1, (ν.1 ⟨r - 1, by omega⟩).2)

/-- Coordinate sum of the piecewise map equals the position index. -/
private lemma insertLeftStepFun_coordSum {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (r : Fin ((p + 1) + q + 1)) :
    (insertLeftStepFun ν j r).1.val + (insertLeftStepFun ν j r).2.val = r.val := by
  simp only [insertLeftStepFun]
  split_ifs with h1 h2
  · -- r < t: succAbove preserves value since fst < j, then use coordSum_eq
    have hfst := (insertLeftIndex_iff ν j ⟨r.val, by omega⟩).mpr h1
    simp only [Fin.succAbove]
    split
    · simp only [Fin.val_castSucc]
      have := coordSum_eq ν ⟨r.val, by omega⟩
      simp at this; omega
    · rename_i hn
      exfalso
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn
      omega
  · -- r = t: j + (t - j) = t = r
    have hge := insertLeftIndex_ge ν j
    simp; omega
  · -- r > t: succAbove adds 1 since fst ≥ j, then use coordSum_eq
    have hfst : ¬ (ν.1 ⟨r.val - 1, by omega⟩).1.val < j.val := by
      rw [insertLeftIndex_iff]; simp; omega
    simp only [Fin.succAbove]
    split
    · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
    · simp only [Fin.val_succ]
      have := coordSum_eq ν ⟨r.val - 1, by omega⟩
      simp at this; omega

/-- Insert a left step at face index `j`, turning a `(p, q)`-shuffle into a
`(p+1, q)`-shuffle.  The original path from `(0,0)` to `(p, q)` is embedded
into a path from `(0,0)` to `(p+1, q)` by applying `Fin.succAbove j` to the
first coordinate and inserting a new left step where the first coordinate
crosses `j`. -/
noncomputable def insertLeftStep {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Shuffle (p + 1) q :=
  ⟨⟨insertLeftStepFun ν j, by
    -- Monotonicity: use coordSum to derive both coordinates weakly increasing
    intro a b hab
    simp only [Prod.le_def]
    constructor
    · -- First coordinate monotone
      suffices hsuc : ∀ r : Fin (p + 1 + q),
          (insertLeftStepFun ν j r.castSucc).1 ≤ (insertLeftStepFun ν j r.succ).1 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertLeftStepFun ν j r).1) ).2 hsuc hab
      intro r
      simp only [insertLeftStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (Fin.succAbove_le_succAbove_iff.mpr (ν.1.monotone (Fin.castSucc_le_succ
            r)).1) -- cs < t, succ < t
      · -- cs < t, succ = t: succAbove(fst) ≤ j since fst < j
        have hfst := (insertLeftIndex_iff ν j ⟨r.val, by omega⟩).mpr h1
        simp only [Fin.succAbove]
        split
        · simp [Fin.le_def]; omega
        · rename_i hn; exfalso; simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs < t, succ > t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ = t (impossible)
      · -- cs = t, succ > t: j ≤ succAbove(fst) since fst ≥ j
        have hfst : ¬ (ν.1 ⟨r.val, by omega⟩).1.val < j.val := by
          rw [insertLeftIndex_iff]; simp at h4; simp; omega
        push Not at hfst
        have heq : (⟨r.succ.val - 1, by omega⟩ : Fin (p + q + 1)) = ⟨r.val, by omega⟩ := by
          ext; simp [Fin.val_succ]
        rw [heq]
        simp only [Fin.succAbove]
        split
        · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
        · simp [Fin.le_def, Fin.val_succ]; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ = t (impossible)
      · exact (Fin.succAbove_le_succAbove_iff.mpr -- cs > t, succ > t
          (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).1)
    · -- Second coordinate monotone
      suffices hsuc : ∀ r : Fin (p + 1 + q),
          (insertLeftStepFun ν j r.castSucc).2 ≤ (insertLeftStepFun ν j r.succ).2 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertLeftStepFun ν j r).2)).2 hsuc hab
      intro r
      simp only [insertLeftStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (ν.1.monotone (Fin.castSucc_le_succ r)).2 -- castSucc < t, succ < t
      · -- castSucc < t, succ = t: snd(ν r) ≤ r+1-j
        -- Reduce to j ≤ ν(r).1 + 1 using coordSum_eq
        simp only [Fin.val_castSucc, Fin.val_succ]
        have hge := insertLeftIndex_ge ν j
        have hsv := Fin.val_succ r
        have hsum := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : j.val ≤ (ν.1 ⟨r.val, by omega⟩).1.val + 1 by
          simp only [Fin.le_def] at hsum ⊢; omega
        by_cases hr : r.val + 1 = p + 1 + q
        · -- r is the last vertex: ν(r) = (p, q), so fst = p and j ≤ p + 1
          have hlast : ν.1 ⟨r.val, by omega⟩ = (Fin.last p, Fin.last q) := by
            have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
              Fin.ext (by simp [Fin.last]; omega)
            rw [this]; exact Shuffle.apply_last ν
          have hfst : (ν.1 ⟨r.val, by omega⟩).1.val = p := by
            rw [hlast]; simp [Fin.last]
          rw [hfst]; omega
        · -- r is not the last vertex: ν(r+1).1 ≥ j (by insertLeftIndex_iff)
          -- and ν(r+1).1 ≤ ν(r).1 + 1 (by shuffle step), so j ≤ ν(r).1 + 1
          let r' : Fin (p + q + 1) := ⟨r.val + 1, by omega⟩
          have hge_j : j.val ≤ (ν.1 r').1.val := by
            by_contra hlt
            push Not at hlt
            have h_iff := (insertLeftIndex_iff ν j r').mp hlt
            have ht : (insertLeftIndex ν j).val = r.val + 1 := by
              simp [Fin.val_succ] at hsv; omega
            change r.val + 1 < _ at h_iff
            omega
          have hstep := shuffle_step ν ⟨r.val, by omega⟩
          have hcs : (⟨r.val, by omega⟩ : Fin (p + q)).castSucc = (⟨r.val,
              by omega⟩ : Fin (p + q + 1)) :=
            Fin.ext (by simp [Fin.castSucc])
          have hsu : (⟨r.val, by omega⟩ : Fin (p + q)).succ = r' :=
            Fin.ext (by simp [Fin.succ, r'])
          rw [hcs, hsu] at hstep
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs < t, succ > t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ = t (impossible)
      ·  -- castSucc = t, succ > t
        simp only [Fin.val_castSucc, Fin.val_succ, add_tsub_cancel_right]
        simp only [Fin.le_def]
        have hcs := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : (ν.1 ⟨r.val, by omega⟩).1.val ≤ j.val by
          have : (⟨r.val, by omega⟩ : Fin (p + q + 1)).val = r.val := rfl
          omega
        by_cases hr : r.val = 0
        · have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = 0 := Fin.ext (by simp [hr])
          rw [this, Shuffle.apply_zero]; simp
        · let r' : Fin (p + q + 1) := ⟨r.val - 1, by omega⟩
          have hr'lt : r'.val < (insertLeftIndex ν j).val := by
            simp [r'] at h4 ⊢; omega
          have hfst_lt : (ν.1 r').1.val < j.val :=
            (insertLeftIndex_iff ν j r').mpr hr'lt
          have hstep := shuffle_step ν ⟨r.val - 1, by omega⟩
          have hcs2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).castSucc = r' :=
            Fin.ext (by simp [Fin.castSucc, r'])
          have hsu2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).succ = ⟨r.val, by omega⟩ :=
            Fin.ext (by simp [Fin.succ]; omega)
          rw [hcs2, hsu2] at hstep
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ = t (impossible)
      · exact (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).2 -- cs > t, succ > t
      ⟩, by
    -- Injectivity: f(a) = f(b) → coordSum(f(a)) = coordSum(f(b)) → a = b
    intro a b hab
    have ha := insertLeftStepFun_coordSum ν j a
    have hb := insertLeftStepFun_coordSum ν j b
    have heq : insertLeftStepFun ν j a = insertLeftStepFun ν j b := hab
    have : (insertLeftStepFun ν j a).1.val + (insertLeftStepFun ν j a).2.val =
        (insertLeftStepFun ν j b).1.val + (insertLeftStepFun ν j b).2.val := by rw [heq]
    exact Fin.ext (by omega)⟩

/-- The underlying piecewise map for `insertRightStep`: before the insertion point,
embed the original vertex via `succAbove k` on the second coordinate; at the
insertion point, place `(t-k, k)`; after the insertion point, embed the
shifted-back vertex via `succAbove k`. -/
noncomputable def insertRightStepFun {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Fin (p + (q + 1) + 1) → Index p × Index (q + 1) :=
  let t := (insertRightIndex ν k).val
  fun r =>
    if h : r.val < t then
      ((ν.1 ⟨r, by omega⟩).1, k.succAbove (ν.1 ⟨r, by omega⟩).2)
    else if h2 : r.val = t then
      (⟨r.val - k.val, by
        have := insertRightIndex_le ν k; omega⟩, k)
    else
      ((ν.1 ⟨r - 1, by omega⟩).1, k.succAbove (ν.1 ⟨r - 1, by omega⟩).2)

/-- Coordinate sum of the right-insertion piecewise map equals the position index. -/
private lemma insertRightStepFun_coordSum {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (r : Fin (p + (q + 1) + 1)) :
    (insertRightStepFun ν k r).1.val + (insertRightStepFun ν k r).2.val = r.val := by
  simp only [insertRightStepFun]
  split_ifs with h1 h2
  · have hsnd := (insertRightIndex_iff ν k ⟨r.val, by omega⟩).mpr h1
    simp only [Fin.succAbove]
    split
    · simp only [Fin.val_castSucc]
      have := coordSum_eq ν ⟨r.val, by omega⟩
      simp at this; omega
    · rename_i hn
      exfalso
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn
      omega
  · have hge := insertRightIndex_ge ν k
    simp; omega
  · have hsnd : ¬ (ν.1 ⟨r.val - 1, by omega⟩).2.val < k.val := by
      rw [insertRightIndex_iff]; simp; omega
    simp only [Fin.succAbove]
    split
    · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
    · simp only [Fin.val_succ]
      have := coordSum_eq ν ⟨r.val - 1, by omega⟩
      simp at this; omega

/-- Insert a right step at face index `k`, turning a `(p, q)`-shuffle into a
`(p, q+1)`-shuffle.  Applies `Fin.succAbove k` to the second coordinate and
inserts a new right step where the second coordinate crosses `k`. -/
noncomputable def insertRightStep {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Shuffle p (q + 1) :=
  ⟨⟨insertRightStepFun ν k, by
    intro a b hab
    simp only [Prod.le_def]
    constructor
    · -- First coordinate monotone
      suffices hsuc : ∀ r : Fin (p + (q + 1)),
          (insertRightStepFun ν k r.castSucc).1 ≤ (insertRightStepFun ν k r.succ).1 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertRightStepFun ν k r).1)).2 hsuc hab
      intro r
      simp only [insertRightStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (ν.1.monotone (Fin.castSucc_le_succ r)).1 -- cs < t, succ < t
      · -- cs < t, succ = t: fst(ν r) ≤ r+1-k
        simp only [Fin.val_castSucc, Fin.val_succ]
        have hge := insertRightIndex_ge ν k
        have hsv := Fin.val_succ r
        have hsum := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : k.val ≤ (ν.1 ⟨r.val, by omega⟩).2.val + 1 by
          simp only [Fin.le_def] at hsum ⊢; omega
        by_cases hr : r.val + 1 = p + q + 1
        · have hlast : ν.1 ⟨r.val, by omega⟩ = (Fin.last p, Fin.last q) := by
            have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
              Fin.ext (by simp [Fin.last]; omega)
            rw [this]; exact Shuffle.apply_last ν
          have hsnd : (ν.1 ⟨r.val, by omega⟩).2.val = q := by
            rw [hlast]; simp [Fin.last]
          rw [hsnd]; omega
        · let r' : Fin (p + q + 1) := ⟨r.val + 1, by omega⟩
          have hge_k : k.val ≤ (ν.1 r').2.val := by
            by_contra hlt
            push Not at hlt
            have h_iff := (insertRightIndex_iff ν k r').mp hlt
            have ht : (insertRightIndex ν k).val = r.val + 1 := by
              simp [Fin.val_succ] at hsv; omega
            change r.val + 1 < _ at h_iff
            omega
          have hstep := shuffle_step ν ⟨r.val, by omega⟩
          have hcs : (⟨r.val, by omega⟩ : Fin (p + q)).castSucc = (⟨r.val,
              by omega⟩ : Fin (p + q + 1)) :=
            Fin.ext (by simp [Fin.castSucc])
          have hsu : (⟨r.val, by omega⟩ : Fin (p + q)).succ = r' :=
            Fin.ext (by simp [Fin.succ, r'])
          rw [hcs, hsu] at hstep
          rcases hstep with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · -- castSucc = t, succ > t
        simp only [Fin.val_castSucc, Fin.val_succ, add_tsub_cancel_right, Fin.eta]
        have hcs := coordSum_eq ν ⟨r.val, by omega⟩
        have hcsv : (⟨r.val, by omega⟩ : Fin (p + q + 1)).val = r.val := rfl
        suffices h : (ν.1 ⟨r.val, by omega⟩).2.val ≤ k.val by
          have hre : (ν.1 r).1.val = (ν.1 ⟨r.val, by omega⟩).1.val := by congr 3
          simp only [Fin.le_def] at hcs ⊢; omega
        by_cases hr : r.val = 0
        · have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = 0 := Fin.ext (by simp [hr])
          rw [this, Shuffle.apply_zero]; simp
        · let r' : Fin (p + q + 1) := ⟨r.val - 1, by omega⟩
          have hr'lt : r'.val < (insertRightIndex ν k).val := by
            simp [r'] at h4 ⊢; omega
          have hsnd_lt : (ν.1 r').2.val < k.val :=
            (insertRightIndex_iff ν k r').mpr hr'lt
          have hstep := shuffle_step ν ⟨r.val - 1, by omega⟩
          have hcs2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).castSucc = r' :=
            Fin.ext (by simp [Fin.castSucc, r'])
          have hsu2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).succ = ⟨r.val, by omega⟩ :=
            Fin.ext (by simp [Fin.succ]; omega)
          rw [hcs2, hsu2] at hstep
          rcases hstep with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · exact (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).1
    · -- Second coordinate monotone
      suffices hsuc : ∀ r : Fin (p + (q + 1)),
          (insertRightStepFun ν k r.castSucc).2 ≤ (insertRightStepFun ν k r.succ).2 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertRightStepFun ν k r).2)).2 hsuc hab
      intro r
      simp only [insertRightStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (Fin.succAbove_le_succAbove_iff.mpr (ν.1.monotone (Fin.castSucc_le_succ
            r)).2) -- cs < t, succ < t
      · -- cs < t, succ = t: succAbove(snd) ≤ k since snd < k
        have hrcs : (⟨r.castSucc.val, by simp; omega⟩ : Fin (p + q + 1)) =
            ⟨r.val, by omega⟩ := Fin.ext (by simp)
        have hsnd := (insertRightIndex_iff ν k ⟨r.val, by omega⟩).mpr h1
        simp only [Fin.succAbove]; split
        · simp only [Fin.le_def, Fin.val_castSucc]
          have : (ν.1 ⟨r.castSucc.val, by simp; omega⟩).2.val =
              (ν.1 ⟨r.val, by omega⟩).2.val := by rw [hrcs]
          omega
        · rename_i hn; exfalso
          simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn
          have : (ν.1 ⟨r.castSucc.val, by simp; omega⟩).2.val =
              (ν.1 ⟨r.val, by omega⟩).2.val := by rw [hrcs]
          omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · -- cs = t, succ > t: k ≤ succAbove(snd) since snd ≥ k
        have hsnd : ¬ (ν.1 ⟨r.val, by omega⟩).2.val < k.val := by
          rw [insertRightIndex_iff]; simp at h4; simp; omega
        push Not at hsnd
        have heq : (⟨r.succ.val - 1, by omega⟩ : Fin (p + q + 1)) = ⟨r.val, by omega⟩ := by
          ext; simp [Fin.val_succ]
        rw [heq]
        simp only [Fin.succAbove]
        split
        · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
        · simp only [Fin.le_def, Fin.val_succ]
          simp only [Fin.val_castSucc] at h4
          omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · exact (Fin.succAbove_le_succAbove_iff.mpr
          (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).2)
    ⟩, by
    -- Injectivity: f(a) = f(b) → coordSum(f(a)) = coordSum(f(b)) → a = b
    intro a b hab
    have ha := insertRightStepFun_coordSum ν k a
    have hb := insertRightStepFun_coordSum ν k b
    have heq : insertRightStepFun ν k a = insertRightStepFun ν k b := hab
    have : (insertRightStepFun ν k a).1.val + (insertRightStepFun ν k a).2.val =
        (insertRightStepFun ν k b).1.val + (insertRightStepFun ν k b).2.val := by rw [heq]
    exact Fin.ext (by omega)⟩

/-- Inserting a left step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove j` applied to the first coordinate.
(Purely combinatorial: no `SimplexCategory` or topology needed.) -/
lemma insertLeftStep_face {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    ∀ (k : Index (p + q)),
      (insertLeftStep ν j).1 (Fin.succAbove
        (⟨(insertLeftIndex ν j).val, by omega⟩ : Fin ((p + 1) + q + 1))
        (k.cast (by omega))) =
      (j.succAbove (ν.1 k).1, (ν.1 k).2) := by
  unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.insertLeftStep;
  intro k
  unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.insertLeftStepFun
  simp only [Fin.succAbove, OrderHom.coe_mk] at *;
  split_ifs <;> simp_all +decide only [Fin.castSucc, Fin.val_castAdd, Fin.val_cast, Fin.eta,
      Fin.succ, not_lt, Prod.mk.injEq, add_tsub_cancel_right];
  · exact absurd ‹_› ( ne_of_lt ‹_› );
  · exact absurd ‹_› ( not_le_of_gt ‹_› );
  · exact False.elim <| ‹¬_› <| Nat.lt_of_succ_lt ‹_›;
  · split_ifs <;> simp_all +decide [ Fin.ext_iff];
    · have := insertLeftIndex_ge ν j; have := insertLeftIndex_le ν j;
          simp_all +decide [ Fin.le_iff_val_le_val ]; omega;
    · have := insertLeftIndex_iff ν j k; simp_all +decide [ Fin.le_def ] ;
      grind

/-- Inserting a right step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove k` applied to the second coordinate. -/
lemma insertRightStep_face {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    ∀ (i : Index (p + q)),
      (insertRightStep ν k).1 (Fin.succAbove
        (⟨(insertRightIndex ν k).val, by omega⟩ : Fin (p + (q + 1) + 1))
        (i.cast (by omega))) =
      ((ν.1 i).1, k.succAbove (ν.1 i).2) := by
  intro i
  generalize_proofs at *;
  unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.insertRightStep; simp +decide only [Fin.succAbove,
      Fin.cast_eq_self, Fin.eta, OrderHom.coe_mk];
  unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.insertRightStepFun; split_ifs <;>
      simp_all +decide only [Order.lt_add_one_iff, Fin.val_castSucc, Fin.eta, Prod.mk.injEq,
      Fin.ext_iff, true_and, not_lt, Fin.val_succ, add_tsub_cancel_right];
  all_goals split_ifs <;> simp_all +decide only [Fin.val_castSucc, Fin.succAbove, ↓reduceIte,
      not_lt, Fin.val_succ, Std.le_refl];
  any_goals split_ifs <;> simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;
  any_goals linarith [ show ( i : ℕ ) < ν.insertRightIndex k from by assumption ];
  · exact False.elim <| ‹¬Fin.castSucc i < ν.insertRightIndex k› <| Nat.lt_of_succ_lt ‹_›;
  · have := Fin.le_iff_val_le_val.mp ‹_›; simp_all +decide [] ; omega;
  · exact absurd ‹_› ( by linarith [ show ( i : ℕ ) + 1 > ( ν.insertRightIndex k : ℕ ) from
                           by linarith [ show ( i : ℕ ) ≥ ( ν.insertRightIndex k : ℕ ) from
                               by assumption ] ] );

/-- The insert-left map `(j, ν) ↦ (insertLeftStep ν j, insertLeftIndex ν j)` is
injective: distinct `(j, ν)` pairs produce distinct `(μ, vertex)` pairs. -/
lemma insertLeftStep_injective {p q : ℕ}
    (j₁ j₂ : Fin (p + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertLeftStep ν₁ j₁ = insertLeftStep ν₂ j₂)
    (hr : insertLeftIndex ν₁ j₁ = insertLeftIndex ν₂ j₂) :
    j₁ = j₂ ∧ ν₁ = ν₂ := by
  have hj : j₁ = j₂ := by
    have hcoordinate := congrArg (fun μ : Shuffle (p + 1) q =>
      (μ.1 ((insertLeftIndex ν₁ j₁).cast (by omega))).1) hμ
    simpa only [insertLeftStep, OrderHom.coe_mk, insertLeftStepFun, Fin.val_cast,
      hr, lt_self_iff_false, ↓reduceDIte] using hcoordinate
  subst j₂
  refine ⟨rfl, Subtype.ext ?_⟩
  apply OrderHom.ext
  funext k
  have hfirst := insertLeftStep_face ν₁ j₁ k
  have hsecond := insertLeftStep_face ν₂ j₁ k
  simp only [← hμ, ← hr] at hsecond
  have hcoordinates := hfirst.symm.trans hsecond
  apply Prod.ext
  · exact Fin.succAbove_right_injective
      (congrArg (fun z : Index (p + 1) × Index q => z.1) hcoordinates)
  · exact congrArg (fun z : Index (p + 1) × Index q => z.2) hcoordinates

/-- The insert-right map is injective. -/
lemma insertRightStep_injective {p q : ℕ}
    (k₁ k₂ : Fin (q + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertRightStep ν₁ k₁ = insertRightStep ν₂ k₂)
    (hr : insertRightIndex ν₁ k₁ = insertRightIndex ν₂ k₂) :
    k₁ = k₂ ∧ ν₁ = ν₂ := by
  -- By comparing the coordinates of the last elements, we can conclude that k₁ = k₂.
  have hk : k₁ = k₂ := by
    unfold Shuffle.insertRightStep at hμ;
    simp_all +decide only [insertRightStepFun, Fin.val_fin_lt, Subtype.mk.injEq, OrderHom.mk.injEq,
        Fin.ext_iff];
    replace hμ := congr_fun hμ ( ν₂.insertRightIndex k₂ ); aesop;
  have := insertRightStep_face ν₁ k₁; have := insertRightStep_face ν₂ k₁; aesop;


end Shuffle

end D5.S3.HomologicalAlgebra.EilenbergZilber
