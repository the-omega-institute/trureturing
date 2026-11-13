/- GID: D5/S1/Words/LatticePaths/KotesovecA263160
   generality: I
   mirror-B: D5/B/S1/Words/LatticePaths/KotesovecA263160
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: First-zero lattice paths and the diagonal OEIS A263160 limit. -/

import D5.S1.Words.LatticePaths.MatharA379464Counting
import Mathlib.Analysis.SumIntegralExpDecay
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# First-zero lattice paths and the OEIS A263160 limit

The labelled ordered first-zero count is defined directly by finite words.
The complete all-index root limit is `diagonal_limit`; it uses no fixed-dimension
hypothesis. Source: OEIS A263160 revision 21 and A263159 revision 16.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/29912.

Definitions have proof_shape: bind-only and are consumed by the counting results.
The newly authored public theorems have proof_shape: content after expansion of
the same-delivery helpers. The live constructions are the coordinate-length
induction, row/column equivalence, terminal/internal append partition, uniform
series estimates, optimized positive term, and quantitative diagonal squeeze.
The final external assertion has prospective admission_basis: open-problem-resolution;
supporting counting content has prospective admission_basis: escape-witness.
No claim of worldwide priority or completed repository settlement is made.
The unfinished source-bound registration audit is tracked at
https://github.com/the-omega-institute/trureturing/issues/29924.
All statements are unbounded symbolic mathematics; utility: none.
-/

open scoped BigOperators Topology
open Filter


namespace D5.S1.Words.LatticePaths.KotesovecA263160

attribute [local instance] Classical.propDecidable

/-- A labelled nonempty set of coordinates decremented by a single step. -/
abbrev Step (d : ℕ) := {s : Finset (Fin d) // s.Nonempty}

/-- Number of decrements of coordinate `i` in an ordered word. -/
def decrements {d : ℕ} (w : List (Step d)) (i : Fin d) : ℕ :=
  w.countP (fun s => decide (i ∈ s.val))

/-- The literal stopping rule, including the immediate empty path convention. -/
def FirstZero {d : ℕ} (h : ℕ) (w : List (Step d)) : Prop :=
  if h = 0 ∨ d = 0 then w = [] else
    (∀ r < w.length, ∀ i, decrements (w.take r) i < h) ∧
      ∃ i, decrements w i = h

/-- The finite count of literal first-zero paths from height `h` in `d` coordinates. -/
noncomputable def paths (d h : ℕ) : ℕ := by
  classical
  exact ∑ t ∈ Finset.range (d * h + 1),
    Fintype.card {w : Fin t → Step d // FirstZero h (List.ofFn w)}

/-- The main diagonal of the first-zero path array. -/
noncomputable def a (n : ℕ) : ℕ := paths n n

private theorem decrements_append {d : ℕ} (u v : List (Step d)) (i : Fin d) :
    decrements (u ++ v) i = decrements u i + decrements v i := by
  simp [decrements]

private theorem decrements_take_le {d : ℕ} (w : List (Step d)) (r : ℕ) (i : Fin d) :
    decrements (w.take r) i ≤ decrements w i := by
  have he := congrArg (fun l => decrements l i) (List.take_append_drop r w)
  rw [decrements_append] at he
  omega

private theorem length_le_total_decrements {d : ℕ} (w : List (Step d)) :
    w.length ≤ ∑ i, decrements w i := by
  induction w with
  | nil => simp [decrements]
  | cons s w ih =>
    have hs : 1 ≤ s.val.card := s.property.card_pos
    have hc : (∑ i : Fin d, if i ∈ s.val then 1 else 0) = s.val.card := by
      simp
    simp only [List.length_cons, decrements, List.countP_cons, decide_eq_true_eq,
      Finset.sum_add_distrib]
    change w.length + 1 ≤ (∑ i : Fin d, decrements w i) +
      ∑ i : Fin d, if i ∈ s.val then 1 else 0
    rw [hc]
    omega

private theorem internal_length_bound {d m : ℕ} (w : List (Step d))
    (hw : ∀ i, decrements w i ≤ m) : w.length ≤ d * m := by
  calc
    w.length ≤ ∑ i, decrements w i := length_le_total_decrements w
    _ ≤ ∑ _ : Fin d, m := Finset.sum_le_sum (fun i _ => hw i)
    _ = d * m := by simp

/-- Every literal path lies in the finite length range used by `paths`. -/
theorem first_zero_length_bound {d h : ℕ} {w : List (Step d)}
    (hw : FirstZero h w) : w.length ≤ d * h := by
  by_cases hz : h = 0 ∨ d = 0
  · have he : w = [] := by simpa [FirstZero, hz] using hw
    simp [he]
  · rw [FirstZero, ite_eq_right hz] at hw
    have hh : 0 < h := by omega
    have hd : 0 < d := by omega
    have hlen : 0 < w.length := by
      by_contra hn
      have he : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      rcases hw.2 with ⟨i, hi⟩
      simp [he, decrements] at hi
      omega
    have ht : ∀ i, decrements (w.take (w.length - 1)) i ≤ h - 1 := by
      intro i
      have := hw.1 (w.length - 1) (by omega) i
      omega
    have hb := internal_length_bound (w.take (w.length - 1)) ht
    simp only [List.length_take, min_eq_left (Nat.sub_le _ _)] at hb
    have hm : d * (h - 1) + d = d * h := by
      calc
        _ = d * ((h - 1) + 1) := by ring
        _ = d * h := by rw [Nat.sub_add_cancel hh]
    omega



/-- Number of internal words of a specified length with each row budget at most `m`. -/
noncomputable def internal_words (d m t : ℕ) : ℕ :=
  MatharA379464Counting.count (Step d) t (fun w => ∀ i, decrements w i ≤ m)

private abbrev Rows (k m : ℕ) := {s : Finset (Fin k) // s.card ≤ m}

private theorem rows_card (k m : ℕ) :
    Fintype.card (Rows k m) = ∑ r ∈ Finset.range (m + 1), k.choose r := by
  classical
  let e : Rows k m ≃ (Σ r : Fin (m + 1), {s : Finset (Fin k) // s.card = r.val}) :=
    { toFun := fun s => ⟨⟨s.val.card, by omega⟩, ⟨s.val, rfl⟩⟩
      invFun := fun r => ⟨r.2.val, by have := r.2.property; have := r.1.isLt; omega⟩
      left_inv := by intro s; rfl
      right_inv := by rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩; cases hs; rfl }
  simpa only [Fintype.card_sigma, Fintype.card_finset_len, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range] using Fintype.card_congr e

private noncomputable def columnEquiv (d : ℕ) : Option (Step d) ≃ Finset (Fin d) where
  toFun o := match o with | none => ∅ | some s => s.val
  invFun s := if hs : s.Nonempty then some ⟨s, hs⟩ else none
  left_inv o := by
    cases o with
    | none => simp
    | some s => simp [s.property]
  right_inv s := by
    by_cases hs : s.Nonempty
    · simp [hs]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

private theorem countP_ofFn {α : Type} {k : ℕ} (w : Fin k → α) (p : α → Bool) :
    (List.ofFn w).countP p = (Finset.univ.filter fun j => p (w j)).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.card_filter_univ_succ]
    rw [ih]
    split_ifs <;> omega

private theorem erase_decrements {d : ℕ} (l : List (Option (Step d))) (i : Fin d) :
    decrements (l.filterMap id) i = l.countP (fun o => decide (i ∈ columnEquiv d o)) := by
  induction l with
  | nil => simp [decrements]
  | cons o l ih =>
    cases o with
    | none => simpa [columnEquiv, decrements] using ih
    | some s =>
      by_cases hs : i ∈ s.val
      · simpa [columnEquiv, decrements, List.countP_cons, hs] using congrArg Nat.succ ih
      · simpa [columnEquiv, decrements, List.countP_cons, hs] using ih


private noncomputable def columnRowsEquiv (d k m : ℕ) :
    {w : Fin k → Option (Step d) //
      ∀ i, decrements ((List.ofFn w).filterMap id) i ≤ m} ≃ (Fin d → Rows k m) := by
  classical
  let col (w : Fin k → Option (Step d)) (i : Fin d) : Finset (Fin k) :=
    Finset.univ.filter (fun j => i ∈ columnEquiv d (w j))
  have hcount (w : Fin k → Option (Step d)) (i : Fin d) :
      decrements ((List.ofFn w).filterMap id) i = (col w i).card := by
    rw [erase_decrements, countP_ofFn]
    simp only [col, decide_eq_true_eq]
  refine
    { toFun := fun w i => ⟨col w.val i, by rw [← hcount]; exact w.property i⟩
      invFun := fun rows => ⟨(fun j => (columnEquiv d).symm
        (Finset.univ.filter fun i => j ∈ (rows i).val)), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    rw [hcount]
    convert (rows i).property using 1
    congr 1
    ext j
    simp [col]
  · intro w
    apply Subtype.ext
    funext j
    apply (columnEquiv d).injective
    simp only [Equiv.apply_symm_apply]
    ext i
    simp [col]
  · intro rows
    funext i
    apply Subtype.ext
    ext j
    simp [col]

/-- Row budgets are the binomial transform of words with no empty columns. -/
theorem insertion_identity (d m k : ℕ) :
    (∑ r ∈ Finset.range (m + 1), k.choose r) ^ d =
      ∑ t ∈ Finset.range (k + 1), k.choose t * internal_words d m t := by
  classical
  have hc := Fintype.card_congr (columnRowsEquiv d k m)
  have hi := MatharA379464Counting.insertion_formula (Step d) k
    (fun w => ∀ i, decrements w i ≤ m)
  rw [Fintype.card_fun, rows_card, Fintype.card_fin] at hc
  have hcount : (∑ r ∈ Finset.range (m + 1), k.choose r) ^ d =
      MatharA379464Counting.count (Option (Step d)) k
        (fun l => ∀ i, decrements (l.filterMap id) i ≤ m) := by
    simpa only [MatharA379464Counting.count, ← Nat.card_eq_fintype_card] using hc.symm
  exact hcount.trans hi



private theorem internal_words_vanish (d m t : ℕ) (ht : d * m < t) :
    internal_words d m t = 0 := by
  classical
  unfold internal_words MatharA379464Counting.count
  let : IsEmpty {w : Fin t → Step d // ∀ i, decrements (List.ofFn w) i ≤ m} :=
    ⟨fun w => by
      have hl := internal_length_bound (List.ofFn w.val) w.property
      simp only [List.length_ofFn] at hl
      omega⟩
  have hc : Nat.card {w : Fin t → Step d //
      ∀ i, decrements (List.ofFn w) i ≤ m} = 0 :=
    Nat.card_eq_zero.mpr (Or.inl inferInstance)
  simpa only [← Nat.card_eq_fintype_card] using hc

private theorem insertion_truncated (d m k : ℕ) :
    (∑ r ∈ Finset.range (m + 1), k.choose r) ^ d =
      ∑ t ∈ Finset.range (d * m + 1), k.choose t * internal_words d m t := by
  rw [insertion_identity]
  by_cases hk : k ≤ d * m
  · apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hk 1))
    intro t ht hn
    have hkt : k < t := by simp only [Finset.mem_range] at *; omega
    simp [Nat.choose_eq_zero_of_lt hkt]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro t ht hn
    have hmt : d * m < t := by simp only [Finset.mem_range] at *; omega
    rw [internal_words_vanish d m t hmt, mul_zero]

private theorem choose_half_hasSum (t : ℕ) :
    HasSum (fun k : ℕ => (k.choose t : ℝ) * (1 / 2 : ℝ) ^ k) 2 := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one t
    (r := (1 / 2 : ℝ)) (by norm_num)).mul_left ((1 / 2 : ℝ) ^ t)
  have hv : (1 / 2 : ℝ) ^ t * (1 / (1 - 1 / 2 : ℝ) ^ (t + 1)) = 2 := by
    norm_num [pow_succ]
    field_simp
  have hs : HasSum (fun k : ℕ => ((k + t).choose t : ℝ) * (1 / 2 : ℝ) ^ (k + t)) 2 := by
    convert h using 1
    · ext k
      rw [pow_add]
      ring
    · exact hv.symm
  have hz : ∑ k ∈ Finset.range t, (k.choose t : ℝ) * (1 / 2 : ℝ) ^ k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk)]
  simpa only [hz, add_zero] using (hasSum_nat_add_iff (f := fun k : ℕ => (k.choose t : ℝ) * (1 / 2 : ℝ) ^ k) t).mp hs

/-- The geometric positive series sums to twice the finite internal-word count. -/
theorem internal_hasSum (d m : ℕ) :
    HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k *
      ((∑ r ∈ Finset.range (m + 1), k.choose r : ℕ) : ℝ) ^ d)
      (2 * ∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ)) := by
  have hs := hasSum_sum (s := Finset.range (d * m + 1))
    (fun t _ => (choose_half_hasSum t).mul_right (internal_words d m t : ℝ))
  convert hs using 1
  · ext k
    have hi := congrArg (fun x : ℕ => (x : ℝ)) (insertion_truncated d m k)
    push_cast at hi ⊢
    rw [hi]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  · simp [Finset.mul_sum]

private theorem first_zero_append_iff {d m : ℕ} (hd : 0 < d)
    (w : List (Step d)) (s : Step d) :
    FirstZero (m + 1) (w ++ [s]) ↔
      (∀ i, decrements w i ≤ m) ∧
        ¬ (∀ i, decrements (w ++ [s]) i ≤ m) := by
  have hz : ¬ (m + 1 = 0 ∨ d = 0) := by omega
  rw [FirstZero, ite_eq_right hz]
  constructor
  · rintro ⟨hp, i, hi⟩
    refine ⟨?_, ?_⟩
    · intro j
      have hh := hp w.length (by simp) j
      simpa only [List.take_append_length] using Nat.le_of_lt_succ hh
    · intro hall
      have := hall i
      omega
  · rintro ⟨hp, hn⟩
    refine ⟨?_, ?_⟩
    · intro r hr i
      have hrw : r ≤ w.length := by
        simp only [List.length_append, List.length_singleton] at hr
        omega
      rw [List.take_append_of_le_length hrw]
      have := decrements_take_le w r i
      have := hp i
      omega
    · push Not at hn
      obtain ⟨i, hi⟩ := hn
      refine ⟨i, ?_⟩
      have hb := hp i
      rw [decrements_append] at hi ⊢
      have hs : decrements [s] i ≤ 1 := by
        simp only [decrements, List.countP_cons, List.countP_nil]
        split_ifs <;> omega
      omega

private theorem first_zero_ofFn_iff {d m t : ℕ} (hd : 0 < d)
    (w : Fin (t + 1) → Step d) :
    FirstZero (m + 1) (List.ofFn w) ↔
      (∀ i, decrements (List.ofFn (fun j : Fin t => w j.castSucc)) i ≤ m) ∧
        ¬ (∀ i, decrements (List.ofFn w) i ≤ m) := by
  conv_lhs => rw [List.ofFn_succ', List.concat_eq_append]
  rw [first_zero_append_iff hd]
  simp only [← List.concat_eq_append, ← List.ofFn_succ']

private noncomputable def parentEquiv (d m t : ℕ) :
    {w : Fin (t + 1) → Step d //
      ∀ i, decrements (List.ofFn (fun j : Fin t => w j.castSucc)) i ≤ m} ≃
    ({w : Fin t → Step d // ∀ i, decrements (List.ofFn w) i ≤ m} × Step d) where
  toFun w := (⟨fun j => w.val j.castSucc, w.property⟩, w.val (Fin.last t))
  invFun w := ⟨Fin.snoc w.1.val w.2, by simpa using w.1.property⟩
  left_inv w := by
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  right_inv w := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      simp
    · simp

private noncomputable def branchEquiv (d m t : ℕ) (hd : 0 < d) :
    {w : Fin (t + 1) → Step d //
      ∀ i, decrements (List.ofFn (fun j : Fin t => w j.castSucc)) i ≤ m} ≃
    ({w : Fin (t + 1) → Step d // ∀ i, decrements (List.ofFn w) i ≤ m} ⊕
      {w : Fin (t + 1) → Step d // FirstZero (m + 1) (List.ofFn w)}) := by
  classical
  have hparent (w : Fin (t + 1) → Step d)
      (hw : ∀ i, decrements (List.ofFn w) i ≤ m) :
      ∀ i, decrements (List.ofFn (fun j : Fin t => w j.castSucc)) i ≤ m := by
    intro i
    have hl := decrements_take_le (List.ofFn w) t i
    have he : (List.ofFn w).take t = List.ofFn (fun j : Fin t => w j.castSucc) := by
      rw [List.ofFn_succ', List.concat_eq_append]
      simp
    rw [he] at hl
    exact hl.trans (hw i)
  refine
    { toFun := fun w => if hf : ∀ i, decrements (List.ofFn w.val) i ≤ m
        then Sum.inl ⟨w.val, hf⟩
        else Sum.inr ⟨w.val, (first_zero_ofFn_iff hd w.val).mpr ⟨w.property, hf⟩⟩
      invFun := fun w => match w with
        | Sum.inl w => ⟨w.val, hparent w.val w.property⟩
        | Sum.inr w => ⟨w.val, ((first_zero_ofFn_iff hd w.val).mp w.property).1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    dsimp only
    split_ifs <;> rfl
  · intro w
    cases w with
    | inl w => simp only [dite_eq_left w.property]
    | inr w =>
      simp only [dite_eq_right ((first_zero_ofFn_iff hd w.val).mp w.property).2]

/-- Appending a step to an internal word either stays internal or terminates once. -/
private theorem terminal_recurrence (d m t : ℕ) (hd : 0 < d) :
    internal_words d m (t + 1) +
      Fintype.card {w : Fin (t + 1) → Step d // FirstZero (m + 1) (List.ofFn w)} =
      internal_words d m t * (2 ^ d - 1) := by
  classical
  have he := Fintype.card_congr ((branchEquiv d m t hd).symm.trans (parentEquiv d m t))
  have hstep : Fintype.card (Step d) = 2 ^ d - 1 := by
    have h := Fintype.card_subtype_compl (fun s : Finset (Fin d) => s = ∅)
    simp [Step, Finset.nonempty_iff_ne_empty]
  rw [Fintype.card_sum, Fintype.card_prod, hstep] at he
  simpa only [internal_words, MatharA379464Counting.count,
    ← Nat.card_eq_fintype_card] using he

private noncomputable def terminalCount (d h t : ℕ) : ℕ :=
  Fintype.card {w : Fin t → Step d // FirstZero h (List.ofFn w)}

private theorem terminalCount_zero (d m : ℕ) (hd : 0 < d) :
    terminalCount d (m + 1) 0 = 0 := by
  classical
  have hz : ¬ (m + 1 = 0 ∨ d = 0) := by omega
  have hempty : IsEmpty {w : Fin 0 → Step d // FirstZero (m + 1) (List.ofFn w)} :=
    ⟨fun w => by
      have hw := w.property
      rw [FirstZero, ite_eq_right hz] at hw
      obtain ⟨i, hi⟩ := hw.2
      simp [decrements] at hi⟩
  have := hempty
  exact Fintype.card_eq_zero

private theorem terminalCount_vanish (d m t : ℕ) (hd : 0 < d)
    (ht : d * m + 1 < t) : terminalCount d (m + 1) t = 0 := by
  classical
  have hz : ¬ (m + 1 = 0 ∨ d = 0) := by omega
  let : IsEmpty {w : Fin t → Step d // FirstZero (m + 1) (List.ofFn w)} :=
    ⟨fun w => by
      have hp := (by simpa only [FirstZero, ite_eq_right hz] using w.property :
        (∀ r < (List.ofFn w.val).length, ∀ i,
          decrements ((List.ofFn w.val).take r) i < m + 1) ∧
          ∃ i, decrements (List.ofFn w.val) i = m + 1).1
      have hb := internal_length_bound ((List.ofFn w.val).take (t - 1))
        (fun i => Nat.le_of_lt_succ (hp (t - 1) (by simp; omega) i))
      simp only [List.length_take, List.length_ofFn, min_eq_left (Nat.sub_le _ _)] at hb
      omega⟩
  exact Fintype.card_eq_zero

private theorem internal_words_zero (d m : ℕ) : internal_words d m 0 = 1 := by
  classical
  have he : {w : Fin 0 → Step d // ∀ i, decrements (List.ofFn w) i ≤ m} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨Fin.elim0, by simp [decrements]⟩
      left_inv := by intro w; apply Subtype.ext; funext i; exact Fin.elim0 i
      right_inv := by intro w; cases w; rfl }
  have hc := Fintype.card_congr he
  simpa only [internal_words, MatharA379464Counting.count,
    ← Nat.card_eq_fintype_card, Nat.card_unique] using hc

/-- The full-branch first-zero count is determined by the finite internal words. -/
theorem paths_eq_internal (d m : ℕ) (hd : 0 < d) :
    paths d (m + 1) = 1 + (2 ^ d - 2) *
      ∑ t ∈ Finset.range (d * m + 1), internal_words d m t := by
  classical
  let N := d * m
  let I := ∑ t ∈ Finset.range (N + 1), internal_words d m t
  have hpaths : paths d (m + 1) =
      ∑ t ∈ Finset.range (N + 1), terminalCount d (m + 1) (t + 1) := by
    unfold paths
    change (∑ t ∈ Finset.range (d * (m + 1) + 1), terminalCount d (m + 1) t) = _
    have hsub : Finset.range (N + 2) ⊆ Finset.range (d * (m + 1) + 1) := by
      apply Finset.range_mono
      dsimp [N]
      nlinarith
    rw [← Finset.sum_subset hsub (fun t ht hn =>
      terminalCount_vanish d m t hd (by simp only [Finset.mem_range] at *; dsimp [N] at *; omega))]
    rw [Finset.sum_range_succ']
    simp only [terminalCount_zero d m hd, add_zero]
  have hsum := Finset.sum_congr (s₁ := Finset.range (N + 1)) (s₂ := Finset.range (N + 1))
    rfl (fun t _ => terminal_recurrence d m t hd)
  change (∑ t ∈ Finset.range (N + 1),
      (internal_words d m (t + 1) + terminalCount d (m + 1) (t + 1))) =
    ∑ t ∈ Finset.range (N + 1), internal_words d m t * (2 ^ d - 1) at hsum
  rw [Finset.sum_add_distrib, ← hpaths, ← Finset.sum_mul] at hsum
  have hshift : (∑ t ∈ Finset.range (N + 1), internal_words d m (t + 1)) + 1 = I := by
    have ha := Finset.sum_range_succ (f := internal_words d m) (N + 1)
    have hb := Finset.sum_range_succ' (f := internal_words d m) (N + 1)
    rw [internal_words_zero] at hb
    rw [internal_words_vanish d m (N + 1) (by dsimp [N]; omega), add_zero] at ha
    exact hb.symm.trans ha
  have htwo : 2 ≤ 2 ^ d := by
    simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd)
  have hq : 2 ^ d - 1 = (2 ^ d - 2) + 1 := by omega
  rw [hq, Nat.mul_add, Nat.mul_one] at hsum
  change (∑ t ∈ Finset.range (N + 1), internal_words d m (t + 1)) +
    paths d (m + 1) = I * (2 ^ d - 2) + I at hsum
  rw [Nat.mul_comm I (2 ^ d - 2)] at hsum
  change paths d (m + 1) = 1 + (2 ^ d - 2) * I
  omega

private theorem row_sum_le_choose (k m : ℕ) :
    (∑ r ∈ Finset.range (m + 1), k.choose r) ≤ (k + m).choose m := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_le_sum
  intro r hr
  exact Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.sub_le m r))

private theorem row_upper (k m : ℕ) :
    ((∑ r ∈ Finset.range (m + 1), k.choose r : ℕ) : ℝ) ≤
      ((k + m : ℕ) : ℝ) ^ m / (m.factorial : ℝ) :=
  (Nat.cast_le.mpr (row_sum_le_choose k m)).trans (Nat.choose_le_pow_div m (k + m))

private theorem row_lower (k m : ℕ) :
    (((k + 1 - m : ℕ) : ℝ) ^ m / (m.factorial : ℝ)) ≤
      ((∑ r ∈ Finset.range (m + 1), k.choose r : ℕ) : ℝ) := by
  apply (Nat.pow_le_choose m k).trans
  exact Nat.cast_le.mpr (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_self m)))

/-- Uniform binomial envelopes for the internal-word series, with both parameters free. -/
private theorem series_term_bounds (d m k : ℕ) :
    (1 / 2 : ℝ) ^ k * ((k + 1 - m : ℕ) : ℝ) ^ (m * d) /
        (m.factorial : ℝ) ^ d ≤
      (1 / 2 : ℝ) ^ k *
        ((∑ r ∈ Finset.range (m + 1), k.choose r : ℕ) : ℝ) ^ d ∧
    (1 / 2 : ℝ) ^ k *
        ((∑ r ∈ Finset.range (m + 1), k.choose r : ℕ) : ℝ) ^ d ≤
      (1 / 2 : ℝ) ^ k * ((k + m : ℕ) : ℝ) ^ (m * d) /
        (m.factorial : ℝ) ^ d := by
  constructor
  · have h := pow_le_pow_left₀ (by positivity) (row_lower k m) d
    have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k)
    simpa only [div_pow, ← pow_mul, mul_div_assoc] using this
  · have h := pow_le_pow_left₀ (by positivity) (row_upper k m) d
    have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k)
    simpa only [div_pow, ← pow_mul, mul_div_assoc] using this

private theorem half_pow_exp (k : ℕ) :
    (1 / 2 : ℝ) ^ k = Real.exp (-(Real.log 2 * (k : ℝ))) := by
  rw [← neg_mul, Real.exp_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp [one_div]

private theorem shifted_moment_bound (m N M : ℕ) :
    (∑ k ∈ Finset.range M, (1 / 2 : ℝ) ^ k * ((k + m : ℕ) : ℝ) ^ N) ≤
      2 ^ (m + 1) * (N.factorial : ℝ) / Real.log 2 ^ (N + 1) := by
  let f := fun j : ℕ => (j : ℝ) ^ N * Real.exp (-(Real.log 2 * (j : ℝ)))
  have hf (j : ℕ) : 0 ≤ f j := by dsimp [f]; positivity
  have hshift : ∑ k ∈ Finset.range M, (1 / 2 : ℝ) ^ k * ((k + m : ℕ) : ℝ) ^ N =
      (2 : ℝ) ^ m * ∑ k ∈ Finset.range M, f (m + k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    rw [← half_pow_exp, pow_add]
    have hm : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    rw [Nat.add_comm m k]
    calc
      _ = ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m) *
          ((1 / 2 : ℝ) ^ k * ((k + m : ℕ) : ℝ) ^ N) := by rw [hm, one_mul]
      _ = _ := by ring
  have hle : ∑ k ∈ Finset.range M, f (m + k) ≤
      ∑ j ∈ Finset.range (m + M), f j := by
    rw [Finset.sum_range_add]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => hf j))
  have hbound := sum_Ico_pow_mul_exp_neg_le (k := N) (M := m + M)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp only [← Finset.range_eq_Ico, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hbound
  rw [hshift]
  calc
    _ ≤ (2 : ℝ) ^ m * ∑ j ∈ Finset.range (m + M), f j := by gcongr
    _ ≤ (2 : ℝ) ^ m * (2 * (N.factorial : ℝ) / Real.log 2 ^ (N + 1)) := by
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- A factorial-scale upper bound uniform in the two row-budget parameters. -/
theorem internal_count_upper (d m : ℕ) :
    (2 : ℝ) * ∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ) ≤
      2 ^ (m + 1) * ((m * d).factorial : ℝ) /
        (Real.log 2 ^ (m * d + 1) * (m.factorial : ℝ) ^ d) := by
  have hs := (internal_hasSum d m).tendsto_sum_nat
  apply le_of_tendsto hs
  filter_upwards [] with M
  calc
    _ ≤ ∑ k ∈ Finset.range M,
        (1 / 2 : ℝ) ^ k * ((k + m : ℕ) : ℝ) ^ (m * d) /
          (m.factorial : ℝ) ^ d :=
      Finset.sum_le_sum (fun k _ => (series_term_bounds d m k).2)
    _ = (∑ k ∈ Finset.range M,
        (1 / 2 : ℝ) ^ k * ((k + m : ℕ) : ℝ) ^ (m * d)) /
          (m.factorial : ℝ) ^ d := by rw [Finset.sum_div]
    _ ≤ (2 ^ (m + 1) * ((m * d).factorial : ℝ) / Real.log 2 ^ (m * d + 1)) /
          (m.factorial : ℝ) ^ d := by
      apply div_le_div_of_nonneg_right (shifted_moment_bound m (m * d) M)
      positivity
    _ = _ := by rw [div_div]

/-- Every positive-series term gives a lower bound for the finite internal count. -/
theorem internal_count_lower (d m k : ℕ) :
    (1 / 2 : ℝ) ^ k * ((k + 1 - m : ℕ) : ℝ) ^ (m * d) /
        (m.factorial : ℝ) ^ d ≤
      2 * ∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ) := by
  apply (series_term_bounds d m k).1.trans
  have h := sum_le_hasSum (s := {k}) (fun j _ => by positivity) (internal_hasSum d m)
  simpa using h

/-- Logarithmic factorial bounds with an optimized single term for the lower estimate. -/
theorem internal_log_bounds (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    let N := m * d
    let H := 2 * ∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ)
    (N : ℝ) * Real.log ((N : ℝ) / Real.log 2) - (N : ℝ) -
        ((m : ℝ) + 1) * Real.log 2 - (d : ℝ) * Real.log (m.factorial : ℝ) ≤ Real.log H ∧
    Real.log H ≤ ((m : ℝ) + 1) * Real.log 2 + Real.log (N.factorial : ℝ) -
        ((N : ℝ) + 1) * Real.log (Real.log 2) -
          (d : ℝ) * Real.log (m.factorial : ℝ) := by
  dsimp only
  let N := m * d
  let c := Real.log 2
  let H := 2 * ∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hN : (0 : ℝ) < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hm hd
  have hF : (0 : ℝ) < m.factorial := by positivity
  have hH : 0 < H := by
    have hl := internal_count_lower d m m
    have ht : (0 : ℝ) < (1 / 2 : ℝ) ^ m *
        ((m + 1 - m : ℕ) : ℝ) ^ (m * d) / (m.factorial : ℝ) ^ d := by
      simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_pow, mul_one]
      positivity
    exact ht.trans_le hl
  constructor
  · let x := (N : ℝ) / c
    let k := Nat.ceil x + m
    have hx : 0 < x := div_pos hN hc
    have hbase : x ≤ ((k + 1 - m : ℕ) : ℝ) := by
      have hh := Nat.le_ceil x
      have he : k + 1 - m = Nat.ceil x + 1 := by dsimp [k]; omega
      rw [he, Nat.cast_add, Nat.cast_one]
      linarith
    have hk : (k : ℝ) ≤ x + (m : ℝ) + 1 := by
      have hh := Nat.ceil_lt_add_one hx.le
      dsimp [k]
      push_cast
      linarith
    have hl : Real.exp (-(c * (k : ℝ))) * x ^ N / (m.factorial : ℝ) ^ d ≤ H := by
      calc
        _ ≤ (1 / 2 : ℝ) ^ k * ((k + 1 - m : ℕ) : ℝ) ^ N /
            (m.factorial : ℝ) ^ d := by
          rw [half_pow_exp]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hbase N) (by positivity)
        _ ≤ H := internal_count_lower d m k
    have ht : 0 < Real.exp (-(c * (k : ℝ))) * x ^ N / (m.factorial : ℝ) ^ d := by positivity
    have hh := Real.log_le_log ht hl
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_exp, Real.log_pow, Real.log_pow] at hh
    have hcx : c * x = N := by dsimp [x]; field_simp
    have hck := mul_le_mul_of_nonneg_left hk hc.le
    change (N : ℝ) * Real.log x - (N : ℝ) - ((m : ℝ) + 1) * c -
      (d : ℝ) * Real.log (m.factorial : ℝ) ≤ Real.log H
    nlinarith
  · have hh := Real.log_le_log hH (internal_count_upper d m)
    have hu : Real.log ((2 : ℝ) ^ (m + 1) * (N.factorial : ℝ) /
        (c ^ (N + 1) * (m.factorial : ℝ) ^ d)) =
        ((m : ℝ) + 1) * c + Real.log (N.factorial : ℝ) -
          ((N : ℝ) + 1) * Real.log c - (d : ℝ) * Real.log (m.factorial : ℝ) := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      dsimp [c]
      ring
    change Real.log H ≤ Real.log ((2 : ℝ) ^ (m + 1) * (N.factorial : ℝ) /
      (c ^ (N + 1) * (m.factorial : ℝ) ^ d)) at hh
    rw [hu] at hh
    exact hh

private theorem paths_log_comparison (d m : ℕ) (hd : 2 ≤ d) :
    let H := 2 * ∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ)
    0 < (paths d (m + 1) : ℝ) ∧
      Real.log H - Real.log 2 ≤ Real.log (paths d (m + 1) : ℝ) ∧
      Real.log (paths d (m + 1) : ℝ) ≤
        (d : ℝ) * Real.log 2 + Real.log H - Real.log 2 := by
  dsimp only
  let I := ∑ t ∈ Finset.range (d * m + 1), internal_words d m t
  have hi : 1 ≤ I := by
    calc
      _ = internal_words d m 0 := (internal_words_zero d m).symm
      _ ≤ I := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
  have hpow : 4 ≤ 2 ^ d := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
  have hb := paths_eq_internal d m (by omega)
  change paths d (m + 1) = 1 + (2 ^ d - 2) * I at hb
  have hcoeff : 1 ≤ 2 ^ d - 2 := by omega
  have hlo : I ≤ paths d (m + 1) := by nlinarith
  have hhi : paths d (m + 1) ≤ 2 ^ d * I := by
    have hp : 2 ^ d = (2 ^ d - 2) + 2 := by omega
    rw [hp]
    nlinarith
  have hiR : (0 : ℝ) < I := by exact_mod_cast (show 0 < I by omega)
  have hbR : (0 : ℝ) < paths d (m + 1) := by exact_mod_cast (show 0 < paths d (m + 1) by omega)
  have hloR := Real.log_le_log hiR (show (I : ℝ) ≤ paths d (m + 1) by exact_mod_cast hlo)
  have hhiR := Real.log_le_log hbR (show (paths d (m + 1) : ℝ) ≤ (2 : ℝ)^d * I by exact_mod_cast hhi)
  rw [Real.log_mul (by positivity) (ne_of_gt hiR), Real.log_pow] at hhiR
  have hH : Real.log (2 * ∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ)) =
      Real.log 2 + Real.log (I : ℝ) := by
    have he : (∑ t ∈ Finset.range (d * m + 1), (internal_words d m t : ℝ)) = (I : ℝ) := by
      dsimp [I]
      norm_cast
    rw [he, Real.log_mul (by norm_num) (ne_of_gt hiR)]
  rw [hH]
  exact ⟨hbR, by linarith, by linarith⟩

private theorem log_factorial_bounds (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) ∧
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  constructor
  · simpa only [Real.sum_log_eq_log_factorial] using (Real.le_sum_log_nat (N := n))
  · have h := Real.sum_log_le (x := (n : ℝ)) (by exact_mod_cast hn)
    simpa only [Nat.floor_natCast, Real.sum_log_eq_log_factorial] using h

set_option maxHeartbeats 1000000 in
/-- A diagonal error bound at the scale required by the conjecture. -/
theorem diagonal_log_estimate (n : ℕ) (hn : 2 ≤ n) :
    |Real.log (a n : ℝ) - (n : ℝ) ^ 2 *
        (Real.log (n : ℝ) - Real.log (Real.log 2))| ≤
      (n : ℝ) * (4 * Real.log (n : ℝ) + 6 + 2 * |Real.log (Real.log 2)|) := by
  let m := n - 1
  let N := m * n
  let c := Real.log 2
  have hm : 0 < m := by dsimp [m]; omega
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmc : (m : ℝ) = (n : ℝ) - 1 := by dsimp [m]; rw [Nat.cast_sub (by omega)]; norm_num
  have hNc : (N : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    dsimp [N]
    push_cast
    rw [hmc]
    ring
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc1 : c ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlogm : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hmR (by rw [hmc]; linarith)
  have hlogN : Real.log (N : ℝ) = Real.log (n : ℝ) + Real.log (m : ℝ) := by
    dsimp [N]
    push_cast
    rw [Real.log_mul (ne_of_gt hmR) (by positivity)]
    ring
  have hlogNc : Real.log ((N : ℝ) / c) =
      Real.log (n : ℝ) + Real.log (m : ℝ) - Real.log c := by
    rw [Real.log_div (by positivity) (ne_of_gt hc), hlogN]
  have hi := internal_log_bounds n m hn0 hm
  have hp := paths_log_comparison n m hn
  have hfN := log_factorial_bounds N (Nat.mul_pos hm hn0)
  have hfm := log_factorial_bounds m hm
  dsimp only at hi hp
  change (N : ℝ) * Real.log ((N : ℝ) / c) - N - ((m : ℝ) + 1) * c -
      (n : ℝ) * Real.log (m.factorial : ℝ) ≤
        Real.log (2 * ∑ t ∈ Finset.range (n * m + 1), (internal_words n m t : ℝ)) ∧
      Real.log (2 * ∑ t ∈ Finset.range (n * m + 1), (internal_words n m t : ℝ)) ≤
        ((m : ℝ) + 1) * c + Real.log (N.factorial : ℝ) -
          ((N : ℝ) + 1) * Real.log c - (n : ℝ) * Real.log (m.factorial : ℝ) at hi
  have he : m + 1 = n := by dsimp [m]; omega
  rw [he] at hp
  change 0 < (a n : ℝ) ∧
      Real.log (2 * ∑ t ∈ Finset.range (n * m + 1), (internal_words n m t : ℝ)) - c ≤
        Real.log (a n : ℝ) ∧
      Real.log (a n : ℝ) ≤ (n : ℝ) * c +
        Real.log (2 * ∑ t ∈ Finset.range (n * m + 1), (internal_words n m t : ℝ)) - c at hp
  have hl : (N : ℝ) * (Real.log (n : ℝ) - Real.log c) -
      (n : ℝ) * (Real.log (m : ℝ) + c + 1) - c ≤ Real.log (a n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hfm.2 (by positivity : (0 : ℝ) ≤ n)
    rw [hlogNc] at hi
    simp only [hmc, hNc] at hi hmul ⊢
    nlinarith [hi.1, hp.2.1]
  have hu : Real.log (a n : ℝ) ≤
      (N : ℝ) * (Real.log (n : ℝ) - Real.log c) +
        (2 * (n : ℝ) - 1) * c + Real.log (N : ℝ) + 1 - Real.log c := by
    have hmul := mul_le_mul_of_nonneg_left hfm.1 (by positivity : (0 : ℝ) ≤ n)
    rw [hlogN]
    simp only [hmc, hNc] at hi hmul ⊢
    rw [hlogN] at hfN
    simp only [hNc, hmc] at hfN
    nlinarith [hi.2, hp.2.2, hfN.2]
  have hal : -|Real.log c| ≤ Real.log c := neg_abs_le _
  have hau : Real.log c ≤ |Real.log c| := le_abs_self _
  have han : 0 ≤ |Real.log c| := abs_nonneg _
  have hml := mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ n)
  have hcl := mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ n)
  have haln := mul_le_mul_of_nonneg_left hal (by positivity : (0 : ℝ) ≤ n)
  have haun := mul_le_mul_of_nonneg_left hau (by positivity : (0 : ℝ) ≤ n)
  have han1 := mul_nonneg (show (0 : ℝ) ≤ n - 1 by linarith) han
  have hln1 := mul_nonneg (show (0 : ℝ) ≤ n - 1 by linarith) hlogn
  rw [hlogN] at hu
  rw [hNc] at hl hu
  apply abs_le.mpr
  constructor <;> dsimp only [c] at * <;> nlinarith

/-- The complete all-index real-root limit conjectured for OEIS A263160. -/
theorem diagonal_limit :
    Tendsto (fun n : ℕ => Real.rpow (a n : ℝ) (1 / (n : ℝ) ^ 2) / (n : ℝ))
      atTop (nhds (1 / Real.log 2)) := by
  let c := Real.log 2
  let K := 6 + 2 * |Real.log c|
  let f := fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ) ^ 2 -
    Real.log (n : ℝ) + Real.log c
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hncast
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hncast
  have hE : Tendsto (fun n : ℕ => (4 * Real.log (n : ℝ) + K) / (n : ℝ))
      atTop (nhds 0) := by
    convert (hlog.const_mul 4).add (hinv.const_mul K) using 1
    · ext n
      simp only [div_eq_mul_inv]
      ring
    · simp
  have hb : ∀ᶠ n : ℕ in atTop,
      |f n| ≤ (4 * Real.log (n : ℝ) + K) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h := diagonal_log_estimate n hn
    have he : f n = (Real.log (a n : ℝ) - (n : ℝ)^2 *
        (Real.log (n : ℝ) - Real.log c)) / (n : ℝ)^2 := by
      dsimp [f]
      field_simp
      ring
    rw [he, abs_div, abs_of_pos (pow_pos hnR 2)]
    have hh := div_le_div_of_nonneg_right h (le_of_lt (pow_pos hnR 2))
    convert hh using 1
    dsimp [K, c]
    field_simp
    ring
  have hf : Tendsto f atTop (nhds 0) := squeeze_zero_norm' hb hE
  have hg : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ)^2 - Real.log (n : ℝ))
      atTop (nhds (-Real.log c)) := by
    convert hf.sub_const (Real.log c) using 1 <;> simp [f]
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hg
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hout : Real.exp (-Real.log c) = 1 / c := by
    rw [Real.exp_neg, Real.exp_log hc, one_div]
  rw [hout] at hexp
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := (paths_log_comparison n (n - 1) hn).1
  have hnEq : n - 1 + 1 = n := by omega
  rw [hnEq] at hp
  change 0 < (a n : ℝ) at hp
  change Real.exp (Real.log (a n : ℝ) / (n : ℝ)^2 - Real.log (n : ℝ)) =
    (a n : ℝ) ^ (1 / (n : ℝ)^2) / (n : ℝ)
  rw [Real.rpow_def_of_pos hp, Real.exp_sub, Real.exp_log hnR]
  congr 1
  congr 1
  ring

end D5.S1.Words.LatticePaths.KotesovecA263160
