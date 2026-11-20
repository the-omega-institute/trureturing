/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: A229637 column 1 vanishes and row 1 is C(k-1,2)2^(k-4), order-3 recurrence, sharp. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#297)
escape_witness: cnt_succ with ext_count (appending a letter to a canonical word: one same-colour
  extension, and two other admissible colours unless the word is constant, so
  c(L+2, m) + [L = m] = c(L+1, m-1) + 2 c(L+1, m)), and the least-order step of result
  (an order-two recurrence on (k-1)(k-2)2^(k-5) forces 8 = 0 from three consecutive indices).
proof_shape:
  horiz, betw, T, claim: source definitions; consumers: column_one, row_one, result.
  monoSet, cnt: private definitions; consumers: the word-count lemmas, row_one.
  canonicalDecidable, arrayCanonicalDecidable: instances for T and cnt.
  mono_snoc, canon_snoc, zero_of_canon, one_of_canon, valid_iff: content; consumer: ext_count.
  ext_count: content; consumer: cnt_succ.
  cnt_eq_sum, shift_sum, cnt_one: bind-only helpers; consumers: cnt_succ, the closed forms.
  cnt_succ: content; consumers: cnt_zero_closed, cnt_one_closed, cnt_two_closed, row_small.
  cnt_zero_closed, cnt_one_closed, cnt_two_closed: content (induction); consumer: row_closed,
    result.
  tail_empty, bond_row, defects_one, canonical_one: content; consumers: column_one, row_one.
  column_one, row_one, row_small, row_closed: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer
  (bondDefects, tailDefects, defects), module
  sha256:0eb5a3c567570fc8e1975bceae0142f2ec59262253a319e37032bf2cad35f6d1;
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical (Canonical), module
  sha256:6f1d1863bf0f2737c2399f9a57e75869de31f094599b6bab0cdc57fb33faaa4c.
Search: HardinA229634Strip counts the width-5 column with the same defects and Canonical
predicates; no frozen module defines the full table T(n,k) or its first row and column, and
no frozen lemma counts canonical words by monochromatic adjacencies.
-/

import Mathlib
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/-! # OEIS A229637: the first column and the first row

`T(n,k)` counts `n × k` arrays over `0..2` with exactly two mistakes, a mistake being a
monochromatic horizontal, diagonal or antidiagonal neighbour pair, with colours introduced in
row-major order. A single column has no such neighbours, so `T(n,1) = 0`. A single row is a
canonical word with exactly two equal adjacent letters; appending a letter gives one way to
repeat and two admissible new colours (one if the word is constant), whence
`T(1,k) = C(k-1,2) 2^(k-4)` for `k ≥ 4`. This row satisfies the recurrence with coefficients
`(6,-12,8)` from `k = 7`, has residual `-4` at `k = 6`, and satisfies no recurrence of order
at most two eventually.
-/

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn

open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects tailDefects defects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

instance canonicalDecidable {k : ℕ} : DecidablePred fun w : Fin k → Fin 3 => Canonical w :=
  fun _ => by unfold Canonical; infer_instance

/-- Positions whose right neighbour carries the same colour. -/
private def monoSet {k : ℕ} (w : Fin k → Fin 3) : Finset (Fin k) :=
  Finset.univ.filter fun i => ∃ j : Fin k, j.val = i.val + 1 ∧ w i = w j

private noncomputable def cnt (k m : ℕ) : ℕ :=
  Fintype.card {w : Fin k → Fin 3 // Canonical w ∧ (monoSet w).card = m}

variable {L : ℕ}

private theorem mono_snoc_iff (w : Fin (L + 1) → Fin 3) (c : Fin 3) (i0 : Fin (L + 1)) :
    (∃ j : Fin (L + 2), j.val = (Fin.castSucc i0).val + 1 ∧
        (Fin.snoc w c : Fin (L + 2) → Fin 3) (Fin.castSucc i0) =
          (Fin.snoc w c : Fin (L + 2) → Fin 3) j) ↔
      (∃ j0 : Fin (L + 1), j0.val = i0.val + 1 ∧ w i0 = w j0) ∨
        (i0 = Fin.last L ∧ w i0 = c) := by
  simp only [Fin.snoc_castSucc, Fin.val_castSucc]
  constructor
  · rintro ⟨j, hj, he⟩
    induction j using Fin.lastCases with
    | last =>
      right
      simp only [Fin.snoc_last] at he
      refine ⟨Fin.ext ?_, he⟩
      simp only [Fin.val_last] at hj ⊢
      omega
    | cast j0 =>
      left
      simp only [Fin.snoc_castSucc, Fin.val_castSucc] at he hj
      exact ⟨j0, hj, he⟩
  · rintro (⟨j0, hj, he⟩ | ⟨rfl, he⟩)
    · exact ⟨Fin.castSucc j0, by simpa using hj, by simpa using he⟩
    · exact ⟨Fin.last (L + 1), by simp, by simpa using he⟩

private theorem mono_snoc (w : Fin (L + 1) → Fin 3) (c : Fin 3) :
    (monoSet (Fin.snoc w c : Fin (L + 2) → Fin 3)).card =
      (monoSet w).card + if w (Fin.last L) = c then 1 else 0 := by
  simp only [monoSet, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  have hlast : ¬ ∃ j : Fin (L + 2), j.val = (Fin.last (L + 1)).val + 1 ∧
      (Fin.snoc w c : Fin (L + 2) → Fin 3) (Fin.last (L + 1)) =
        (Fin.snoc w c : Fin (L + 2) → Fin 3) j := by
    rintro ⟨j, hj, -⟩
    have := j.isLt
    simp only [Fin.val_last] at hj
    omega
  simp only [hlast, ↓reduceIte, add_zero]
  simp_rw [mono_snoc_iff]
  have hsplit : ∀ i0 : Fin (L + 1),
      (if (∃ j0 : Fin (L + 1), j0.val = i0.val + 1 ∧ w i0 = w j0) ∨
          (i0 = Fin.last L ∧ w i0 = c) then 1 else 0) =
        (if ∃ j0 : Fin (L + 1), j0.val = i0.val + 1 ∧ w i0 = w j0 then 1 else 0) +
          (if i0 = Fin.last L ∧ w i0 = c then 1 else 0) := by
    intro i0
    by_cases h1 : ∃ j0 : Fin (L + 1), j0.val = i0.val + 1 ∧ w i0 = w j0
    · have h2 : ¬ (i0 = Fin.last L ∧ w i0 = c) := by
        rintro ⟨rfl, -⟩
        obtain ⟨j0, hj, -⟩ := h1
        have := j0.isLt
        simp only [Fin.val_last] at hj
        omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl h1)), ite_eq_left_of_eq_true _ _ (eq_true h1),
        ite_eq_right_of_eq_false _ _ (eq_false h2)]
    · by_cases h2 : i0 = Fin.last L ∧ w i0 = c
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr h2)),
          ite_eq_right_of_eq_false _ _ (eq_false h1),
          ite_eq_left_of_eq_true _ _ (eq_true h2)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_or.2 ⟨h1, h2⟩)),
          ite_eq_right_of_eq_false _ _ (eq_false h1),
          ite_eq_right_of_eq_false _ _ (eq_false h2)]
  rw [Finset.sum_congr rfl (fun i0 _ => hsplit i0), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (Fin.last L)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private theorem canon_snoc (w : Fin (L + 1) → Fin 3) (c : Fin 3) :
    Canonical (Fin.snoc w c : Fin (L + 2) → Fin 3) ↔
      Canonical w ∧ ∀ b : Fin 3, b.val < c.val → ∃ j, w j = b := by
  simp only [← Fin.lt_def]
  unfold Canonical
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.exists_fin_succ',
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, true_and]
  have h1 : ∀ i0 : Fin (L + 1), ¬ Fin.last (L + 1) < Fin.castSucc i0 :=
    fun i0 => (Fin.castSucc_lt_last i0).asymm
  simp only [h1, false_and, or_false, lt_irrefl]

private theorem zero_of_canon {w : Fin (L + 1) → Fin 3} (hw : Canonical w) : w 0 = 0 := by
  by_contra h
  obtain ⟨j, hj, -⟩ := hw 0 0 (Fin.pos_iff_ne_zero.2 h)
  exact (Fin.not_lt_zero j) hj

private theorem one_of_canon {w : Fin (L + 1) → Fin 3} (hw : Canonical w) (hz : ¬ ∀ i, w i = 0) :
    ∃ j, w j = 1 := by
  push Not at hz
  obtain ⟨i, hi⟩ := hz
  by_cases h1 : w i = 1
  · exact ⟨i, h1⟩
  · have : (1 : Fin 3) < w i := by
      have := (w i).isLt
      have h0 : (w i).val ≠ 0 := fun h => hi (Fin.ext h)
      have h1' : (w i).val ≠ 1 := fun h => h1 (Fin.ext h)
      rw [Fin.lt_def]
      simp
      omega
    obtain ⟨j, -, hj⟩ := hw i 1 this
    exact ⟨j, hj⟩

private theorem valid_iff {w : Fin (L + 1) → Fin 3} (hw : Canonical w) (c : Fin 3) :
    (∀ b : Fin 3, b.val < c.val → ∃ j, w j = b) ↔ (c = 2 → ¬ ∀ i, w i = 0) := by
  have h0 : ∃ j, w j = 0 := ⟨0, zero_of_canon hw⟩
  fin_cases c
  · simp
  · simp only [Fin.mk_one, Fin.isValue]
    constructor
    · intro _ h
      exact absurd h (by decide)
    · intro _ b hb
      have : b = 0 := Fin.ext (by omega)
      rw [this]
      exact h0
  · simp only [Fin.reduceFinMk, Fin.isValue, forall_const]
    constructor
    · intro h hz
      obtain ⟨j, hj⟩ := h 1 (by decide)
      rw [hz j] at hj
      exact absurd hj (by decide)
    · intro hz b hb
      obtain ⟨j1, hj1⟩ := one_of_canon hw hz
      have hb' : b = 0 ∨ b = 1 := by
        rcases Fin.exists_fin_succ.mp ⟨b, rfl⟩ with h | h <;> omega
      rcases hb' with rfl | rfl
      · exact h0
      · exact ⟨j1, hj1⟩

private theorem ext_count (w : Fin (L + 1) → Fin 3) (hw : Canonical w) (m : ℕ) :
    (∑ c : Fin 3, if Canonical (Fin.snoc w c : Fin (L + 2) → Fin 3) ∧
        (monoSet (Fin.snoc w c : Fin (L + 2) → Fin 3)).card = m then 1 else 0) +
      (if (monoSet w).card = m ∧ ∀ i, w i = 0 then 1 else 0) =
    (if (monoSet w).card + 1 = m then 1 else 0) + 2 * (if (monoSet w).card = m then 1 else 0) := by
  simp only [canon_snoc, hw, mono_snoc, true_and, valid_iff hw, Fin.sum_univ_three]
  generalize hM : (monoSet w).card = M
  by_cases hz : ∀ i, w i = 0
  · have hl : w (Fin.last L) = 0 := hz _
    simp only [hl, hz]
    simp
    split_ifs <;> omega
  · simp only [hz, not_false_eq_true, implies_true, true_and, and_false]
    generalize w (Fin.last L) = v
    fin_cases v <;> simp <;> split_ifs <;> omega

private theorem cnt_eq_sum (k m : ℕ) :
    cnt k m = ∑ w : Fin k → Fin 3, if Canonical w ∧ (monoSet w).card = m then 1 else 0 := by
  rw [cnt, Fintype.card_subtype, Finset.card_filter]

private theorem zero_word_mono (L : ℕ) :
    (monoSet (fun _ : Fin (L + 1) => (0 : Fin 3))).card = L := by
  have : monoSet (fun _ : Fin (L + 1) => (0 : Fin 3)) =
      (Finset.univ.filter fun i : Fin (L + 1) => i.val < L) := by
    ext i
    simp only [monoSet, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨j, hj⟩
      have := j.isLt
      omega
    · intro hi
      exact ⟨⟨i.val + 1, by omega⟩, rfl⟩
  rw [this, Fin.card_filter_val_lt]
  omega

private theorem cnt_succ (L m : ℕ) :
    cnt (L + 2) m + (if L = m then 1 else 0) =
      (∑ w : Fin (L + 1) → Fin 3, if Canonical w ∧ (monoSet w).card + 1 = m then 1 else 0) +
        2 * cnt (L + 1) m := by
  rw [cnt_eq_sum, cnt_eq_sum, ← (Fin.snocEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  have hzero : (if L = m then 1 else 0) = ∑ w : Fin (L + 1) → Fin 3,
      (if Canonical w then (if (monoSet w).card = m ∧ ∀ i, w i = 0 then 1 else 0) else 0) := by
    rw [Finset.sum_eq_single (fun _ => (0 : Fin 3))]
    · have hc : Canonical (fun _ : Fin (L + 1) => (0 : Fin 3)) := by
        intro i b hb
        exact absurd hb (Fin.not_lt_zero b)
      simp only [hc, ↓reduceIte, zero_word_mono, implies_true, and_true]
    · intro w _ hw
      split_ifs with h1 h2
      · exact absurd (funext h2.2) hw
      · rfl
      · rfl
    · simp
  rw [hzero, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : Canonical w
  · simp only [hw, ↓reduceIte, true_and]
    exact ext_count w hw m
  · have : ∀ c : Fin 3, ¬ Canonical (Fin.snoc w c : Fin (L + 2) → Fin 3) :=
      fun c h => hw ((canon_snoc w c).1 h).1
    simp only [hw, ↓reduceIte, false_and, add_zero, mul_zero]
    exact Finset.sum_eq_zero
      (fun c _ => ite_eq_right_of_eq_false _ _ (eq_false fun h => this c h.1))

private theorem shift_sum (L m : ℕ) :
    (∑ w : Fin (L + 1) → Fin 3, if Canonical w ∧ (monoSet w).card + 1 = m then 1 else 0) =
      if m = 0 then 0 else cnt (L + 1) (m - 1) := by
  split_ifs with hm
  · exact Finset.sum_eq_zero (fun w _ => by simp [hm])
  · rw [cnt_eq_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have : ((monoSet w).card + 1 = m) ↔ ((monoSet w).card = m - 1) := by omega
    simp only [this]

private theorem cnt_one (m : ℕ) : cnt 1 m = if m = 0 then 1 else 0 := by
  rw [cnt_eq_sum]
  have hmono : ∀ w : Fin 1 → Fin 3, (monoSet w).card = 0 := by
    intro w
    rw [Finset.card_eq_zero]
    unfold monoSet
    rw [Finset.filter_eq_empty_iff]
    rintro i - ⟨j, hj, -⟩
    have := j.isLt
    have := i.isLt
    omega
  have hcanon : ∀ w : Fin 1 → Fin 3, Canonical w ↔ w 0 = 0 := by
    intro w
    constructor
    · exact zero_of_canon
    · intro h i b hb
      rw [Fin.fin_one_eq_zero i, h] at hb
      exact absurd hb (Fin.not_lt_zero b)
  simp only [hmono, hcanon]
  rw [Finset.sum_eq_single (fun _ => (0 : Fin 3))]
  · simp [eq_comm]
  · intro w _ hw
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hw (funext fun i => by
      rw [Fin.fin_one_eq_zero i]; exact h.1))]
  · simp

private theorem cnt_zero_closed (j : ℕ) : cnt (j + 2) 0 = 2 ^ j := by
  induction j with
  | zero =>
    have h := cnt_succ 0 0
    rw [shift_sum, cnt_one] at h
    simp at h
    omega
  | succ j ih =>
    have h := cnt_succ (j + 1) 0
    rw [shift_sum] at h
    simp only [show j + 1 + 1 = j + 2 from rfl, ih] at h
    rw [show j + 1 + 2 = j + 1 + 2 from rfl, pow_succ]
    simp at h
    omega

private theorem cnt_one_closed (j : ℕ) : cnt (j + 3) 1 = (j + 2) * 2 ^ j := by
  induction j with
  | zero =>
    have h := cnt_succ 1 1
    rw [shift_sum] at h
    have h1 := cnt_succ 0 1
    rw [shift_sum, cnt_one, cnt_one] at h1
    have h0 := cnt_zero_closed 0
    simp at h h1 h0
    show cnt 3 1 = 2
    omega
  | succ j ih =>
    have h := cnt_succ (j + 2) 1
    rw [shift_sum] at h
    have h0 := cnt_zero_closed (j + 1)
    simp only [show j + 2 + 1 = j + 3 from rfl, ih] at h
    simp at h
    rw [show j + 1 + 3 = j + 2 + 2 from rfl, pow_succ]
    rw [show j + 2 + 1 = j + 1 + 2 from rfl, h0] at h
    rw [show j + 2 + 2 = j + 4 from rfl] at h ⊢
    rw [pow_succ] at h
    nlinarith

private theorem cnt_two_closed (j : ℕ) : cnt (j + 4) 2 = (j + 3).choose 2 * 2 ^ j := by
  induction j with
  | zero =>
    have h := cnt_succ 2 2
    rw [shift_sum] at h
    have h3 := cnt_succ 1 2
    rw [shift_sum] at h3
    have h2 := cnt_succ 0 2
    rw [shift_sum, cnt_one, cnt_one] at h2
    have h31 := cnt_one_closed 0
    have h21 := cnt_succ 0 1
    rw [shift_sum, cnt_one, cnt_one] at h21
    simp at h h3 h2 h31 h21
    show cnt 4 2 = (3 : ℕ).choose 2 * 1
    rw [show (3 : ℕ).choose 2 = 3 by decide]
    omega
  | succ j ih =>
    have h := cnt_succ (j + 3) 2
    rw [shift_sum] at h
    have h1 := cnt_one_closed (j + 1)
    simp only [show j + 3 + 1 = j + 4 from rfl, ih] at h
    simp at h
    rw [show j + 3 + 2 = j + 1 + 4 from rfl] at h
    rw [show j + 1 + 3 = j + 3 + 1 from rfl] at h1
    rw [h1] at h
    rw [show j + 1 + 3 = j + 3 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
    rw [h, pow_succ]
    ring

/-- The bonds `(j, j + 1)` inside a row of width `k`. -/
def horiz (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun e => e.2.val = e.1.val + 1

/-- The diagonal and antidiagonal bonds between consecutive rows of width `k`, as pairs
(upper column, lower column). -/
def betw (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun e => e.2.val = e.1.val + 1 ∨ e.1.val = e.2.val + 1

instance arrayCanonicalDecidable {n k : ℕ} : DecidablePred fun A : Fin n × Fin k → Fin 3 =>
    @Canonical (Fin n × Fin k)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A :=
  fun _ => by unfold Canonical; infer_instance

/-- OEIS A229637: `n × k` arrays over `0..2` with exactly two monochromatic horizontal,
diagonal or antidiagonal neighbour pairs, colours introduced in row-major order. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin k → Fin 3 =>
    defects (horiz k) (betw k) (List.ofFn fun i j => A (i, j)) = 2 ∧
    (@Canonical (Fin n × Fin k)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

private theorem tail_empty {k : ℕ} (r : Fin k → Fin 3) (rs : List (Fin k → Fin 3)) :
    tailDefects (∅ : Finset (Fin k × Fin k)) ∅ r rs = 0 := by
  induction rs generalizing r with
  | nil => rfl
  | cons t ts ih => simp [tailDefects, bondDefects, ih]

private theorem column_one (n : ℕ) : T n 1 = 0 := by
  have hh : horiz 1 = ∅ := by
    unfold horiz
    rw [Finset.filter_eq_empty_iff]
    intro e _ he
    have := e.2.isLt
    omega
  have hb : betw 1 = ∅ := by
    unfold betw
    rw [Finset.filter_eq_empty_iff]
    intro e _ he
    have := e.2.isLt
    have := e.1.isLt
    omega
  have hd : ∀ rs : List (Fin 1 → Fin 3), defects (horiz 1) (betw 1) rs = 0 := by
    intro rs
    rw [hh, hb]
    cases rs with
    | nil => rfl
    | cons r rs => simp [defects, bondDefects, tail_empty]
  unfold T
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro A _ hA
  rw [hd] at hA
  exact absurd hA.1 (by decide)

private theorem bond_row {k : ℕ} (r : Fin k → Fin 3) :
    bondDefects (horiz k) r r = (monoSet r).card := by
  unfold bondDefects
  rw [← Finset.card_image_of_injOn (f := Prod.fst)]
  · congr 1
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, horiz, Finset.mem_univ, true_and, monoSet]
    constructor
    · rintro ⟨e, ⟨he, hr⟩, rfl⟩
      exact ⟨e.2, he, hr⟩
    · rintro ⟨j, hj, hr⟩
      exact ⟨(i, j), ⟨hj, hr⟩, rfl⟩
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    simp only [horiz, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact Prod.ext hxy (Fin.ext (by rw [hx.1, hy.1, hxy]))

private theorem defects_one {k : ℕ} (A : Fin 1 × Fin k → Fin 3) :
    defects (horiz k) (betw k) (List.ofFn fun i j => A (i, j)) =
      (monoSet fun j => A (0, j)).card := by
  rw [List.ofFn_succ, List.ofFn_zero]
  simp only [defects, tailDefects, add_zero]
  exact bond_row _

private theorem canonical_one {k : ℕ} (A : Fin 1 × Fin k → Fin 3) :
    @Canonical (Fin 1 × Fin k)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A ↔
      Canonical fun j => A (0, j) := by
  have hp : ∀ p : Fin 1 × Fin k, p = (0, p.2) := fun p => Prod.ext (Fin.fin_one_eq_zero _) rfl
  have hlt : ∀ i j : Fin k, (@LT.lt (Fin 1 × Fin k)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT (0, i) (0, j)) ↔
        i < j := by
    intro i j
    change finProdFinEquiv (0, i) < finProdFinEquiv (0, j) ↔ i < j
    rw [Fin.lt_def, Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
    simp
  unfold Canonical
  constructor
  · intro h i b hb
    obtain ⟨q, hq, hqb⟩ := h (0, i) b hb
    rw [hp q, hlt] at hq
    rw [hp q] at hqb
    exact ⟨q.2, hq, hqb⟩
  · intro h p b hb
    rw [hp p] at hb ⊢
    obtain ⟨j, hj, hjb⟩ := h p.2 b hb
    exact ⟨(0, j), (hlt j p.2).2 hj, hjb⟩

private theorem row_one (k : ℕ) : T 1 k = cnt k 2 := by
  let e : (Fin 1 × Fin k → Fin 3) ≃ (Fin k → Fin 3) :=
    { toFun := fun A j => A (0, j)
      invFun := fun w p => w p.2
      left_inv := fun A => by
        funext p
        rw [show p = (0, p.2) from Prod.ext (Fin.fin_one_eq_zero _) rfl]
      right_inv := fun w => rfl }
  rw [cnt, Fintype.card_subtype, T]
  refine Finset.card_bij (fun A _ => e A) ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    obtain ⟨hdef, hcan⟩ := hA
    change Canonical (fun j => A (0, j)) ∧ (monoSet fun j => A (0, j)).card = 2
    exact ⟨(canonical_one A).1 hcan, by rw [← defects_one]; exact hdef⟩
  · intro A _ B _ h
    exact e.injective h
  · intro w hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨by rw [defects_one]; exact hw.2, (canonical_one _).2 hw.1⟩

private theorem row_small : T 1 1 = 0 ∧ T 1 2 = 0 ∧ T 1 3 = 1 := by
  have h2 := cnt_succ 0 2
  rw [shift_sum, cnt_one, cnt_one] at h2
  have h3 := cnt_succ 1 2
  rw [shift_sum] at h3
  have h21 := cnt_succ 0 1
  rw [shift_sum, cnt_one, cnt_one] at h21
  simp at h2 h3 h21
  refine ⟨?_, ?_, ?_⟩
  · rw [row_one, cnt_one]; rfl
  · rw [row_one]; omega
  · rw [row_one]; omega

private theorem row_closed (j : ℕ) : (T 1 (j + 4) : ℚ) = (j + 3) * (j + 2) / 2 * 2 ^ j := by
  rw [row_one, cnt_two_closed, Nat.cast_mul, Nat.cast_choose_two]
  push_cast
  ring

/-- OEIS A229637, column 1 and row 1: `T(n,1) = 0`, `T(1,1) = T(1,2) = 0`, `T(1,3) = 1`,
`T(1,k) = C(k-1,2) 2^(k-4)` for `k ≥ 4`; the recurrence with coefficients `(6,-12,8)` holds
for `k ≥ 7`, its residual at `k = 6` is `-4`, and no recurrence of order at most two holds
eventually. -/
def claim : Prop :=
  (∀ n, T n 1 = 0) ∧ T 1 1 = 0 ∧ T 1 2 = 0 ∧ T 1 3 = 1 ∧
    (∀ k, 4 ≤ k → T 1 k = (k - 1).choose 2 * 2 ^ (k - 4)) ∧
    (∀ k, 7 ≤ k → (T 1 k : ℤ) = 6 * T 1 (k - 1) - 12 * T 1 (k - 2) + 8 * T 1 (k - 3)) ∧
    (T 1 6 : ℤ) - (6 * T 1 5 - 12 * T 1 4 + 8 * T 1 3) = -4 ∧
    ¬ ∃ (N : ℕ) (c₁ c₂ : ℚ), ∀ k, N ≤ k → (T 1 k : ℚ) = c₁ * T 1 (k - 1) + c₂ * T 1 (k - 2)

theorem result : claim := by
  obtain ⟨h1, h2, h3⟩ := row_small
  have hform : ∀ k, 4 ≤ k → T 1 k = (k - 1).choose 2 * 2 ^ (k - 4) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    rw [row_one, cnt_two_closed, show j + 4 - 1 = j + 3 by omega, show j + 4 - 4 = j by omega]
  have hq : ∀ j : ℕ, (T 1 (j + 4) : ℚ) = (j + 3) * (j + 2) / 2 * 2 ^ j := row_closed
  refine ⟨column_one, h1, h2, h3, hform, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    have e : ((T 1 (j + 7) : ℤ) : ℚ) = 6 * T 1 (j + 6) - 12 * T 1 (j + 5) + 8 * T 1 (j + 4) := by
      push_cast
      rw [show j + 7 = (j + 3) + 4 by omega, show j + 6 = (j + 2) + 4 by omega,
        show j + 5 = (j + 1) + 4 by omega, hq, hq, hq, hq]
      push_cast
      ring
    rw [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega]
    exact_mod_cast e
  · have e6 : (T 1 6 : ℚ) = 40 := by
      have := hq 2
      rw [this]
      norm_num
    have e5 : (T 1 5 : ℚ) = 12 := by
      have := hq 1
      rw [this]
      norm_num
    have e4 : (T 1 4 : ℚ) = 3 := by
      have := hq 0
      rw [this]
      norm_num
    have : (T 1 6 : ℚ) - (6 * T 1 5 - 12 * T 1 4 + 8 * T 1 3) = -4 := by
      rw [e6, e5, e4, h3]
      norm_num
    exact_mod_cast this
  · rintro ⟨N, c₁, c₂, h⟩
    have eq : ∀ t : ℕ, (4 * ((N : ℚ) + t + 5) * ((N : ℚ) + t + 4) -
        2 * c₁ * ((N : ℚ) + t + 4) * ((N : ℚ) + t + 3) -
          c₂ * ((N : ℚ) + t + 3) * ((N : ℚ) + t + 2)) = 0 := by
      intro t
      have ht := h (N + t + 6) (by omega)
      rw [show N + t + 6 - 1 = (N + t + 1) + 4 by omega,
        show N + t + 6 - 2 = (N + t) + 4 by omega,
        show N + t + 6 = (N + t + 2) + 4 by omega, hq, hq, hq] at ht
      have hp : (2 : ℚ) ^ (N + t) ≠ 0 := pow_ne_zero _ two_ne_zero
      have : (2 : ℚ) ^ (N + t) * (4 * ((N : ℚ) + t + 5) * ((N : ℚ) + t + 4) -
          2 * c₁ * ((N : ℚ) + t + 4) * ((N : ℚ) + t + 3) -
            c₂ * ((N : ℚ) + t + 3) * ((N : ℚ) + t + 2)) = 0 := by
        push_cast at ht
        rw [pow_add] at ht ⊢
        linear_combination 2 * ht
      exact (mul_eq_zero.1 this).resolve_left hp
    have e0 := eq 0
    have e1 := eq 1
    have e2 := eq 2
    push_cast at e0 e1 e2
    have : (8 : ℚ) = 0 := by
      linear_combination (1 + ((N : ℚ) + 3) + ((N : ℚ) + 4) * ((N : ℚ) + 3) / 2) * e0 +
        (-((N : ℚ) + 3) - ((N : ℚ) + 4) * ((N : ℚ) + 3)) * e1 +
        (((N : ℚ) + 4) * ((N : ℚ) + 3) / 2) * e2
    norm_num at this

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
