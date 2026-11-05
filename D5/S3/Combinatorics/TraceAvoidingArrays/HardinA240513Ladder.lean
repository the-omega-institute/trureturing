/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Literal binary ladder counts, their signed recurrence and generating series. -/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
R. H. Hardin's OEIS A240513 counts binary arrays on an open two-column board,
with the first entry zero and no cell having exactly two equal neighbours.
The recurrence and generating function are the empirical formulas attributed
to Colin Barker. All arithmetic in those formulas is over the integers.
-/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder

private def equalBit (x y : Bool) : ℕ := if x = y then 1 else 0

private def Legal {n : ℕ} (A : Fin n × Fin 2 → Bool) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = false) ∧
  ∀ (i : Fin n) (j : Fin 2),
    equalBit (A (i, j.rev)) (A (i, j)) +
      (if h : 0 < i.val then
        equalBit (A (⟨i.val - 1, by omega⟩, j)) (A (i, j)) else 0) +
      (if h : i.val + 1 < n then
        equalBit (A (⟨i.val + 1, h⟩, j)) (A (i, j)) else 0) ≠ 2

private instance {n : ℕ} (A : Fin n × Fin 2 → Bool) : Decidable (Legal A) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ ∀ i j, (_ : ℕ) ≠ 2))

/-- The filtered finite set of literal boards; the empty board has count zero. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 2 → Bool => Legal A)).card

private abbrev Row := Fin 2 → Bool

private def Boundary (r s : Row) : Prop :=
  ∀ j : Fin 2, equalBit (r j.rev) (r j) + equalBit (s j) (r j) ≠ 2

private def Interior (r s t : Row) : Prop :=
  ∀ j : Fin 2,
    equalBit (s j.rev) (s j) + equalBit (r j) (s j) + equalBit (t j) (s j) ≠ 2

private instance (r s : Row) : Decidable (Boundary r s) :=
  inferInstanceAs (Decidable (∀ j : Fin 2, (_ : ℕ) ≠ 2))

private instance (r s t : Row) : Decidable (Interior r s t) :=
  inferInstanceAs (Decidable (∀ j : Fin 2, (_ : ℕ) ≠ 2))

/-- All rows except the first satisfy their local condition. -/
private def TailGood (k : ℕ) (f : Fin (k + 2) → Row) : Prop :=
  Boundary (f (Fin.last (k + 1))) (f (Fin.last k).castSucc) ∧
  ∀ i : Fin k, Interior (f i.castSucc.castSucc) (f i.castSucc.succ) (f i.succ.succ)

private instance (k : ℕ) (f : Fin (k + 2) → Row) : Decidable (TailGood k f) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ ∀ i : Fin k, (_ : Prop)))

private theorem tailGood_cons (k : ℕ) (r : Row) (f : Fin (k + 2) → Row) :
    TailGood (k + 1) (Fin.cons r f) ↔
      Interior r (f 0) (f 1) ∧ TailGood k f := by
  simp only [TailGood, Fin.forall_fin_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.succ_zero_eq_one, Fin.cons_succ, Fin.castSucc_succ, Fin.cons_last,
    Fin.last_succ]
  tauto

private theorem legal_iff (k : ℕ) (A : Fin (k + 2) × Fin 2 → Bool) :
    Legal A ↔
      A (0, 0) = false ∧ Boundary (fun j => A (0, j)) (fun j => A (1, j)) ∧
        TailGood k (fun i j => A (i, j)) := by
  constructor
  · rintro ⟨⟨i, hi, ha⟩, h⟩
    have hi0 : i = 0 := Fin.ext hi
    refine ⟨by simpa only [hi0] using ha, ?_, ?_, ?_⟩
    · intro j
      simpa [Boundary, Fin.val_zero] using h 0 j
    · intro j
      have hh := h (Fin.last (k + 1)) j
      simpa [Boundary, Fin.val_last] using hh
    · intro i j
      have hh := h i.castSucc.succ j
      have hp : 0 < (i.castSucc.succ).val := by simp
      have hn : (i.castSucc.succ).val + 1 < k + 2 := by omega
      simpa [Interior, hp, hn] using hh
  · rintro ⟨ha, ht, hb, hm⟩
    refine ⟨⟨0, rfl, ha⟩, ?_⟩
    intro i j
    by_cases hz : i.val = 0
    · have hi : i = 0 := Fin.ext hz
      subst i
      simpa [Boundary] using ht j
    · by_cases hl : i.val = k + 1
      · have hi : i = Fin.last (k + 1) := Fin.ext hl
        subst i
        simpa [Boundary, Fin.val_last] using hb j
      · let p : Fin k := ⟨i.val - 1, by omega⟩
        have hprev : p.castSucc.castSucc = ⟨i.val - 1, by omega⟩ := Fin.ext rfl
        have hcur : p.castSucc.succ = i := Fin.ext (by dsimp [p]; omega)
        have hnext : p.succ.succ = ⟨i.val + 1, by omega⟩ :=
          Fin.ext (by dsimp [p]; omega)
        have hh := hm p j
        simpa only [Interior, hprev, hcur, hnext,
          dif_pos (show 0 < i.val by omega),
          dif_pos (show i.val + 1 < k + 2 by omega)] using hh

private def step (v : Row → Row → ℤ) (r s : Row) : ℤ :=
  ∑ t : Row, if Interior r s t then v s t else 0

private def v : ℕ → Row → Row → ℤ
  | 0, r, s => if Boundary s r then 1 else 0
  | k + 1, r, s => step (v k) r s

private def count (k : ℕ) (r s : Row) : ℤ :=
  ∑ f : Fin k → Row, if TailGood k (Fin.cons r (Fin.cons s f)) then 1 else 0

private theorem count_zero (r s : Row) : count 0 r s = v 0 r s := by
  simp [count, v, TailGood, Fin.forall_fin_one]

private theorem count_succ (k : ℕ) (r s : Row) :
    count (k + 1) r s = step (count k) r s := by
  unfold count
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Row)).sum_comp
    (fun f => if TailGood (k + 1) (Fin.cons r (Fin.cons s f)) then (1 : ℤ) else 0),
    Fintype.sum_prod_type]
  change (∑ t : Row, ∑ f : Fin k → Row,
    if TailGood (k + 1) (Fin.cons r (Fin.cons s (Fin.cons t f)))
      then (1 : ℤ) else 0) = _
  unfold step
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : Interior r s t <;> simp [tailGood_cons, h]

private theorem count_eq_v (k : ℕ) : count k = v k := by
  induction k with
  | zero => funext r s; exact count_zero r s
  | succ k ih => funext r s; rw [count_succ, ih]; rfl

private def total (w : Row → Row → ℤ) : ℤ :=
  ∑ r : Row, ∑ s : Row, if r 0 = false ∧ Boundary r s then w r s else 0

private theorem counting_bridge (k : ℕ) : (a (k + 2) : ℤ) = total (v k) := by
  let e : (Fin (k + 2) × Fin 2 → Bool) ≃ (Fin (k + 2) → Row) := Equiv.curry _ _ _
  have hc : (a (k + 2) : ℤ) =
      ∑ f : Fin (k + 2) → Row,
        if f 0 0 = false ∧ Boundary (f 0) (f 1) ∧ TailGood k f then 1 else 0 := by
    rw [a, Finset.natCast_card_filter]
    exact e.sum_comp _ |>.symm.trans (Finset.sum_congr rfl (by
      intro A _
      simp only [e, Equiv.curry_apply, legal_iff]))
  rw [hc]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Row)).sum_comp
    (fun f => if f 0 0 = false ∧ Boundary (f 0) (f 1) ∧ TailGood k f
      then (1 : ℤ) else 0), Fintype.sum_prod_type]
  change (∑ r : Row, ∑ f : Fin (k + 1) → Row,
    if r 0 = false ∧ Boundary r (f 0) ∧ TailGood k (Fin.cons r f)
      then (1 : ℤ) else 0) = _
  unfold total
  apply Finset.sum_congr rfl
  intro r _
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Row)).sum_comp
    (fun f => if r 0 = false ∧ Boundary r (f 0) ∧ TailGood k (Fin.cons r f)
      then (1 : ℤ) else 0), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ f : Fin k → Row,
    if r 0 = false ∧ Boundary r s ∧ TailGood k (Fin.cons r (Fin.cons s f))
      then (1 : ℤ) else 0) = _
  by_cases h : r 0 = false ∧ Boundary r s
  · simp only [h.1, h.2, true_and, if_pos h]
    exact congrFun (congrFun (count_eq_v k) r) s
  · have hh : ∀ p : Prop, ¬ (r 0 = false ∧ Boundary r s ∧ p) := by tauto
    simp [h, hh]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
