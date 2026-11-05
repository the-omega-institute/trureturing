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
  inferInstanceAs (Decidable ((_ : Prop) ∧ ∀ _ _, (_ : ℕ) ≠ 2))

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
  inferInstanceAs (Decidable (∀ _ : Fin 2, (_ : ℕ) ≠ 2))

private instance (r s t : Row) : Decidable (Interior r s t) :=
  inferInstanceAs (Decidable (∀ _ : Fin 2, (_ : ℕ) ≠ 2))

/-- All rows except the first satisfy their local condition. -/
private def TailGood (k : ℕ) (f : Fin (k + 2) → Row) : Prop :=
  Boundary (f (Fin.last (k + 1))) (f (Fin.last k).castSucc) ∧
  ∀ i : Fin k, Interior (f i.castSucc.castSucc) (f i.castSucc.succ) (f i.succ.succ)

private instance (k : ℕ) (f : Fin (k + 2) → Row) : Decidable (TailGood k f) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ ∀ _ : Fin k, (_ : Prop)))

private theorem tailGood_cons (k : ℕ) (r : Row) (f : Fin (k + 2) → Row) :
    TailGood (k + 1) (Fin.cons r f) ↔
      Interior r (f 0) (f 1) ∧ TailGood k f := by
  simp only [TailGood, Fin.forall_fin_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.succ_zero_eq_one, Fin.cons_succ, Fin.castSucc_succ, Fin.cons_last]
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
      have he : (⟨k, by omega⟩ : Fin (k + 2)) = (Fin.last k).castSucc := Fin.ext rfl
      simpa [Boundary, Fin.val_last, he] using hh
    · intro i j
      have hh := h i.castSucc.succ j
      have hp : 0 < (i.castSucc.succ).val := by simp
      have hn : (i.castSucc.succ).val + 1 < k + 2 := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have he : (⟨i.val, by omega⟩ : Fin (k + 2)) = i.castSucc.castSucc := Fin.ext rfl
      have hf : (⟨i.val + 1 + 1, by omega⟩ : Fin (k + 2)) = i.succ.succ := Fin.ext rfl
      simpa [Interior, hp, hn, he, hf] using hh
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
        have he : (⟨k, by omega⟩ : Fin (k + 2)) = (Fin.last k).castSucc := Fin.ext rfl
        simpa [Boundary, Fin.val_last, he] using hb j
      · let p : Fin k := ⟨i.val - 1, by omega⟩
        have hprev : p.castSucc.castSucc = ⟨i.val - 1, by omega⟩ := Fin.ext rfl
        have hcur : p.castSucc.succ = i := Fin.ext (by dsimp [p]; omega)
        have hnext : p.succ.succ = ⟨i.val + 1, by omega⟩ :=
          Fin.ext (by dsimp [p]; omega)
        have hh := hm p j
        simpa only [Interior, hprev, hcur, hnext,
          dite_eq_left (show 0 < i.val by omega),
          dite_eq_left (show i.val + 1 < k + 2 by omega)] using hh

private def step (v : Row → Row → ℤ) (r s : Row) : ℤ :=
  ∑ t : Row, if Interior r s t then v s t else 0

private def v : ℕ → Row → Row → ℤ
  | 0, r, s => if Boundary s r then 1 else 0
  | k + 1, r, s => step (v k) r s

private def count (k : ℕ) (r s : Row) : ℤ :=
  ∑ f : Fin k → Row, if TailGood k (Fin.cons r (Fin.cons s f)) then 1 else 0

private theorem count_zero (r s : Row) : count 0 r s = v 0 r s := by
  simp [count, v, TailGood]

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
    rw [← e.sum_comp (fun f =>
      if f 0 0 = false ∧ Boundary (f 0) (f 1) ∧ TailGood k f then (1 : ℤ) else 0)]
    apply Finset.sum_congr rfl
    intro A _
    simp only [e, Equiv.curry_apply, Function.curry, legal_iff]
    rfl
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
  · simp only [h.1, h.2, true_and]
    exact congrFun (congrFun (count_eq_v k) r) s
  · have hh : ∀ p : Prop, ¬ (r 0 = false ∧ Boundary r s ∧ p) := by tauto
    simp [h, hh]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Six continuation vectors on sixteen row-pair states are reduced in the kernel.
private theorem finite_certificate : ∀ r s : Row,
    v 5 r s = 2 * v 4 r s + v 3 r s - v 2 r s - 2 * v 1 r s + v 0 r s := by
  decide +kernel

private theorem vector_recurrence (k : ℕ) : ∀ r s : Row,
    v (k + 5) r s =
      2 * v (k + 4) r s + v (k + 3) r s - v (k + 2) r s -
        2 * v (k + 1) r s + v k r s := by
  induction k with
  | zero => exact finite_certificate
  | succ k ih =>
    intro r s
    change step (v (k + 5)) r s =
      2 * step (v (k + 4)) r s + step (v (k + 3)) r s -
        step (v (k + 2)) r s - 2 * step (v (k + 1)) r s + step (v k) r s
    unfold step
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : Interior r s t
    · simpa only [ite_eq_left h] using ih s t
    · simp only [ite_eq_right h, mul_zero, add_zero, sub_zero]

private theorem total_recurrence (k : ℕ) :
    total (v (k + 5)) = 2 * total (v (k + 4)) + total (v (k + 3)) -
      total (v (k + 2)) - 2 * total (v (k + 1)) + total (v k) := by
  unfold total
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : r 0 = false ∧ Boundary r s
  · simpa only [ite_eq_left h] using vector_recurrence k r s
  · simp only [ite_eq_right h, mul_zero, add_zero, sub_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The first six counts use the literal singleton board and bounded continuation sums.
private theorem initial :
    (a 0 : ℤ) = 0 ∧ (a 1 : ℤ) = 2 ∧ (a 2 : ℤ) = 3 ∧ (a 3 : ℤ) = 6 ∧
      (a 4 : ℤ) = 10 ∧ (a 5 : ℤ) = 21 ∧ (a 6 : ℤ) = 42 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_, ?_⟩
  · change (a (0 + 2) : ℤ) = 3
    rw [counting_bridge]
    decide +kernel
  · change (a (1 + 2) : ℤ) = 6
    rw [counting_bridge]
    decide +kernel
  · change (a (2 + 2) : ℤ) = 10
    rw [counting_bridge]
    decide +kernel
  · change (a (3 + 2) : ℤ) = 21
    rw [counting_bridge]
    decide +kernel
  · change (a (4 + 2) : ℤ) = 42
    rw [counting_bridge]
    decide +kernel

set_option maxRecDepth 4096 in
private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - (a (n - 3) : ℤ) -
      2 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  rcases initial with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  by_cases he : n = 6
  · subst n
    norm_num [h1, h2, h3, h4, h5, h6]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    simpa only [show k + 7 - 1 = k + 6 by omega,
      show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega,
      show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega,
      ← counting_bridge, Nat.add_assoc, Nat.reduceAdd] using total_recurrence k

open PowerSeries

set_option maxRecDepth 4096 in
private theorem generating_function :
    (1 - X) * (1 - X - 2 * X ^ 2 - X ^ 3 + X ^ 4) *
        (PowerSeries.mk fun n => (a n : ℤ)) =
      X * (2 - X) * (1 - X ^ 2 - 2 * X ^ 3) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  change (1 - X) * (1 - X - 2 * X ^ 2 - X ^ 3 + X ^ 4) * F = _
  have he : (1 - X) * (1 - X - 2 * X ^ 2 - X ^ 3 + X ^ 4) * F =
      F - 2 * (F * X ^ 1) - F * X ^ 2 + F * X ^ 3 +
        2 * (F * X ^ 4) - F * X ^ 5 := by ring
  have hr : (X * (2 - X) * (1 - X ^ 2 - 2 * X ^ 3) : PowerSeries ℤ) =
      2 * X - X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4 + 2 * X ^ 5 := by ring
  rw [he, hr]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X,
    PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk]
  by_cases hn : 6 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_left (show 4 ≤ n by omega),
      ite_eq_left (show 5 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega), ite_eq_right (show n ≠ 4 by omega),
      ite_eq_right (show n ≠ 5 by omega)]
    have hh := recurrence n hn
    linarith
  · rcases initial with ⟨h0, h1, h2, h3, h4, h5, h6⟩
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5]

/-- The two empirical formulas for the literal, first-entry-zero ladder count. -/
theorem result :
    (∀ n : ℕ, 6 ≤ n →
      (a n : ℤ) = 2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - (a (n - 3) : ℤ) -
        2 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
    (1 - X) * (1 - X - 2 * X ^ 2 - X ^ 3 + X ^ 4) *
        (PowerSeries.mk fun n => (a n : ℤ)) =
      X * (2 - X) * (1 - X ^ 2 - 2 * X ^ 3) :=
  ⟨recurrence, generating_function⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
