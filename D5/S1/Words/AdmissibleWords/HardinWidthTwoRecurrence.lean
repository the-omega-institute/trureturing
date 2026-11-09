/- GID: D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hardin's width-two array recurrence and offset-one generating function. -/

/-
result: proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#24139; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26280
Direct frozen dependencies: AdmissibleCount.Adm, AdmissibleCount.adm_iff_no_adjacent_true,
  AdmissibleCount.decAdm, AdmissibleCount.admissibleWord_card_eq_fib.
Private theorem proof_shape: bind-only, each with a consumer:
  straight_iff -> avoids_iff; avoids_iff -> arrayEquiv;
  forbidden_switch -> column_switch_iff; column_switch_iff -> switchEquiv;
  switches_reconstruct -> switchEquiv;
  column_card -> array_count; array_count -> recurrence, generating_function;
  recurrence -> generating_function, result; generating_function -> result.
The literal array definitions are those of OEIS A206981; the proofs use the
existing admissible-word count and Fin.partialSum's reconstruction laws.
All statements concern arbitrary heights; finite Boolean cases only simplify
local predicates, so computational_content.kind = none.
-/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Basic

/-!
Binding definitions for R. H. Hardin, OEIS A206981, NAME and first FORMULA,
revision 17. Arrays are ordinary rectangles; triples are contiguous, with no wraparound.
No recurrence or closed formula is used to define the array count.
-/

namespace D5.S1.Words.AdmissibleWords.HardinWidthTwoRecurrence

/-- The two forbidden binary triples, literally 010 and 101. -/
def Forbidden (x y z : Bool) : Prop :=
  (x = false ∧ y = true ∧ z = false) ∨
    (x = true ∧ y = false ∧ z = true)

/-- Three cells separated by a single step in one of the four source directions. -/
def StraightTriple {n : ℕ} (p q r : Fin n × Fin 2) : Prop :=
  ∃ dr dc : ℤ,
    ((dr = 0 ∧ dc = 1) ∨ (dr = 1 ∧ dc = 0) ∨
      (dr = 1 ∧ dc = 1) ∨ (dr = 1 ∧ dc = -1)) ∧
    (q.1.val : ℤ) = (p.1.val : ℤ) + dr ∧
    (r.1.val : ℤ) = (q.1.val : ℤ) + dr ∧
    (q.2.val : ℤ) = (p.2.val : ℤ) + dc ∧
    (r.2.val : ℤ) = (q.2.val : ℤ) + dc

/-- No forbidden triple in any row, column, diagonal or antidiagonal. -/
def Avoids {n : ℕ} (A : Fin n → Fin 2 → Bool) : Prop :=
  ∀ p q r : Fin n × Fin 2, StraightTriple p q r →
    ¬ Forbidden (A p.1 p.2) (A q.1 q.2) (A r.1 r.2)

/-- Cardinality of the actual finite set of source arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin n → Fin 2 → Bool // Avoids A}

/-- The ordinary generating series starts at the source's offset 1. -/
noncomputable def gf : PowerSeries ℤ :=
  PowerSeries.mk fun n : ℕ => if n = 0 then 0 else (a n : ℤ)

open PowerSeries

/-- The first FORMULA entry, with signed arithmetic and its OGF cleared by a unit denominator. -/
def claim : Prop :=
  (∀ n : ℕ, 4 ≤ n →
    (a n : ℤ) = 2 * (a (n - 1) : ℤ) + 2 * (a (n - 2) : ℤ) - (a (n - 3) : ℤ)) ∧
  gf * (1 - 2 * X - 2 * X ^ 2 + X ^ 3) = 4 * X + 8 * X ^ 2 - 4 * X ^ 3

end D5.S1.Words.AdmissibleWords.HardinWidthTwoRecurrence

namespace D5.S1.Words.AdmissibleWords.HardinWidthTwoRecurrence
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open PowerSeries

/-- Every in-bounds source triple in width two is vertical. -/
private theorem straight_iff {n : ℕ} (p q r : Fin n × Fin 2) :
    StraightTriple p q r ↔
      q.1.val = p.1.val + 1 ∧ r.1.val = q.1.val + 1 ∧
      q.2 = p.2 ∧ r.2 = q.2 := by
  constructor
  · rintro ⟨dr, dc, hd, hq, hr, hcq, hcr⟩
    have hp := p.2.isLt
    have hq' := q.2.isLt
    have hr' := r.2.isLt
    rcases hd with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩
    · omega
    · refine ⟨by omega, by omega, Fin.ext (by omega), Fin.ext (by omega)⟩
    · omega
    · omega
  · rintro ⟨hq, hr, hcq, hcr⟩
    refine ⟨1, 0, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · rw [hcq]; omega
    · rw [hcr]; omega

private def ColumnLegal {n : ℕ} (w : Fin n → Bool) : Prop :=
  ∀ p q r : Fin n, q.val = p.val + 1 → r.val = q.val + 1 →
    ¬ Forbidden (w p) (w q) (w r)

private theorem avoids_iff {n : ℕ} (A : Fin n → Fin 2 → Bool) :
    Avoids A ↔ ∀ c : Fin 2, ColumnLegal (fun i => A i c) := by
  constructor
  · intro h c p q r hq hr
    exact h (p,c) (q,c) (r,c) ((straight_iff _ _ _).2 ⟨hq,hr,rfl,rfl⟩)
  · intro h p q r ht
    obtain ⟨hq,hr,hcq,hcr⟩ := (straight_iff _ _ _).1 ht
    have ht' := h p.2 p.1 q.1 r.1 hq hr
    simpa only [hcr, hcq] using ht'

/-- Local forbidden triples are exactly two successive true switches. -/
private theorem forbidden_switch (x y z : Bool) :
    Forbidden x y z ↔ (Bool.xor x y = true ∧ Bool.xor y z = true) := by
  cases x <;> cases y <;> cases z <;> simp [Forbidden]

private def switches {m : ℕ} (w : Fin (m + 1) → Bool) : Fin m → Bool :=
  fun i => Bool.xor (w i.castSucc) (w i.succ)

private theorem column_switch_iff {m : ℕ} (w : Fin (m + 1) → Bool) :
    ColumnLegal w ↔ Adm m (switches w) := by
  rw [adm_iff_no_adjacent_true]
  constructor
  · intro h i j hij
    have hj : i.succ = j.castSucc := Fin.ext hij
    have hh := h i.castSucc i.succ j.succ (by simp) (by simp only [Fin.val_succ]; omega)
    rw [forbidden_switch] at hh
    have hs : ¬ (switches w i = true ∧ switches w j = true) := by
      simpa only [switches, hj] using hh
    cases hi : switches w i <;> cases hj : switches w j <;> simp_all
  · intro h p q r hq hr
    have hp := p.isLt
    have hq' := q.isLt
    have hr' := r.isLt
    let i : Fin m := ⟨p.val, by omega⟩
    let j : Fin m := ⟨q.val, by omega⟩
    have hi : i.castSucc = p := Fin.ext rfl
    have his : i.succ = q := Fin.ext (by simpa [i] using hq.symm)
    have hj : j.castSucc = q := Fin.ext rfl
    have hjs : j.succ = r := Fin.ext (by simpa [j] using hr.symm)
    have hs := h i j (by simpa [i, j] using hq.symm)
    rw [forbidden_switch]
    simpa only [switches, hi, his, hj, hjs, Bool.eq_false_iff, not_and_or] using hs

private theorem switches_reconstruct {m : ℕ} (b : Bool) (d : Fin m → Bool) :
    switches (fun i => b + Fin.partialSum d i) = d := by
  funext i
  change (b + Fin.partialSum d i.castSucc) + (b + Fin.partialSum d i.succ) = d i
  rw [add_add_add_comm, BooleanRing.add_self, zero_add]
  exact Fin.partialSum_right_neg d i

private def switchEquiv (m : ℕ) :
    {w : Fin (m + 1) → Bool // ColumnLegal w} ≃
      Bool × {d : Fin m → Bool // Adm m d} where
  toFun w := (w.val 0, ⟨switches w.val, (column_switch_iff _).1 w.property⟩)
  invFun p := ⟨fun i => p.1 + Fin.partialSum p.2.val i, (column_switch_iff _).2 (by
    rw [switches_reconstruct]
    exact p.2.property)⟩
  left_inv w := Subtype.ext (by
    change (fun i => w.val 0 + Fin.partialSum (switches w.val) i) = w.val
    have hs : switches w.val = (fun j => -w.val j.castSucc + w.val j.succ) := rfl
    rw [hs]
    exact Fin.partialSum_left_neg w.val)
  right_inv p := by
    apply Prod.ext
    · simp only [Fin.partialSum_zero, add_zero]
    · apply Subtype.ext
      exact switches_reconstruct p.1 p.2.val

private def arrayEquiv (n : ℕ) :
    {A : Fin n → Fin 2 → Bool // Avoids A} ≃
      ({w : Fin n → Bool // ColumnLegal w} × {w : Fin n → Bool // ColumnLegal w}) :=
  ((Equiv.piComm (fun (_ : Fin n) (_ : Fin 2) => Bool)).subtypeEquiv
    (fun A => avoids_iff A)).trans
    ((Equiv.subtypePiEquivPi).trans (piFinTwoEquiv _))

private theorem column_card (m : ℕ) :
    Nat.card {w : Fin (m + 1) → Bool // ColumnLegal w} = 2 * Nat.fib (m+2) := by
  rw [Nat.card_congr (switchEquiv m), Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool, admissibleWord_card_eq_fib]

private theorem array_count (n : ℕ) (hn : 1 ≤ n) : a n = 4 * Nat.fib (n+1)^2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  unfold a
  rw [Nat.card_congr (arrayEquiv (m + 1)), Nat.card_prod, column_card]
  ring

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 2 * (a (n-1) : ℤ) + 2 * (a (n-2) : ℤ) - (a (n-3) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n-4, by omega⟩
  rw [show k+4-1 = k+3 by omega, show k+4-2 = k+2 by omega,
    show k+4-3 = k+1 by omega]
  rw [array_count (k+4) (by omega), array_count (k+3) (by omega),
    array_count (k+2) (by omega), array_count (k+1) (by omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [Nat.fib_add_two (n := k+3), Nat.fib_add_two (n := k+2)]
  push_cast
  ring

private theorem generating_function :
    gf * (1 - 2 * X - 2 * X^2 + X^3) = 4 * X + 8 * X^2 - 4 * X^3 := by
  have a1 : a 1 = 4 := by norm_num [array_count, Nat.fib]
  have a2 : a 2 = 16 := by norm_num [array_count, Nat.fib]
  have a3 : a 3 = 36 := by norm_num [array_count, Nat.fib]
  have expand : gf * (1 - 2 * X - 2 * X^2 + X^3) =
      gf - 2 * (gf * X^1) - 2 * (gf * X^2) + gf * X^3 := by ring
  rw [expand]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul]
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X,
    PowerSeries.coeff_X_pow, gf, PowerSeries.coeff_mk]
  by_cases hn : 4 ≤ n
  · have hn0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
    have hn1 : n-1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr (by omega)
    have hn2 : n-2 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr (by omega)
    have hn3 : n-3 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hn
    simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_right hn0, ite_eq_right hn1, ite_eq_right hn2,
      ite_eq_right hn3,
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega)]
    have hrec := recurrence n hn
    linarith
  · interval_cases n <;> norm_num [a1, a2, a3]

theorem result : claim := by
  exact ⟨recurrence, generating_function⟩

end D5.S1.Words.AdmissibleWords.HardinWidthTwoRecurrence
