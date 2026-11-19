/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-state transfers and continuation counts for the two strip geometries. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Batteries.Tactic.OpenPrivate

/-! Source columns retain every colouring; source rows retain exactly the proper words. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers

open HardinColumnContinuations (Column cross columnV)
open HardinThinGraphTransport (Row proper compatible stripGraph)

section Words
open private continuation tailGood tail_count graph_count from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

/-- A source word of length `k + 1` with adjacent letters different. -/
abbrev Word (k : ℕ) := {p : Row k // proper p}

/-- Source row transfer. With `d = true` it gives R, with `d = false` it gives S. -/
def wordTransfer (d : Bool) (k : ℕ) : Matrix (Word k) (Word k) ℤ :=
  fun p q => if compatible d p.val q.val then 1 else 0

private theorem sum_words {k : ℕ} {A : Type*} [AddCommMonoid A] (f : Row k → A) :
    (∑ p : Word k, f p.val) = ∑ p : Row k, if proper p then f p else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter proper) (by simp) f).symm

private theorem word_power (d : Bool) (k m : ℕ) (p : Word k) :
    ((wordTransfer d k)^m).mulVec (1 : Word k → ℤ) p = continuation d m p.val := by
  induction m generalizing p with
  | zero => simp [continuation]
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    change (∑ q : Word k, (if compatible d p.val q.val then (1 : ℤ) else 0) *
      (((wordTransfer d k)^m).mulVec (1 : Word k → ℤ)) q) = _
    simp only [ih, ite_mul, one_mul, zero_mul, continuation, Nat.cast_sum]
    rw [sum_words (fun q => if compatible d p.val q then (continuation d m q : ℤ) else 0)]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : proper q <;> by_cases h' : compatible d p.val q <;> simp [h, h']

/-- All tails with the first row fixed, in the literal row order. -/
theorem word_continuations (d : Bool) (k m : ℕ) (p : Word k) :
    ((wordTransfer d k)^m).mulVec (1 : Word k → ℤ) p =
      (Nat.card {f : Fin m → Row k // tailGood d p.val f} : ℤ) := by
  rw [word_power, ← tail_count d m p.val, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Summing the full row continuation yields the actual three-colour strip count. -/
theorem word_count (d : Bool) (k m : ℕ) :
    (Nat.card ((stripGraph d m k).Coloring (Fin 3)) : ℤ) =
      ∑ p : Word k, ((wordTransfer d k)^m).mulVec (1 : Word k → ℤ) p := by
  simp only [word_power, graph_count, Nat.cast_sum]
  rw [sum_words (fun p => (continuation d m p : ℤ))]
  exact Finset.sum_congr rfl (fun p _ => by split_ifs <;> simp)

end Words

open private tailGood tail_count tail_local graph_count from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations

private theorem cross_iff {h : ℕ} (p q : Column h) :
    cross p q ↔ ∀ r s : Fin (h + 1),
      (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) → p r ≠ q s := by
  constructor
  · rintro ⟨same, edge⟩ r s ⟨h₁, h₂⟩
    rcases lt_trichotomy r.val s.val with lt | eq | gt
    · let j : Fin h := ⟨r.val, by omega⟩
      have hr : r = j.castSucc := Fin.ext rfl
      have hs : s = j.succ := Fin.ext (by simp [j]; omega)
      rw [hr, hs]
      exact (edge j).1
    · have hs : s = r := Fin.ext eq.symm
      rw [hs]
      exact same r
    · let j : Fin h := ⟨s.val, by omega⟩
      have hr : r = j.succ := Fin.ext (by simp [j]; omega)
      have hs : s = j.castSucc := Fin.ext rfl
      rw [hr, hs]
      exact (edge j).2
  · intro f
    exact ⟨fun i => f i i (by omega), fun j => ⟨f j.castSucc j.succ (by simp <;> omega),
      f j.succ j.castSucc (by simp <;> omega)⟩⟩

/-- Source C on all unrestricted columns of height `h + 1`. -/
def C (h : ℕ) : Matrix (Column h) (Column h) ℤ :=
  fun p q => if cross p q then 1 else 0

/-- Powers of C give the continuation with the first column fixed. -/
theorem column_power (h m : ℕ) (p : Column h) :
    ((C h)^m).mulVec (1 : Column h → ℤ) p = columnV m p := by
  induction m generalizing p with
  | zero => simp [columnV]
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    change (∑ q : Column h, (if cross p q then (1 : ℤ) else 0) *
      (((C h)^m).mulVec (1 : Column h → ℤ)) q) = _
    simp only [ih, ite_mul, one_mul, zero_mul, columnV, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> simp)

/-- All tails with the first unrestricted column fixed, in the literal column order. -/
theorem column_continuations (h m : ℕ) (p : Column h) :
    ((C h)^m).mulVec (1 : Column h → ℤ) p =
      (Nat.card {f : Fin m → Column h // tailGood p f} : ℤ) := by
  rw [column_power, ← tail_count m p, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The source transfer remains valid for one column, with no bonds to a further column. -/
theorem column_count (h m : ℕ) :
    (Nat.card ((stripGraph true h m).Coloring (Fin 3)) : ℤ) =
      ∑ p : Column h, ((C h)^m).mulVec (1 : Column h → ℤ) p := by
  simp only [column_power, graph_count, Nat.cast_sum]

/-- Exact solution of the continuation powers under a colour-class quotient.
Every fibre contributes exactly its row count, including for a state with no successors. -/
theorem powerOnes_of_rows {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (T : Matrix A A ℤ) (Q : Matrix B B ℤ) (cls : A → B)
    (rows : ∀ a b, (∑ x : A, if cls x = b then T a x else 0) = Q (cls a) b)
    (m : ℕ) (a : A) :
    (T ^ m).mulVec (1 : A → ℤ) a = (Q ^ m).mulVec (1 : B → ℤ) (cls a) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ', ← Matrix.mulVec_mulVec]
    change (∑ x, T a x * (T ^ m).mulVec (1 : A → ℤ) x) =
      ∑ y, Q (cls a) y * (Q ^ m).mulVec (1 : B → ℤ) y
    simp only [ih, ← rows, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp only [ite_mul, zero_mul]
    simp

/-- Source lag coefficients in order from one to the full degree. The row shift
is one, and the proper-word shift is zero. -/
def IsLagRelation {A : Type*} [Fintype A] [DecidableEq A]
    (T : Matrix A A ℤ) (b : ℕ) {d : ℕ} (c : Fin d → ℤ) : Prop :=
  (T ^ (b + d)).mulVec (1 : A → ℤ) =
    ∑ j : Fin d, c j • (T ^ (b + d-(j.val + 1))).mulVec (1 : A → ℤ)

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers
