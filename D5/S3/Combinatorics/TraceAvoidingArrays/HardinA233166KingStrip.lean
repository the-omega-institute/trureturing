/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Literal six-column king strips and their four-colour rectangle structure. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Fin.Init

/-!
The literal array count retains strict first-occurrence conditions and free
boundaries. The rectangle identity concerns complementary colour pairs; it
does not count signed lifts or assert the generating-function conjecture.
-/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
  (beta colour_bond_iff)

/-- The literal constraints, including every distinct neighbouring cell pair. -/
def Legal {n : ℕ} (f : Fin n × Fin 6 → Fin 8) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ f (i, 0) = 0) ∧
  (∀ p q, p ≠ q →
    p.1.val ≤ q.1.val + 1 → q.1.val ≤ p.1.val + 1 →
    p.2.val ≤ q.2.val + 1 → q.2.val ≤ p.2.val + 1 →
    f p ≠ f q ∧ (f p).val + (f q).val ≠ 7) ∧
  (∀ p,
    ((f p = 2 ∨ f p = 3 ∨ f p = 4 ∨ f p = 5 ∨ f p = 6) →
      ∃ q, 6*q.1.val + q.2.val < 6*p.1.val + p.2.val ∧ f q = 1) ∧
    ((f p = 3 ∨ f p = 4 ∨ f p = 5) →
      ∃ q, 6*q.1.val + q.2.val < 6*p.1.val + p.2.val ∧ f q = 2) ∧
    (f p = 4 →
      ∃ q, 6*q.1.val + q.2.val < 6*p.1.val + p.2.val ∧ f q = 3))

/-- Cardinality of actual functions; the empty-height coefficient is zero. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Fin n × Fin 6 → Fin 8 => Legal f)).card

/-- The full conjunction, with all universal onsets and the exceptional prefix. -/
def claim : Prop :=
  a 1 = 236 ∧
  (PowerSeries.mk fun n => (a n : ℚ)) =
    4*PowerSeries.X*(59-10304*PowerSeries.X+356352*PowerSeries.X^2)*
      ((1-64*PowerSeries.X)*(1-128*PowerSeries.X))⁻¹ ∧
  (∀ n : ℕ, 2 ≤ n → a n = 64^(n-1)*(2^n+60)) ∧
  (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 192*(a (n-1) : ℤ)-8192*(a (n-2) : ℤ))

private def Proper {n : ℕ} (c : Fin n × Fin 6 → Fin 4) : Prop :=
  ∀ p q, p ≠ q →
    p.1.val ≤ q.1.val + 1 → q.1.val ≤ p.1.val + 1 →
    p.2.val ≤ q.2.val + 1 → q.2.val ≤ p.2.val + 1 → c p ≠ c q

private theorem square_xor : ∀ a b c d : Fin 4,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    a ^^^ b = c ^^^ d := by
  decide +kernel

private theorem xor_transport : ∀ a b c d : Fin 4,
    a ^^^ b = c ^^^ d → d = (c ^^^ a) ^^^ b := by
  decide +kernel

private theorem xor_rectangle : ∀ a b c d x y : Fin 4,
    b = (a ^^^ x) ^^^ y → c ^^^ d = a ^^^ b →
    d = (c ^^^ x) ^^^ y := by
  decide +kernel

private theorem proper_square {n : ℕ} (c : Fin n × Fin 6 → Fin 4)
    (hc : Proper c) (i : ℕ) (hi : i+1<n) (j : Fin 5) :
    c (⟨i, by omega⟩, j.castSucc) ^^^ c (⟨i, by omega⟩, j.succ) =
      c (⟨i+1,hi⟩, j.castSucc) ^^^ c (⟨i+1,hi⟩, j.succ) := by
  apply square_xor
  all_goals apply hc <;> (first | intro h; have := congrArg (fun p => p.1.val) h;
      have := congrArg (fun p => p.2.val) h; simp at *; omega | simp; omega)

private theorem horizontal_invariant {n : ℕ} (hn : 0<n)
    (c : Fin n × Fin 6 → Fin 4) (hc : Proper c) (i : Fin n) (j : Fin 5) :
    c (i,j.castSucc) ^^^ c (i,j.succ) =
      c (⟨0,hn⟩,j.castSucc) ^^^ c (⟨0,hn⟩,j.succ) := by
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    exact (proper_square c hc i hi j).symm.trans (ih (by omega))

private theorem proper_rectangle {n : ℕ} (hn : 0<n)
    (c : Fin n × Fin 6 → Fin 4) (hc : Proper c) (i : Fin n) (j : Fin 6) :
    c (i,j) = (c (i,0) ^^^ c (⟨0,hn⟩,0)) ^^^ c (⟨0,hn⟩,j) := by
  obtain ⟨j,hj⟩ := j
  induction j with
  | zero => simp only [Fin.xor_assoc (show 4 = 2^2 from rfl), Fin.xor_self, Fin.xor_zero]
  | succ j ih =>
    have h := horizontal_invariant hn c hc i (⟨j, by omega⟩ : Fin 5)
    exact xor_rectangle _ _ _ _ _ _ (ih (by omega)) h.symm

/-- Complementary-pair colours separate into the first row and first column. -/
theorem pair_rectangle {n : ℕ} (hn : 0<n)
    (f : Fin n × Fin 6 → Fin 8) (hf : Legal f) :
    ∀ i j, beta (f (i,j)) =
      (beta (f (i,0)) ^^^ beta (f (⟨0,hn⟩,0))) ^^^ beta (f (⟨0,hn⟩,j)) := by
  apply proper_rectangle hn (fun p => beta (f p))
  intro p q hp hr hs ht hu
  exact (colour_bond_iff _ _).mp (hf.2.1 p q hp hr hs ht hu)

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
