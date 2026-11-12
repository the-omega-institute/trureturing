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
import Mathlib.Tactic.FinCases

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
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

private theorem xor_rectangle : ∀ a b c d x y : Fin 4,
    a = (x ^^^ y) ^^^ b → a ^^^ c = b ^^^ d →
    c = (x ^^^ y) ^^^ d := by
  decide +kernel

private theorem xor_cross : ∀ a b c d : Fin 4,
    a ^^^ b = c ^^^ d → a ^^^ c = b ^^^ d := by
  decide +kernel

private theorem xor_cancel : ∀ a b c : Fin 4,
    a ^^^ b = a ^^^ c ↔ b = c := by
  decide +kernel

private theorem xor_nonzero : ∀ a b : Fin 4, a ^^^ b ≠ 0 ↔ a ≠ b := by
  decide +kernel

private theorem square_exhausts : ∀ a b c d : Fin 4,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ k, k = a ∨ k = b ∨ k = c ∨ k = d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

private theorem proper_square {n : ℕ} (c : Fin n × Fin 6 → Fin 4)
    (hc : Proper c) (i : ℕ) (hi : i + 1 < n) (j : Fin 5) :
    c (⟨i, by omega⟩, j.castSucc) ^^^ c (⟨i, by omega⟩, j.succ) =
      c (⟨i+1,hi⟩, j.castSucc) ^^^ c (⟨i+1,hi⟩, j.succ) := by
  apply square_xor
  all_goals
    apply hc
    · intro h
      have h₁ := congrArg (fun p : Fin n × Fin 6 => p.1.val) h
      have h₂ := congrArg (fun p : Fin n × Fin 6 => p.2.val) h
      dsimp at h₁ h₂
      omega
    all_goals dsimp; omega

private theorem horizontal_invariant {n : ℕ} (hn : 0 < n)
    (c : Fin n × Fin 6 → Fin 4) (hc : Proper c) (i : Fin n) (j : Fin 5) :
    c (i,j.castSucc) ^^^ c (i,j.succ) =
      c (⟨0,hn⟩,j.castSucc) ^^^ c (⟨0,hn⟩,j.succ) := by
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    exact (proper_square c hc i hi j).symm.trans (ih (by omega))

private theorem vertical_invariant {n : ℕ}
    (c : Fin n × Fin 6 → Fin 4) (hc : Proper c)
    (i : ℕ) (hi : i + 1 < n) (j : Fin 6) :
    c (⟨i,by omega⟩,j) ^^^ c (⟨i+1,hi⟩,j) =
      c (⟨i,by omega⟩,0) ^^^ c (⟨i+1,hi⟩,0) := by
  obtain ⟨j,hj⟩ := j
  induction j with
  | zero => rfl
  | succ j ih =>
    have h := xor_cross _ _ _ _ (proper_square c hc i hi (⟨j,by omega⟩ : Fin 5))
    exact h.symm.trans (ih (by omega))

private theorem proper_rectangle {n : ℕ} (hn : 0 < n)
    (c : Fin n × Fin 6 → Fin 4) (hc : Proper c) (i : Fin n) (j : Fin 6) :
    c (i,j) = (c (i,0) ^^^ c (⟨0,hn⟩,0)) ^^^ c (⟨0,hn⟩,j) := by
  obtain ⟨j,hj⟩ := j
  induction j with
  | zero =>
    change c (i,0) = (c (i,0) ^^^ c (⟨0,hn⟩,0)) ^^^ c (⟨0,hn⟩,0)
    simp only [Fin.xor_assoc (show 4 = 2^2 from rfl), Fin.xor_self, Fin.xor_zero]
  | succ j ih =>
    have h := horizontal_invariant hn c hc i (⟨j, by omega⟩ : Fin 5)
    exact xor_rectangle _ _ _ _ _ _ (ih (by omega)) h

private theorem legal_proper {n : ℕ} (f : Fin n × Fin 6 → Fin 8) (hf : Legal f) :
    Proper (fun p => beta (f p)) := by
  intro p q hp hr hs ht hu
  exact (colour_bond_iff _ _).mp (hf.2.1 p q hp hr hs ht hu)

private theorem proper_increments {n : ℕ} (hn : 0 < n)
    (c : Fin n × Fin 6 → Fin 4) (hc : Proper c) :
    (∀ j : Fin 5, c (⟨0,hn⟩,j.castSucc) ^^^ c (⟨0,hn⟩,j.succ) ≠ 0) ∧
    (∀ (i : ℕ) (hi : i + 1 < n),
      c (⟨i,by omega⟩,0) ^^^ c (⟨i+1,hi⟩,0) ≠ 0 ∧
      ∀ j : Fin 5,
        c (⟨0,hn⟩,j.castSucc) ^^^ c (⟨0,hn⟩,j.succ) ≠
          c (⟨i,by omega⟩,0) ^^^ c (⟨i+1,hi⟩,0)) := by
  constructor
  · intro j
    apply (xor_nonzero _ _).mpr
    apply hc
    · intro h
      have := congrArg (fun p : Fin n × Fin 6 => p.2.val) h
      dsimp at this
      omega
    all_goals dsimp; omega
  · intro i hi
    constructor
    · apply (xor_nonzero _ _).mpr
      apply hc
      · intro h
        have := congrArg (fun p : Fin n × Fin 6 => p.1.val) h
        dsimp at this
        omega
      all_goals dsimp; omega
    · intro j h
      rw [← horizontal_invariant hn c hc (⟨i,by omega⟩ : Fin n) j,
        ← vertical_invariant c hc i hi j.castSucc] at h
      have he := (xor_cancel _ _ _).mp h
      apply hc (⟨i,by omega⟩,j.succ) (⟨i+1,hi⟩,j.castSucc) _ _ _ _ _ he
      · intro h
        have := congrArg (fun p : Fin n × Fin 6 => p.1.val) h
        dsimp at this
        omega
      all_goals dsimp; omega

private theorem proper_exhausts {n : ℕ} (hn : 2 ≤ n)
    (c : Fin n × Fin 6 → Fin 4) (hc : Proper c) :
    ∀ k : Fin 4, ∃ p, p.1.val ≤ 1 ∧ c p = k := by
  have h := square_exhausts
    (c (⟨0,by omega⟩,0)) (c (⟨0,by omega⟩,1))
    (c (⟨1,by omega⟩,0)) (c (⟨1,by omega⟩,1))
  have hpair : ∀ p q : Fin 2 × Fin 2, p ≠ q →
      c (⟨p.1.val,by omega⟩,⟨p.2.val,by omega⟩) ≠
        c (⟨q.1.val,by omega⟩,⟨q.2.val,by omega⟩) := by
    intro p q hp
    apply hc
    · intro he
      apply hp
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg (fun p : Fin n × Fin 6 => p.1.val) he
      · exact congrArg (fun p : Fin n × Fin 6 => p.2.val) he
    all_goals dsimp; omega
  have hfull := h (hpair (0,0) (0,1) (by decide))
    (hpair (0,0) (1,0) (by decide)) (hpair (0,0) (1,1) (by decide))
    (hpair (0,1) (1,0) (by decide)) (hpair (0,1) (1,1) (by decide))
    (hpair (1,0) (1,1) (by decide))
  intro k
  rcases hfull k with h | h | h | h
  · exact ⟨(⟨0,by omega⟩,0),by decide,h.symm⟩
  · exact ⟨(⟨0,by omega⟩,1),by decide,h.symm⟩
  · exact ⟨(⟨1,by omega⟩,0),by decide,h.symm⟩
  · exact ⟨(⟨1,by omega⟩,1),by decide,h.symm⟩

private theorem legal_seen {n : ℕ} (hn : 2 ≤ n)
    (f : Fin n × Fin 6 → Fin 8) (hf : Legal f) :
    ∀ d : Fin 3, ∃ p, p.1.val ≤ 1 ∧ (f p).val = d.val + 1 := by
  obtain ⟨p,hp,hp3⟩ := proper_exhausts hn _ (legal_proper f hf) 3
  have hβ : ∀ x : Fin 8, beta x = 3 → x = 3 ∨ x = 4 := by decide +kernel
  obtain ⟨q,hq,hq3⟩ : ∃ q, q.1.val ≤ 1 ∧ f q = 3 := by
    rcases hβ (f p) hp3 with h | h
    · exact ⟨p,hp,h⟩
    · obtain ⟨q,hq,hq3⟩ := (hf.2.2 p).2.2 h
      refine ⟨q,?_,hq3⟩
      have := p.2.isLt
      omega
  obtain ⟨q₁,hq₁,hq₁c⟩ := (hf.2.2 q).1 (Or.inr (Or.inl hq3))
  obtain ⟨q₂,hq₂,hq₂c⟩ := (hf.2.2 q).2.1 (Or.inl hq3)
  have hr₁ : q₁.1.val ≤ 1 := by have := q.2.isLt; omega
  have hr₂ : q₂.1.val ≤ 1 := by have := q.2.isLt; omega
  intro d
  fin_cases d
  · exact ⟨q₁,hr₁,by simp [hq₁c]⟩
  · exact ⟨q₂,hr₂,by simp [hq₂c]⟩
  · exact ⟨q,hq,by simp [hq3]⟩

/-- The complete necessary zone data of a literal strip of height at least two. -/
theorem pair_rectangle {n : ℕ} (hn : 2 ≤ n)
    (f : Fin n × Fin 6 → Fin 8) (hf : Legal f) :
    let c := fun p => beta (f p)
    let z : Fin n := ⟨0,by omega⟩
    (∀ i j, c (i,j) = (c (i,0) ^^^ c (z,0)) ^^^ c (z,j)) ∧
    (∀ j : Fin 5, c (z,j.castSucc) ^^^ c (z,j.succ) ≠ 0) ∧
    (∀ (i : ℕ) (hi : i + 1 < n),
      c (⟨i,by omega⟩,0) ^^^ c (⟨i+1,hi⟩,0) ≠ 0 ∧
      ∀ j : Fin 5, c (z,j.castSucc) ^^^ c (z,j.succ) ≠
        c (⟨i,by omega⟩,0) ^^^ c (⟨i+1,hi⟩,0)) ∧
    (∀ k : Fin 4, ∃ p, p.1.val ≤ 1 ∧ c p = k) ∧
    (∀ d : Fin 3, ∃ p, p.1.val ≤ 1 ∧ (f p).val = d.val + 1) := by
  have hc := legal_proper f hf
  exact ⟨proper_rectangle (by omega) _ hc,
    (proper_increments (by omega) _ hc).1,
    (proper_increments (by omega) _ hc).2, proper_exhausts hn _ hc,
    legal_seen hn f hf⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
