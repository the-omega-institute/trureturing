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
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721EdgeDifferences

/-!
The literal array count retains strict first-occurrence conditions and free
boundaries. The rectangle identity concerns complementary colour pairs; it
does not count signed lifts or assert the generating-function conjecture.
-/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

set_option maxRecDepth 100000
-- Finite pair-word cardinality conversions require a larger elaboration budget.
set_option maxHeartbeats 4000000

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

def Proper {n : ℕ} (c : Fin n × Fin 6 → Fin 4) : Prop :=
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
  · exact ⟨(⟨0,by omega⟩,0),by simp,h.symm⟩
  · exact ⟨(⟨0,by omega⟩,1),by simp,h.symm⟩
  · exact ⟨(⟨1,by omega⟩,0),by simp,h.symm⟩
  · exact ⟨(⟨1,by omega⟩,1),by simp,h.symm⟩

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

private def choices (h : Fin 5 → Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun v => v ≠ 0 ∧ ∀ j, h j ≠ v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem choices_card : ∀ h : Fin 5 → Fin 4,
    (∀ j, h j ≠ 0) → (∃ v, v ≠ 0 ∧ ∀ j, h j ≠ v) →
    (choices h).card = if ∀ j, h j = h 0 then 2 else 1 := by
  intro h
  fin_cases h <;> decide +kernel

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
    (∀ d : Fin 3, ∃ p, p.1.val ≤ 1 ∧ (f p).val = d.val + 1) ∧
    ((Finset.univ.filter (fun v : Fin 4 => v ≠ 0 ∧ ∀ j : Fin 5,
      c (z,j.castSucc) ^^^ c (z,j.succ) ≠ v)).card =
      if ∀ j : Fin 5, c (z,j.castSucc) ^^^ c (z,j.succ) = c (z,0) ^^^ c (z,1)
      then 2 else 1) := by
  have hc := legal_proper f hf
  refine ⟨proper_rectangle (by omega) _ hc,
    (proper_increments (by omega) _ hc).1,
    (proper_increments (by omega) _ hc).2, proper_exhausts hn _ hc,
    legal_seen hn f hf, ?_⟩
  apply choices_card
  · exact (proper_increments (by omega) _ hc).1
  · exact ⟨_, (proper_increments (by omega) _ hc).2 0 (by omega)⟩


/-- First-column values and first-row offsets with disjoint nonzero increments. -/
def zones (n : ℕ) : Set ((Fin n → Fin 4) × (Fin 6 → Fin 4)) := fun z =>
  z.2 0 = 0 ∧
  (∀ j : Fin 5, z.2 j.castSucc ^^^ z.2 j.succ ≠ 0) ∧
  (∀ (i : ℕ) (hi : i + 1 < n),
    z.1 ⟨i,by omega⟩ ^^^ z.1 ⟨i+1,hi⟩ ≠ 0 ∧
    ∀ j : Fin 5, z.2 j.castSucc ^^^ z.2 j.succ ≠
      z.1 ⟨i,by omega⟩ ^^^ z.1 ⟨i+1,hi⟩)

private theorem xor_shift : ∀ a b c : Fin 4,
    (a ^^^ b) ^^^ (a ^^^ c) = b ^^^ c := by decide +kernel

private theorem adjacent_delta {m : ℕ} (u : Fin m → Fin 4) (i r : Fin m)
    (hir : i.val ≤ r.val + 1) (hri : r.val ≤ i.val + 1) :
    (i = r ∧ u i ^^^ u r = 0) ∨
    ∃ (k : ℕ) (hk : k + 1 < m),
      u i ^^^ u r = u ⟨k,by omega⟩ ^^^ u ⟨k+1,hk⟩ := by
  by_cases h : i = r
  · exact Or.inl ⟨h,by simp [h]⟩
  · right
    have hval : i.val ≠ r.val := fun he => h (Fin.ext he)
    by_cases hil : i.val < r.val
    · have hk : i.val + 1 < m := by omega
      have he : r = ⟨i.val+1,hk⟩ := Fin.ext (by dsimp; omega)
      refine ⟨i.val,hk,?_⟩
      exact congrArg (fun t => u i ^^^ u t) he
    · have hk : r.val + 1 < m := by omega
      have he : i = ⟨r.val+1,hk⟩ := Fin.ext (by dsimp; omega)
      refine ⟨r.val,hk,?_⟩
      exact (congrArg (fun t => u t ^^^ u r) he).trans (Fin.xor_comm _ _)

private theorem zones_proper {n : ℕ}
    (z : (Fin n → Fin 4) × (Fin 6 → Fin 4)) (hz : z ∈ zones n) :
    Proper (fun p => z.1 p.1 ^^^ z.2 p.2) := by
  intro p q hp hir hri hjs hsj he
  have hd := xor_cross _ _ _ _ he
  rcases adjacent_delta z.1 p.1 q.1 hir hri with ⟨hr,hrz⟩ | ⟨i,hi,he⟩
  · rcases adjacent_delta z.2 p.2 q.2 hjs hsj with ⟨hs,hsz⟩ | ⟨j,hj,hje⟩
    · exact hp (Prod.ext hr hs)
    · have hh := hz.2.1 (⟨j,by omega⟩ : Fin 5)
      change z.2 ⟨j,by omega⟩ ^^^ z.2 ⟨j+1,hj⟩ ≠ 0 at hh
      exact hh (hje.symm.trans (hd.symm.trans hrz))
  · rcases adjacent_delta z.2 p.2 q.2 hjs hsj with ⟨hs,hsz⟩ | ⟨j,hj,hje⟩
    · exact (hz.2.2 i hi).1 (he.symm.trans (hd.trans hsz))
    · have hh := (hz.2.2 i hi).2 (⟨j,by omega⟩ : Fin 5)
      change z.2 ⟨j,by omega⟩ ^^^ z.2 ⟨j+1,hj⟩ ≠
        z.1 ⟨i,by omega⟩ ^^^ z.1 ⟨i+1,hi⟩ at hh
      exact hh (hje.symm.trans (hd.symm.trans he))

/-- Every proper pair-colouring is uniquely reconstructed from its zone data. -/
def zoneEquiv {n : ℕ} (hn : 0 < n) :
    {c : Fin n × Fin 6 → Fin 4 // Proper c} ≃ {z // z ∈ zones n} where
  toFun c := ⟨(fun i => c.1 (i,0),
    fun j => c.1 (⟨0,hn⟩,0) ^^^ c.1 (⟨0,hn⟩,j)),by
    refine ⟨by simp, ?_, ?_⟩
    · intro j
      rw [xor_shift]
      exact (proper_increments hn c.1 c.2).1 j
    · intro i hi
      refine ⟨(proper_increments hn c.1 c.2).2 i hi |>.1, ?_⟩
      intro j
      rw [xor_shift]
      exact (proper_increments hn c.1 c.2).2 i hi |>.2 j⟩
  invFun z := ⟨fun p => z.1.1 p.1 ^^^ z.1.2 p.2, zones_proper z.1 z.2⟩
  left_inv c := by
    apply Subtype.ext
    funext p
    have h := proper_rectangle hn c.1 c.2 p.1 p.2
    simpa only [Fin.xor_assoc (show 4 = 2^2 from rfl)] using h.symm
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change z.1.1 i ^^^ z.1.2 0 = z.1.1 i
      rw [z.2.1,Fin.xor_zero]
    · funext j
      change (z.1.1 ⟨0,hn⟩ ^^^ z.1.2 0) ^^^ (z.1.1 ⟨0,hn⟩ ^^^ z.1.2 j) = z.1.2 j
      rw [z.2.1,Fin.xor_zero]
      rw [← Fin.xor_assoc (show 4 = 2^2 from rfl),Fin.xor_self,
        Fin.xor_comm,Fin.xor_zero]


open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open private first_occurrence First firstEquiv canonical_unique from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

private def colourEquiv8 : Fin 8 ≃ Fin 4 × Bool where
  toFun x := (beta x, decide (4 ≤ x.val))
  invFun p := if p.2 then ⟨7 - p.1.val, by have := p.1.isLt; omega⟩
    else ⟨p.1.val, by have := p.1.isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel


private def Normal8 {C : Type*} [LT C] (f : C → Fin 8) : Prop :=
  ∀ i,
    ((f i = 2 ∨ f i = 3 ∨ f i = 4 ∨ f i = 5 ∨ f i = 6) →
      ∃ j, j < i ∧ f j = 1) ∧
    ((f i = 3 ∨ f i = 4 ∨ f i = 5) → ∃ j, j < i ∧ f j = 2) ∧
    (f i = 4 → ∃ j, j < i ∧ f j = 3)

private def FirstSides8 {C : Type*} [LT C] (f : C → Fin 8) : Prop :=
  ∀ i, (∀ j, j < i → beta (f j) ≠ beta (f i)) →
    (f i).val = (beta (f i)).val

private theorem normalization8_iff {C : Type*} [Fintype C] [LinearOrder C]
    (z : C) (hz : ∀ i, z ≤ i) (f : C → Fin 8) (hf : f z = 0) :
    Normal8 f ↔ Canonical (beta ∘ f) ∧ FirstSides8 f := by
  classical
  constructor
  · intro hn
    have before (i : C) (hi : beta (f i) ≠ 0) : z < i := by
      apply lt_of_le_of_ne (hz i)
      intro he
      subst i
      exact hi (by rw [hf]; rfl)
    constructor
    · intro i b hb
      change b < beta (f i) at hb
      by_cases hb0 : b = 0
      · subst b
        exact ⟨z, before i (ne_of_gt hb), by change beta (f z) = 0; rw [hf]; rfl⟩
      · have hx : ∀ x : Fin 8, ∀ b : Fin 4, b ≠ 0 → b < beta x →
            (b = 1 ∧ (x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5)) ∨
            (b = 2 ∧ (x = 3 ∨ x = 4)) := by decide +kernel
        rcases hx (f i) b hb0 hb with ⟨rfl,hx⟩ | ⟨rfl,hx⟩
        · obtain ⟨j,hj,he⟩ := (hn i).1 (by
            rcases hx with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
          exact ⟨j,hj,by change beta (f j) = 1; rw [he]; rfl⟩
        · obtain ⟨j,hj,he⟩ := (hn i).2.1 (by
            rcases hx with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h))
          exact ⟨j,hj,by change beta (f j) = 2; rw [he]; rfl⟩
    · intro i hi
      have hi' := hn i
      generalize he : f i = x at *
      fin_cases x
      · rfl
      · rfl
      · rfl
      · rfl
      · obtain ⟨j,hj,h⟩ := hi'.2.2 rfl
        exact False.elim (hi j hj (by rw [h]; rfl))
      · obtain ⟨j,hj,h⟩ := hi'.2.1 (Or.inr (Or.inr rfl))
        exact False.elim (hi j hj (by rw [h]; rfl))
      · obtain ⟨j,hj,h⟩ := hi'.1 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        exact False.elim (hi j hj (by rw [h]; rfl))
      · have hzlt : z < i := by
          apply lt_of_le_of_ne (hz i)
          intro hei
          have hv := congrArg (fun j => (f j).val) hei
          rw [hf,he] at hv
          norm_num at hv
        exact False.elim (hi z hzlt (by rw [hf]; rfl))
  · rintro ⟨hc,hs⟩
    have lift (i : C) (d : Fin 4) (h : ∃ j, j < i ∧ beta (f j) = d) :
        ∃ j, j < i ∧ f j = ⟨d.val,by have := d.isLt; omega⟩ := by
      obtain ⟨j,hj,hd⟩ := h
      obtain ⟨t,ht,he,hfirst⟩ := first_occurrence (beta ∘ f) j
      have hs' := hs t hfirst
      refine ⟨t,lt_of_le_of_lt ht hj,Fin.ext ?_⟩
      exact hs'.trans (congrArg Fin.val (he.trans hd))
    have earlier (i : C) (h : (f i).val ≠ (beta (f i)).val) :
        ∃ j, j < i ∧ beta (f j) = beta (f i) := by
      by_contra hn
      apply h
      exact hs i (fun j hj he => hn ⟨j,hj,he⟩)
    intro i
    have h1 (h : f i = 2 ∨ f i = 3 ∨ f i = 4 ∨ f i = 5 ∨ f i = 6) :
        ∃ j, j < i ∧ f j = 1 := by
      have hlabel : ∃ j, j < i ∧ beta (f j) = 1 := by
        rcases h with h | h | h | h | h
        · exact hc i 1 (by change (1 : Fin 4) < beta (f i); rw [h]; decide)
        · exact hc i 1 (by change (1 : Fin 4) < beta (f i); rw [h]; decide)
        · exact hc i 1 (by change (1 : Fin 4) < beta (f i); rw [h]; decide)
        · exact hc i 1 (by change (1 : Fin 4) < beta (f i); rw [h]; decide)
        · simpa only [h,show beta (6 : Fin 8) = 1 from rfl] using
            earlier i (by rw [h]; decide)
      exact lift i 1 hlabel
    have h2 (h : f i = 3 ∨ f i = 4 ∨ f i = 5) :
        ∃ j, j < i ∧ f j = 2 := by
      have hlabel : ∃ j, j < i ∧ beta (f j) = 2 := by
        rcases h with h | h | h
        · exact hc i 2 (by change (2 : Fin 4) < beta (f i); rw [h]; decide)
        · exact hc i 2 (by change (2 : Fin 4) < beta (f i); rw [h]; decide)
        · simpa only [h,show beta (5 : Fin 8) = 2 from rfl] using
            earlier i (by rw [h]; decide)
      exact lift i 2 hlabel
    refine ⟨h1,h2,?_⟩
    intro h
    apply lift i 3
    simpa only [h,show beta (4 : Fin 8) = 3 from rfl] using
      earlier i (by rw [h]; decide)

private abbrev Fibre8 {C : Type*} [LT C] (P : C → Fin 4) :=
  {f : C → Fin 8 // (∀ i, beta (f i) = P i) ∧ FirstSides8 f}

private theorem side_false8 (x : Fin 8) :
    (colourEquiv8 x).2 = false ↔ x.val = (beta x).val := by
  fin_cases x <;> decide +kernel

private noncomputable def fibreEquiv8 {C : Type*} [Fintype C] [LinearOrder C]
    (P : C → Fin 4) : Fibre8 P ≃ ({i // ¬ First P i} → Bool) := by
  classical
  let build (b : {i // ¬ First P i} → Bool) (i : C) : Fin 8 :=
    colourEquiv8.symm (P i, if hi : First P i then false else b ⟨i, hi⟩)
  have build_label (b : {i // ¬ First P i} → Bool) (i : C) :
      beta (build b i) = P i := by
    exact congrArg Prod.fst (colourEquiv8.apply_symm_apply _)
  have build_bit (b : {i // ¬ First P i} → Bool) (i : C) :
      (colourEquiv8 (build b i)).2 = if hi : First P i then false else b ⟨i, hi⟩ := by
    exact congrArg Prod.snd (colourEquiv8.apply_symm_apply _)
  refine {
    toFun := fun f i => (colourEquiv8 (f.val i.val)).2
    invFun := fun b => ⟨build b, build_label b, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro i hi
    apply (side_false8 _).mp
    rw [build_bit]
    have hf : First P i := by
      intro j hj he
      exact hi j hj (by rw [build_label, build_label, he])
    simp only [dite_eq_left hf]
  · intro f
    apply Subtype.ext
    funext i
    change build (fun j => (colourEquiv8 (f.val j.val)).2) i = f.val i
    apply colourEquiv8.injective
    apply Prod.ext
    · change beta (build (fun j => (colourEquiv8 (f.val j.val)).2) i) = beta (f.val i)
      exact (build_label (fun j => (colourEquiv8 (f.val j.val)).2) i).trans
        (f.property.1 i).symm
    · rw [build_bit (fun j => (colourEquiv8 (f.val j.val)).2) i]
      by_cases hi : First P i
      · rw [dite_eq_left hi]
        apply ((side_false8 _).mpr (f.property.2 i ?_)).symm
        intro j hj he
        exact hi j hj (by rw [← f.property.1 j, ← f.property.1 i]; exact he)
      · rw [dite_eq_right hi]
  · intro b
    funext i
    change (colourEquiv8 (build b i.val)).2 = b i
    rw [build_bit, dite_eq_right i.property]

private theorem fibre_card8 {C : Type*} [Fintype C] [LinearOrder C] (P : C → Fin 4) :
    Nat.card (Fibre8 P) = 2 ^ (Fintype.card C - Nat.card (Set.range P)) := by
  classical
  have hf : Fintype.card {i // First P i} = Fintype.card (Set.range P) :=
    Fintype.card_congr (firstEquiv P)
  rw [Nat.card_congr (fibreEquiv8 P), Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, hf,
    Nat.card_eq_fintype_card]


open scoped Classical in
private theorem normalized_card8 {C : Type*} [Fintype C] [LinearOrder C]
    (z : C) (hz : ∀ i, z ≤ i) (S : (C → Fin 4) → Prop) :
    Nat.card {f : C → Fin 8 // S (beta ∘ f) ∧ f z = 0 ∧ Normal8 f} =
      ∑ P : {P : C → Fin 4 // S P ∧ Canonical P},
        2 ^ (Fintype.card C - Nat.card (Set.range P.val)) := by
  classical
  have first_zero (P : C → Fin 4) (hc : Canonical P) : P z = 0 := by
    by_contra hn
    have hlt : (0 : Fin 4) < P z := Fin.pos_iff_ne_zero.mpr hn
    obtain ⟨j, hj, _⟩ := hc z 0 hlt
    exact (not_lt_of_ge (hz j)) hj
  have mk_normal (P : {P : C → Fin 4 // S P ∧ Canonical P}) (f : Fibre8 P.val) :
      S (beta ∘ f.val) ∧ f.val z = 0 ∧ Normal8 f.val := by
    have heq : beta ∘ f.val = P.val := funext f.property.1
    have hc : Canonical (beta ∘ f.val) := by rw [heq]; exact P.property.2
    have hzero : f.val z = 0 := by
      have hfirst := f.property.2 z (fun j hj => False.elim ((not_lt_of_ge (hz j)) hj))
      apply Fin.ext
      exact hfirst.trans (congrArg Fin.val ((f.property.1 z).trans
        (first_zero P.val P.property.2)))
    exact ⟨by rw [heq]; exact P.property.1, hzero,
      (normalization8_iff z hz f.val hzero).mpr ⟨hc, f.property.2⟩⟩
  let E : (Σ P : {P : C → Fin 4 // S P ∧ Canonical P}, Fibre8 P.val) →
      {f : C → Fin 8 // S (beta ∘ f) ∧ f z = 0 ∧ Normal8 f} :=
    fun p => ⟨p.2.val, mk_normal p.1 p.2⟩
  have hE : Function.Bijective E := by
    constructor
    · rintro ⟨P, f⟩ ⟨Q, g⟩ h
      have hfg : f.val = g.val := congrArg Subtype.val h
      have hPQ : P = Q := by
        apply Subtype.ext
        funext i
        rw [← f.property.1 i, ← g.property.1 i, hfg]
      cases hPQ
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hfg))
    · intro f
      have hn := (normalization8_iff z hz f.val f.property.2.1).mp f.property.2.2
      exact ⟨⟨⟨beta ∘ f.val, f.property.1, hn.1⟩, ⟨f.val, fun _ => rfl, hn.2⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective E hE), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro P _
  simpa only [Nat.card_eq_fintype_card] using fibre_card8 P.val

private theorem canonical_pattern_card4 {C : Type*} [Fintype C] [LinearOrder C]
    (S : (C → Fin 4) → Prop)
    (hinv : ∀ e : Equiv.Perm (Fin 4), ∀ P, S (e ∘ P) ↔ S P)
    (huse : ∀ P, S P → Function.Surjective P) :
    Nat.card {P // S P} = 24 * Nat.card {P // S P ∧ Canonical P} := by
  classical
  let E : ({P // S P ∧ Canonical P} × Equiv.Perm (Fin 4)) → {P // S P} :=
    fun q => ⟨q.2 ∘ q.1.val, (hinv q.2 q.1.val).mpr q.1.property.1⟩
  have hE : Function.Bijective E := by
    constructor
    · rintro ⟨Q, e⟩ ⟨R, d⟩ he
      have heq : e ∘ Q.val = d ∘ R.val := congrArg Subtype.val he
      have hQR : Q.val = R.val := by
        apply canonical_unique _ _ Q.property.2 R.property.2
        intro i j
        calc
          Q.val i = Q.val j ↔ e (Q.val i) = e (Q.val j) := e.injective.eq_iff.symm
          _ ↔ d (R.val i) = d (R.val j) := by
            rw [show e (Q.val i) = d (R.val i) from congrFun heq i,
              show e (Q.val j) = d (R.val j) from congrFun heq j]
          _ ↔ R.val i = R.val j := d.injective.eq_iff
      have hsub : Q = R := Subtype.ext hQR
      subst R
      have hed : e = d := by
        ext b
        obtain ⟨i,rfl⟩ := huse Q.val Q.property.1 b
        exact congrArg Fin.val (congrFun heq i)
      exact Prod.ext rfl hed
    · intro P
      obtain ⟨Q, ⟨hQ, e, he⟩, _⟩ := D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique P.val
      have hSQ : S Q := he ▸ (hinv e P.val).mpr P.property
      refine ⟨(⟨Q, hSQ, hQ⟩, e.symm), ?_⟩
      apply Subtype.ext
      funext i
      change e.symm (Q i) = P.val i
      rw [he]
      exact e.symm_apply_apply _
  have hc := Nat.card_congr (Equiv.ofBijective E hE)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 4)),
    Fintype.card_perm, Fintype.card_fin] at hc
  norm_num at hc
  simpa only [Nat.mul_comm, Nat.card_eq_fintype_card] using hc.symm



private theorem legal_word_iff {n : ℕ} (hn : 0 < n) (f : Fin (n*6) → Fin 8) :
    Legal (fun p => f (finProdFinEquiv p)) ↔
      Proper (fun p => beta (f (finProdFinEquiv p))) ∧
        f ⟨0,by omega⟩ = 0 ∧ Normal8 f := by
  constructor
  · intro hf
    refine ⟨legal_proper _ hf, ?_, ?_⟩
    · obtain ⟨i,hi,hf⟩ := hf.1
      have he : finProdFinEquiv (i,(0 : Fin 6)) = (⟨0,by omega⟩ : Fin (n*6)) := by
        apply Fin.ext
        dsimp [finProdFinEquiv]
        omega
      simpa only [he] using hf
    · intro p
      let q : Fin n × Fin 6 := finProdFinEquiv.symm p
      have he : finProdFinEquiv q = p := finProdFinEquiv.apply_symm_apply p
      have h := hf.2.2 q
      dsimp only at h
      rw [he] at h
      have push (d : Fin 8) (h : ∃ r : Fin n × Fin 6,
          6*r.1.val+r.2.val < 6*q.1.val+q.2.val ∧ f (finProdFinEquiv r) = d) :
          ∃ t, t < p ∧ f t = d := by
        obtain ⟨r,hr,hd⟩ := h
        refine ⟨finProdFinEquiv r,?_,hd⟩
        have heval := congrArg Fin.val he
        change (finProdFinEquiv r).val < p.val
        dsimp [finProdFinEquiv] at heval ⊢
        omega
      exact ⟨fun h' => push 1 (h.1 h'), fun h' => push 2 (h.2.1 h'),
        fun h' => push 3 (h.2.2 h')⟩
  · rintro ⟨hp,hz,hnorm⟩
    refine ⟨⟨⟨0,hn⟩,rfl,?_⟩,?_,?_⟩
    · exact hz
    · intro p q hne h₁ h₂ h₃ h₄
      exact (colour_bond_iff _ _).mpr (hp p q hne h₁ h₂ h₃ h₄)
    · intro p
      have h := hnorm (finProdFinEquiv p)
      have pull (d : Fin 8) (h : ∃ t, t < finProdFinEquiv p ∧ f t = d) :
          ∃ q : Fin n × Fin 6,
            6*q.1.val+q.2.val < 6*p.1.val+p.2.val ∧ f (finProdFinEquiv q) = d := by
        obtain ⟨t,ht,hd⟩ := h
        let q : Fin n × Fin 6 := finProdFinEquiv.symm t
        have he : finProdFinEquiv q = t := finProdFinEquiv.apply_symm_apply t
        refine ⟨q,?_,by rw [he]; exact hd⟩
        have heval := congrArg Fin.val he
        change t.val < (finProdFinEquiv p).val at ht
        dsimp [finProdFinEquiv] at heval ht
        omega
      exact ⟨fun h' => pull 1 (h.1 h'),fun h' => pull 2 (h.2.1 h'),
        fun h' => pull 3 (h.2.2 h')⟩

open scoped Classical in
private theorem literal_signed_count {n : ℕ} (hn : 0 < n) :
    a n = ∑ P : {P : Fin (n*6) → Fin 4 //
      Proper (fun p => P (finProdFinEquiv p)) ∧ Canonical P},
      2 ^ (n*6 - Nat.card (Set.range P.val)) := by
  classical
  let S (P : Fin (n*6) → Fin 4) := Proper (fun p => P (finProdFinEquiv p))
  let A := {f : Fin (n*6) → Fin 8 // S (beta ∘ f) ∧ f ⟨0,by omega⟩ = 0 ∧ Normal8 f}
  let E : {f : Fin n × Fin 6 → Fin 8 // Legal f} ≃ A := {
    toFun := fun g => ⟨fun t => g.val (finProdFinEquiv.symm t),
      (legal_word_iff (n := n) hn (fun t => g.val (finProdFinEquiv.symm t))).mp
        (by simpa only [Equiv.symm_apply_apply] using g.property)⟩
    invFun := fun f => ⟨fun p => f.val (finProdFinEquiv p),
      (legal_word_iff (n := n) (by omega) _).mpr f.property⟩
    left_inv := fun f => Subtype.ext (by funext p; simp only [Equiv.symm_apply_apply])
    right_inv := fun f => Subtype.ext (by funext p; simp only [Equiv.apply_symm_apply]) }
  have ha : a n = Nat.card A := by
    rw [← Nat.card_congr E, Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype (fun f => Legal f)).symm
  rw [ha]
  simpa only [A,Fintype.card_fin] using
    normalized_card8 (⟨0,by omega⟩ : Fin (n*6))
      (fun i => show (0 : ℕ) ≤ i.val from Nat.zero_le _) S

/-- The signed fibre and label-permutation factors for the literal count. -/
private theorem literal_pair_count {n : ℕ} (hn : 2 ≤ n) :
    24 * a n = 2^(6*n-4) * Nat.card {c : Fin n × Fin 6 → Fin 4 // Proper c} := by
  classical
  let S (P : Fin (n*6) → Fin 4) := Proper (fun p => P (finProdFinEquiv p))
  have huse : ∀ P, S P → Function.Surjective P := by
    intro P hp k
    obtain ⟨p,_,he⟩ := proper_exhausts hn _ hp k
    exact ⟨finProdFinEquiv p,he⟩
  have hfibre : a n = 2^(6*n-4) * Nat.card {P // S P ∧ Canonical P} := by
    rw [literal_signed_count (by omega : 0 < n)]
    change (∑ P : {P // S P ∧ Canonical P},
      2^(n*6-Nat.card (Set.range P.val))) = _
    have hrange (P : {P // S P ∧ Canonical P}) : Nat.card (Set.range P.val) = 4 := by
      rw [Set.range_eq_univ.mpr (huse P.val P.property.1),Nat.card_univ]
      exact Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)
    simp_rw [hrange]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
    have he : n*6-4 = 6*n-4 := by omega
    rw [he,Nat.mul_comm]
  have hperm := canonical_pattern_card4 S (by
    intro e P
    constructor <;> intro hp p q hne h₁ h₂ h₃ h₄
    · exact fun he => hp p q hne h₁ h₂ h₃ h₄ (congrArg e he)
    · exact fun he => hp p q hne h₁ h₂ h₃ h₄ (e.injective he)) huse
  let EP : {P // S P} ≃ {c : Fin n × Fin 6 → Fin 4 // Proper c} := {
    toFun := fun P => ⟨fun p => P.val (finProdFinEquiv p),P.property⟩
    invFun := fun c => ⟨fun t => c.val (finProdFinEquiv.symm t),by
      simpa only [S,Equiv.symm_apply_apply] using c.property⟩
    left_inv := fun P => Subtype.ext (by funext t; simp only [Equiv.apply_symm_apply])
    right_inv := fun c => Subtype.ext (by funext p; simp only [Equiv.symm_apply_apply]) }
  rw [← Nat.card_congr EP, hperm,hfibre]
  ring


open private count_histories from
  D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721EdgeDifferences

private theorem xor_right_cancel : ∀ x d : Fin 4, x ^^^ (x ^^^ d) = d := by
  decide +kernel

private theorem xor_walk_count (T : Finset (Fin 4)) (m : ℕ) :
    Nat.card {u : Fin (m+1) → Fin 4 // ∀ i : Fin m,
      u i.castSucc ^^^ u i.succ ∈ T} = 4 * T.card^m := by
  classical
  have hdegree (x : Fin 4) :
      (Finset.univ.filter (fun y : Fin 4 => x ^^^ y ∈ T)).card = T.card := by
    apply Finset.card_bij (fun y _ => x ^^^ y)
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
    · intro y hy z hz he
      exact (xor_cancel x y z).mp he
    · intro d hd
      refine ⟨x ^^^ d,?_,xor_right_cancel x d⟩
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,xor_right_cancel,hd]
  have hs (k : ℕ) (x : Fin 4) :
      T.card^(k+1) = ∑ y : Fin 4, if x ^^^ y ∈ T then T.card^k else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul,hdegree]
    rw [pow_succ,Nat.mul_comm]
  have h := count_histories (fun x y : Fin 4 => x ^^^ y ∈ T)
    (fun k _ => T.card^k) (by simp) hs m
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

private def offsetOK (v : Fin 6 → Fin 4) : Prop :=
  v 0 = 0 ∧ ∀ j : Fin 5, v j.castSucc ^^^ v j.succ ≠ 0

private def offsetChoices (v : Fin 6 → Fin 4) : Finset (Fin 4) :=
  choices (fun j => v j.castSucc ^^^ v j.succ)

private instance (v : Fin 6 → Fin 4) : Decidable (offsetOK v) := by
  unfold offsetOK
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem offset_certificate :
    (∀ v : Fin 6 → Fin 4, offsetOK v → (offsetChoices v).card ≤ 2) ∧
    ((Finset.univ.filter (fun v : Fin 6 → Fin 4 =>
      offsetOK v ∧ (offsetChoices v).card = 0)).card = 150) ∧
    ((Finset.univ.filter (fun v : Fin 6 → Fin 4 =>
      offsetOK v ∧ (offsetChoices v).card = 1)).card = 90) ∧
    ((Finset.univ.filter (fun v : Fin 6 → Fin 4 =>
      offsetOK v ∧ (offsetChoices v).card = 2)).card = 3) := by
  decide +kernel

private theorem zones_iff (m : ℕ) (u : Fin (m+1) → Fin 4) (v : Fin 6 → Fin 4) :
    (u,v) ∈ zones (m+1) ↔ offsetOK v ∧ ∀ i : Fin m,
      u i.castSucc ^^^ u i.succ ∈ offsetChoices v := by
  constructor
  · intro hz
    refine ⟨⟨hz.1,hz.2.1⟩,?_⟩
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hz.2.2 i.val (by have := i.isLt; omega)).1,
      (hz.2.2 i.val (by have := i.isLt; omega)).2⟩
  · rintro ⟨hv,hu⟩
    refine ⟨hv.1,hv.2,?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hu (⟨i,by omega⟩ : Fin m))).2

private noncomputable def zoneWordEquiv (m : ℕ) :
    {z // z ∈ zones (m+1)} ≃
      Σ v : {v : Fin 6 → Fin 4 // offsetOK v},
        {u : Fin (m+1) → Fin 4 // ∀ i : Fin m,
          u i.castSucc ^^^ u i.succ ∈ offsetChoices v.val} where
  toFun z := ⟨⟨z.val.2,((zones_iff m _ _).mp z.property).1⟩,
    ⟨z.val.1,((zones_iff m _ _).mp z.property).2⟩⟩
  invFun p := ⟨(p.2.val,p.1.val),(zones_iff m _ _).mpr ⟨p.1.property,p.2.property⟩⟩
  left_inv z := by cases z; rfl
  right_inv p := by rcases p with ⟨⟨v,hv⟩,⟨u,hu⟩⟩; rfl

private theorem offset_sum (m : ℕ) (hm : 1 ≤ m) :
    (∑ v : {v : Fin 6 → Fin 4 // offsetOK v}, (offsetChoices v.val).card^m) =
      3*2^m+90 := by
  classical
  let U : Finset (Fin 6 → Fin 4) := Finset.univ.filter offsetOK
  have hsum : (∑ v : {v : Fin 6 → Fin 4 // offsetOK v},
      (offsetChoices v.val).card^m) = ∑ v ∈ U, (offsetChoices v).card^m := by
    exact (Finset.sum_subtype (p := offsetOK) U
      (by intro v; simp only [U,Finset.mem_filter,Finset.mem_univ,true_and])
      (fun v => (offsetChoices v).card^m)).symm
  rw [hsum]
  have point (v : Fin 6 → Fin 4) (hv : v ∈ U) :
      (offsetChoices v).card^m =
        (if (offsetChoices v).card = 1 then 1 else 0) +
        (if (offsetChoices v).card = 2 then 2^m else 0) := by
    have hb := offset_certificate.1 v (Finset.mem_filter.mp hv).2
    interval_cases h : (offsetChoices v).card <;> simp [h,show m ≠ 0 by omega]
  rw [Finset.sum_congr rfl point,Finset.sum_add_distrib]
  rw [← Finset.sum_filter,← Finset.sum_filter]
  have h1 : (U.filter (fun v => (offsetChoices v).card = 1)).card = 90 := by
    simpa only [U,Finset.filter_filter] using offset_certificate.2.2.1
  have h2 : (U.filter (fun v => (offsetChoices v).card = 2)).card = 3 := by
    simpa only [U,Finset.filter_filter] using offset_certificate.2.2.2
  simp only [Finset.sum_const,smul_eq_mul,h1,h2]
  omega

/-- The exact all-height cardinality of the zone data. -/
private theorem labelled_pair_count (m : ℕ) (hm : 1 ≤ m) :
    Nat.card {c : Fin (m+1) × Fin 6 → Fin 4 // Proper c} =
      4*(3*2^m+90) := by
  classical
  rw [Nat.card_congr (zoneEquiv (by omega)),Nat.card_congr (zoneWordEquiv m),
    Nat.card_sigma]
  simp_rw [xor_walk_count]
  rw [← Finset.mul_sum,offset_sum m hm]


private instance {n : ℕ} (P : Fin n × Fin 6 → Fin 4) : Decidable (Proper P) := by
  unfold Proper
  infer_instance

private instance (P : Fin 6 → Fin 4) : Decidable (Canonical P) := by
  unfold Canonical
  infer_instance

private def oneRowWeight (P : Fin 6 → Fin 4) : ℕ :=
  if Proper (fun p : Fin 1 × Fin 6 => P (finProdFinEquiv p)) ∧ Canonical P
    then 2 ^ (6 - (Finset.univ.image P).card) else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem one_row_certificate : (∑ P : Fin 6 → Fin 4, oneRowWeight P) = 236 := by
  decide +kernel

/-- The exceptional literal one-row cardinality, including unused colours. -/
private theorem one_row_count : a 1 = 236 := by
  classical
  rw [literal_signed_count (by omega : 0 < 1)]
  change (∑ P : {P : Fin 6 → Fin 4 //
    Proper (fun p : Fin 1 × Fin 6 => P (finProdFinEquiv p)) ∧ Canonical P},
      2 ^ (6 - Nat.card (Set.range P.val))) = 236
  have hr (P : Fin 6 → Fin 4) : Nat.card (Set.range P) = (Finset.univ.image P).card := by
    exact Nat.subtype_card (Finset.univ.image P) (by intro b; simp)
  simp_rw [hr]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun P : Fin 6 → Fin 4 =>
    Proper (fun p : Fin 1 × Fin 6 => P (finProdFinEquiv p)) ∧ Canonical P)) (by simp)]
  rw [Finset.sum_filter]
  exact one_row_certificate


private theorem closed_shift (m : ℕ) : a (m+2) = 64^(m+1)*(2^(m+2)+60) := by
  have h := literal_pair_count (by omega : 2 ≤ m+2)
  rw [labelled_pair_count (m+1) (by omega)] at h
  have hp : 2^(6*(m+2)-4) = 4*64^(m+1) := by
    rw [show 6*(m+2)-4 = 6*(m+1)+2 by omega,pow_add,pow_mul]
    norm_num
    ring
  rw [hp] at h
  have h2 : 2^(m+2) = 2^(m+1)*2 := pow_succ 2 (m+1)
  rw [h2]
  nlinarith [h]

/-- Barker's closed formula for every natural height at least two. -/
private theorem closed_count (n : ℕ) (hn : 2 ≤ n) : a n = 64^(n-1)*(2^n+60) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2,by omega⟩
  simpa only [show m+2-1 = m+1 by omega] using closed_shift m

private theorem geometric_shift (m : ℕ) :
    (a (m+2) : ℤ) = 2*128^(m+1)+60*64^(m+1) := by
  rw [closed_shift]
  push_cast
  have hp : (128 : ℤ)^(m+1) = 64^(m+1)*2^(m+1) := by
    rw [← mul_pow]
    norm_num
  rw [hp,pow_succ (2 : ℤ) (m+1)]
  ring

/-- The literal integer recurrence starts at height four. -/
private theorem integer_recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 192*(a (n-1) : ℤ)-8192*(a (n-2) : ℤ) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+4 := ⟨n-4,by omega⟩
  rw [show m+4-1 = (m+1)+2 by omega,show m+4-2 = m+2 by omega,
    show m+4 = (m+2)+2 by omega,geometric_shift,geometric_shift,geometric_shift]
  simp only [pow_succ]
  ring

private theorem zero_count : a 0 = 0 := by
  classical
  simp [a,Legal]

open PowerSeries in
private theorem series_cross :
    ((1-64*X)*(1-128*X)) * (PowerSeries.mk fun n => (a n : ℚ)) =
      4*X*(59-10304*X+356352*X^2) := by
  let F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  have hp : (1-64*X)*(1-128*X)*F =
      F-192*(F*X^1)+8192*(F*X^2) := by ring
  have hr : (4*X*(59-10304*X+356352*X^2) : PowerSeries ℚ) =
      236*X^1-41216*X^2+1425408*X^3 := by ring
  change (1-64*X)*(1-128*X)*F = _
  rw [hp,hr]
  ext n
  simp only [map_add,map_sub,coeff_ofNat_mul,coeff_mul_X_pow',coeff_X_pow,F,coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega),ite_eq_left (show 2 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega),ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega)]
    have hh : (a n : ℚ) = 192*(a (n-1) : ℚ)-8192*(a (n-2) : ℚ) := by
      exact_mod_cast integer_recurrence n hn
    linarith
  · have h2 : a 2 = 4096 := by norm_num [closed_count 2 (by omega)]
    have h3 : a 3 = 278528 := by norm_num [closed_count 3 (by omega)]
    interval_cases n <;> norm_num [zero_count,one_row_count,h2,h3]

/-- The complete literal event: exceptional prefix, formal series, formula and recurrence. -/
theorem result : claim := by
  refine ⟨one_row_count,?_,closed_count,integer_recurrence⟩
  have hd : PowerSeries.constantCoeff
      ((1-64*PowerSeries.X)*(1-128*PowerSeries.X) : PowerSeries ℚ) ≠ 0 := by simp
  have hi := PowerSeries.mul_inv_cancel
    ((1-64*PowerSeries.X)*(1-128*PowerSeries.X) : PowerSeries ℚ) hd
  let D : PowerSeries ℚ := (1-64*PowerSeries.X)*(1-128*PowerSeries.X)
  let F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  have hc : D*F = 4*PowerSeries.X*(59-10304*PowerSeries.X+356352*PowerSeries.X^2) :=
    series_cross
  change F = _*D⁻¹
  calc
    F = F*1 := (mul_one F).symm
    _ = F*(D*D⁻¹) := by rw [hi]
    _ = (D*F)*D⁻¹ := by ring
    _ = _ := congrArg (fun t : PowerSeries ℚ => t*D⁻¹) hc

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

