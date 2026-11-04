/- GID: D5/S3/StatisticalMechanics/NoisyVoter/TerminatedHistories
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/TerminatedHistories
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual stopped graphical histories have exactly the native disjoint source labels. -/

import D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
import Mathlib.Data.List.Basic

/-! # Terminated native graphical histories -/

namespace D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories

open RepetitionVarianceLinear AncestralSources

variable {V Ω : Type} {G : SimpleGraph V}

/-- One actual backward step; stopping includes time zero and the first refresh. -/
def step (x : (c : Coord V) → Ω → Value G c) (ω : Ω) :
    ℕ × V → Option (ℕ × V)
  | (0, _) => none
  | (n+1, v) => if x (.refresh (n+1) v) ω then none
      else some (n, (x (.choice (n+1) v) ω).val)

/-- The finite list of actual absolute space-time vertices, including its terminal vertex. -/
def history (x : (c : Coord V) → Ω → Value G c) : ℕ → V → Ω → List (ℕ × V)
  | 0, v, _ => [(0, v)]
  | n+1, v, ω => if x (.refresh (n+1) v) ω then [(n+1, v)]
      else (n+1, v) :: history x n (x (.choice (n+1) v) ω).val ω

/-- The absolute space-time vertex encoded by an initial or a positive fresh label. -/
def labelVertex : Label V → ℕ × V
  | .inl v => (0, v)
  | .inr p => (p.1.val, p.2)

/-- Meeting means membership of one actual vertex at one actual absolute time. -/
def Meets (x : (c : Coord V) → Ω → Value G c) (ω : Ω) (n m : ℕ) (v w : V) : Prop :=
  ∃ p, p ∈ history x n v ω ∧ p ∈ history x m w ω

private theorem labelVertex_injective : Function.Injective (labelVertex (V := V)) := by
  intro a b h
  cases a with
  | inl v =>
    cases b with
    | inl w => simpa [labelVertex] using h
    | inr p =>
      have hzero : 0 = p.1.val := congrArg Prod.fst h
      exact False.elim ((Nat.ne_of_gt p.1.property) hzero.symm)
  | inr p =>
    cases b with
    | inl w =>
      have hzero : p.1.val = 0 := congrArg Prod.fst h
      exact False.elim ((Nat.ne_of_gt p.1.property) hzero)
    | inr q =>
      have ht : p.1 = q.1 := Subtype.ext (congrArg Prod.fst h)
      have hv : p.2 = q.2 := congrArg (fun z : ℕ × V => z.2) h
      exact congrArg Sum.inr (Prod.ext ht hv)

private theorem history_head (x : (c : Coord V) → Ω → Value G c) (n : ℕ) (v : V) (ω : Ω) :
    (history x n v ω)[0]? = some (n, v) := by
  cases n with
  | zero => rfl
  | succ n => simp only [history]; split <;> rfl

private theorem history_ne_nil (x : (c : Coord V) → Ω → Value G c) (n : ℕ) (v : V) (ω : Ω) :
    history x n v ω ≠ [] := by
  intro h
  have := history_head x n v ω
  simp [h] at this

/- The native extraction law identifies the entire remaining stopped list at every
actual offset. It is used by the source-invariance and common-suffix conclusions. -/
private theorem history_suffix (x : (c : Coord V) → Ω → Value G c) :
    ∀ n v ω i p, (history x n v ω)[i]? = some p →
      (history x n v ω).drop i = history x p.1 p.2 ω := by
  intro n
  induction n with
  | zero =>
    intro v ω i p hi
    cases i with
    | zero => simp only [history, List.getElem?_cons_zero, Option.some.injEq] at hi; subst p; rfl
    | succ i => simp [history] at hi
  | succ n ih =>
    intro v ω i p hi
    by_cases h : x (.refresh (n+1) v) ω = true
    · cases i with
      | zero => simp only [history, h, Bool.false_eq_true, ite_true, List.getElem?_cons_zero, Option.some.injEq] at hi
                subst p; rfl
      | succ i => simp [history, h] at hi
    · cases i with
      | zero => simp only [history, h, Bool.false_eq_true, ite_false, List.getElem?_cons_zero, Option.some.injEq] at hi
                subst p; rfl
      | succ i =>
        simp only [history, h, Bool.false_eq_true, ite_false, List.getElem?_cons_succ] at hi
        simpa only [history, h, Bool.false_eq_true, ite_false, List.drop_succ_cons] using ih _ ω i p hi

private theorem history_end (x : (c : Coord V) → Ω → Value G c) :
    ∀ n v ω, (history x n v ω).getLast? = some (labelVertex (source x n v ω)) ∧
      step x ω (labelVertex (source x n v ω)) = none := by
  intro n
  induction n with
  | zero => intros; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro v ω
    by_cases h : x (.refresh (n+1) v) ω = true
    · simp [history, source, labelVertex, step, h]
    · have ht := ih (x (.choice (n+1) v) ω).val ω
      simpa [history, source, h, List.getLast?_cons_of_ne_nil (history_ne_nil x n _ ω)] using ht

private theorem history_source (x : (c : Coord V) → Ω → Value G c)
    (n : ℕ) (v : V) (ω : Ω) (i : ℕ) (p : ℕ × V)
    (hi : (history x n v ω)[i]? = some p) : source x n v ω = source x p.1 p.2 ω := by
  have hs := history_suffix x n v ω i p hi
  have hlt : i < (history x n v ω).length := List.getElem?_eq_some_iff.mp hi |>.1
  have he := congrArg List.getLast? hs
  rw [List.getLast?_drop, if_neg (Nat.not_le_of_gt hlt),
    (history_end x n v ω).1, (history_end x p.1 p.2 ω).1] at he
  exact labelVertex_injective (Option.some.inj he)

private theorem history_edge (x : (c : Coord V) → Ω → Value G c)
    (n : ℕ) (v : V) (ω : Ω) (i : ℕ) (p q : ℕ × V)
    (hp : (history x n v ω)[i]? = some p)
    (hq : (history x n v ω)[i+1]? = some q) : step x ω p = some q := by
  have hs := history_suffix x n v ω i p hp
  have hq' : (history x p.1 p.2 ω)[1]? = some q := by
    rw [← hs, List.getElem?_drop]
    simpa using hq
  rcases p with ⟨k, a⟩
  cases k with
  | zero => simp [history] at hq'
  | succ k =>
    by_cases h : x (.refresh (k+1) a) ω = true
    · simp [history, h] at hq'
    · simp only [history, h, Bool.false_eq_true, ite_false, List.getElem?_cons_succ] at hq'
      rw [show (history x k (x (.choice (k+1) a) ω).val ω)[0]? =
        some (k, (x (.choice (k+1) a) ω).val) from history_head x k _ ω] at hq'
      simpa only [step, h, Bool.false_eq_true, ite_false] using hq'

/-- Complete native source correspondence, ordered common suffixes, and both directions
of coalescence, with arbitrary starting times and the terminal vertex included. -/
theorem terminated_history_source_correspondence
    (x : (c : Coord V) → Ω → Value G c) (ω : Ω) (n m : ℕ) (v w : V) :
    (history x n v ω)[0]? = some (n, v) ∧
    (∀ i p q, (history x n v ω)[i]? = some p →
      (history x n v ω)[i+1]? = some q → step x ω p = some q) ∧
    (history x n v ω).getLast? = some (labelVertex (source x n v ω)) ∧
    step x ω (labelVertex (source x n v ω)) = none ∧
    (∀ i j p, (history x n v ω)[i]? = some p → (history x m w ω)[j]? = some p →
      (history x n v ω).drop i = history x p.1 p.2 ω ∧
      (history x m w ω).drop j = history x p.1 p.2 ω) ∧
    (source x n v ω = source x m w ω ↔ Meets x ω n m v w) ∧
    (source x n v ω = source x m w ω →
      labelVertex (source x n v ω) ∈ history x n v ω ∧
      labelVertex (source x n v ω) ∈ history x m w ω ∧
      (history x n v ω).getLast? = (history x m w ω).getLast?) := by
  refine ⟨history_head x n v ω, history_edge x n v ω, (history_end x n v ω).1,
    (history_end x n v ω).2, ?_, ?_, ?_⟩
  · intro i j p hi hj
    exact ⟨history_suffix x n v ω i p hi, history_suffix x m w ω j p hj⟩
  · constructor
    · intro h
      refine ⟨labelVertex (source x n v ω), List.mem_of_getLast? (history_end x n v ω).1, ?_⟩
      rw [h]
      exact List.mem_of_getLast? (history_end x m w ω).1
    · rintro ⟨p, hp, hq⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
      exact (history_source x n v ω i p hi).trans (history_source x m w ω j p hj).symm
  · intro h
    refine ⟨List.mem_of_getLast? (history_end x n v ω).1, ?_, ?_⟩
    · rw [h]; exact List.mem_of_getLast? (history_end x m w ω).1
    · rw [(history_end x n v ω).1, (history_end x m w ω).1, h]

end D5.S3.StatisticalMechanics.NoisyVoter.TerminatedHistories
