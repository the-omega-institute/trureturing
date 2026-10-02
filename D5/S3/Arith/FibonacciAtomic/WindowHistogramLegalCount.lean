/- GID: D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Neutral windows uniquely separate legal words into ordered low-end-high gaps. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.WindowHistogramLegalCount

open LiteralWindowEnd (Window bits first last flatten run endable nonzero execution)
open D5.S3.Arith.ZeckendorfFutureKernel (legal)
open scoped BigOperators

/-- The Boolean records which of the two actual neutral windows occurs. -/
def neutral (d : Bool) : Window := if d then .middle else .zero

/-- A gap contains no neutral input window. -/
def Free (g : List Window) : Prop := ∀ b ∈ g, b ≠ .zero ∧ b ≠ .middle

/-- The three exponents of a legal gap; the central exponent is zero or one. -/
structure Gap where
  x : ℕ
  z : Bool
  y : ℕ
  deriving DecidableEq

def gap (q : Gap) : List Window :=
  List.replicate q.x .low ++ (if q.z then [.ends] else []) ++
    List.replicate q.y .high

/-- The first gap, followed by each neutral letter and its following gap. -/
abbrev Cuts := List Window × List (Bool × List Window)

def join (p : Cuts) : List Window :=
  p.1 ++ p.2.flatMap (fun dg => neutral dg.1 :: dg.2)

def gaps (p : Cuts) : List (List Window) := p.1 :: p.2.map Prod.snd

def Clean (p : Cuts) : Prop := ∀ g ∈ gaps p, Free g

/-- Split at actual neutral input positions, retaining every empty gap. -/
def split : List Window → Cuts
  | [] => ([], [])
  | b :: w =>
      let p := split w
      match b with
      | .zero => ([], (false, p.1) :: p.2)
      | .middle => ([], (true, p.1) :: p.2)
      | b => (b :: p.1, p.2)

private theorem gap_language (w : List Window) (hw : Free w) :
    (legal false (flatten w) ↔ ∃ q : Gap, gap q = w) ∧
    (legal true (flatten w) ↔ ∃ n : ℕ, w = List.replicate n .high) := by
  have highs (n : ℕ) (s : Bool) : legal s (flatten (List.replicate n .high)) := by
    induction n generalizing s with
    | zero => simp [flatten, legal]
    | succ n ih => simpa [List.replicate_succ, flatten, bits, legal] using ih true
  have normal (q : Gap) : legal false (flatten (gap q)) := by
    rcases q with ⟨a, z, b⟩
    induction a with
    | zero =>
      cases z
      · simpa [gap] using highs b false
      · simpa [gap, flatten, bits, legal] using highs b true
    | succ a ih => simpa [gap, List.replicate_succ, flatten, bits, legal] using ih
  have forward : ∀ w : List Window, Free w →
      (legal false (flatten w) → ∃ q : Gap, gap q = w) ∧
      (legal true (flatten w) → ∃ n : ℕ, w = List.replicate n .high) := by
    intro v
    induction v with
    | nil => intro _; exact ⟨fun _ => ⟨⟨0, false, 0⟩, rfl⟩, fun _ => ⟨0, rfl⟩⟩
    | cons d v ih =>
      intro hv
      have ht : Free v := fun b hb => hv b (List.mem_cons_of_mem d hb)
      obtain ⟨ihf, iht⟩ := ih ht
      cases d with
      | zero => exact (hv .zero (by simp)).1 rfl |>.elim
      | middle => exact (hv .middle (by simp)).2 rfl |>.elim
      | low =>
        constructor
        · intro h
          obtain ⟨q, hq⟩ := ihf (by simpa [flatten, bits, legal] using h)
          exact ⟨⟨q.x + 1, q.z, q.y⟩,
            by simpa [gap, List.replicate_succ] using congrArg (List.cons .low) hq⟩
        · simp [flatten, bits, legal]
      | ends =>
        constructor
        · intro h
          obtain ⟨n, hn⟩ := iht (by simpa [flatten, bits, legal] using h)
          exact ⟨⟨0, true, n⟩, by simp [gap, hn]⟩
        · simp [flatten, bits, legal]
      | high =>
        constructor
        · intro h
          obtain ⟨n, hn⟩ := iht (by simpa [flatten, bits, legal] using h)
          exact ⟨⟨0, false, n + 1⟩, by simp [gap, List.replicate_succ, hn]⟩
        · intro h
          obtain ⟨n, hn⟩ := iht (by simpa [flatten, bits, legal] using h)
          exact ⟨n + 1, by simp [List.replicate_succ, hn]⟩
  exact ⟨⟨(forward w hw).1, fun ⟨q, hq⟩ => hq ▸ normal q⟩,
    ⟨(forward w hw).2, fun ⟨n, hn⟩ => hn ▸ highs n true⟩⟩

private theorem split_properties (w : List Window) :
    join (split w) = w ∧ Clean (split w) ∧
    (split w).2.length = w.count .zero + w.count .middle ∧
    (∀ s : Bool, legal s (flatten w) ↔
      legal s (flatten (split w).1) ∧
        ∀ dg ∈ (split w).2, legal false (flatten dg.2)) := by
  induction w with
  | nil => simp [split, join, Clean, gaps, Free, flatten, legal]
  | cons d w ih =>
    obtain ⟨he, hc, hn, hl⟩ := ih
    rcases hp : split w with ⟨g, ds⟩
    simp only [hp, join, Clean, gaps, List.mem_cons, List.mem_map,
      forall_eq_or_imp, Prod.forall, exists_and_right, exists_eq_right] at he hc hn hl
    cases d <;>
      simp_all [split, join, Clean, gaps, Free, neutral, flatten, bits, legal,
        List.count_cons, List.mem_map, List.flatMap_cons, List.cons_append]
    all_goals first | exact hc.2 | exact ⟨hc.2, by omega⟩

private theorem split_inverse (p : Cuts) (hp : Clean p) : split (join p) = p := by
  have split_prefix (g : List Window) (hg : Free g) (w : List Window) :
      split (g ++ w) = (g ++ (split w).1, (split w).2) := by
    induction g with
    | nil => simp
    | cons d g ih =>
      have hd := hg d (by simp)
      have ht : Free g := fun b hb => hg b (List.mem_cons_of_mem d hb)
      cases d <;> simp_all [split, List.cons_append]
  rcases p with ⟨g, ds⟩
  simp only [Clean, gaps, List.mem_cons, forall_eq_or_imp] at hp
  rw [join, split_prefix g hp.1]
  induction ds with
  | nil => simp [split]
  | cons dg ds ih =>
    rcases dg with ⟨d, h⟩
    have hh : Free h := hp.2 h (by simp)
    have ht : ∀ v ∈ ds.map Prod.snd, Free v := by
      intro v hv
      exact hp.2 v (by simp [hv])
    have hi := ih ⟨hp.1, ht⟩
    cases d <;> simp_all [List.flatMap_cons, neutral, split, split_prefix h hh]

/-- Neutral positions determine a unique decomposition, and each legal gap
has unique low/end/high exponents. -/
theorem result :
    (∀ w : List Window, ∃! p : Cuts, Clean p ∧ join p = w) ∧
    (∀ w : List Window, (split w).2.length = w.count .zero + w.count .middle) ∧
    (∀ w : List Window, legal false (flatten w) ↔
      ∀ g ∈ gaps (split w), ∃! q : Gap, gap q = g) := by
  have injective : Function.Injective gap := by
    intro p q h
    have hx : (gap p).count .low = (gap q).count .low := congrArg (List.count .low) h
    have hy : (gap p).count .high = (gap q).count .high := congrArg (List.count .high) h
    have hz : (gap p).count .ends = (gap q).count .ends := congrArg (List.count .ends) h
    rcases p with ⟨a, z, b⟩
    rcases q with ⟨a', z', b'⟩
    cases z <;> cases z' <;>
      simp [gap, List.count_replicate] at hx hy hz <;> simp_all
  refine ⟨?_, ?_, ?_⟩
  · intro w
    refine ⟨split w, ⟨(split_properties w).2.1, (split_properties w).1⟩, ?_⟩
    intro p hp
    rw [← split_inverse p hp.1, hp.2]
  · intro w
    exact (split_properties w).2.2.1
  · intro w
    rw [(split_properties w).2.2.2 false]
    have characterize (g : List Window) (hg : Free g) :
        legal false (flatten g) ↔ ∃! q : Gap, gap q = g := by
      rw [(gap_language g hg).1]
      exact ⟨fun ⟨q, hq⟩ => ⟨q, hq, fun p hp => injective (hp.trans hq.symm)⟩,
        fun ⟨q, hq, _⟩ => ⟨q, hq⟩⟩
    have hc := (split_properties w).2.1
    unfold Clean at hc
    constructor
    · rintro ⟨hg, ht⟩ g h
      apply (characterize g (hc g h)).mp
      rcases List.mem_cons.mp h with he | h
      · simpa [he] using hg
      · obtain ⟨dg, hdg, rfl⟩ := List.mem_map.mp h
        exact ht dg hdg
    · intro h
      refine ⟨(characterize _ (hc _ (by simp [gaps]))).mpr (h _ (by simp [gaps])), ?_⟩
      intro dg hdg
      have hg : dg.2 ∈ gaps (split w) :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨dg, hdg, rfl⟩)
      exact (characterize dg.2 (hc _ hg)).mpr (h _ hg)

#print axioms result

end D5.S3.Arith.FibonacciAtomic.WindowHistogramLegalCount
