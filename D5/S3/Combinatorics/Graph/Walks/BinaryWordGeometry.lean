/- GID: D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/BinaryWordGeometry
   mirror-E: none(waiver:no-computational-evidence)
   anchors: [mathlib/module/Mathlib.Data.List.Infix]
   utility: none
   digest: Binary-word edits attain common-prefix distance within endpoint heights. -/

import Mathlib.Data.List.Infix
import Mathlib.Tactic

/-!
The longest-common-prefix definition and its prefix proofs are adapted from
vltanh/lean4-camus, revision f6edae966a69a4153f41ee94f679e16c87d798b4,
Camus/Defs.lean and Camus/Tree/Geometry.lean (Apache-2.0).
The complete supplier license is docs/reports/third-party/lean4-camus-LICENSE.txt.
Retire this supplier slice when the pinned mathlib provides equivalent binary-list
longest-common-prefix declarations, replacing its uses by those declarations.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry

abbrev Word := List Bool

/-- The actual longest common initial word. -/
def lcp : Word → Word → Word
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, b :: q => if a = b then a :: lcp p q else []

private theorem lcp_prefix_left (p q : Word) : lcp p q <+: p := by
  induction p generalizing q with
  | nil => simp [lcp]
  | cons a p ih =>
    cases q with
    | nil => simp [lcp]
    | cons b q =>
      by_cases h : a = b
      · simp [lcp, h, ih]
      · simp [lcp, h]

private theorem lcp_prefix_right (p q : Word) : lcp p q <+: q := by
  induction p generalizing q with
  | nil => simp [lcp]
  | cons a p ih =>
    cases q with
    | nil => simp [lcp]
    | cons b q =>
      by_cases h : a = b
      · subst b; simp [lcp, ih]
      · simp [lcp, h]

private theorem prefix_lcp {x p q : Word} (hp : x <+: p) (hq : x <+: q) :
    x <+: lcp p q := by
  induction x generalizing p q with
  | nil => simp
  | cons a x ih =>
    cases p with
    | nil => have := hp.length_le; simp at this
    | cons b p =>
      cases q with
      | nil => have := hq.length_le; simp at this
      | cons c q =>
        obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
        obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.mp hq
        simp [lcp, ih hp' hq']

/-- Unit edits are precisely right-end APPEND and its inverse POP. -/
inductive Step : Word → Word → Prop
  | append (w : Word) (b : Bool) : Step w (w ++ [b])
  | pop (w : Word) (b : Bool) : Step (w ++ [b]) w

/-- An actual finite edit sequence; its length counts every charged edit. -/
inductive Path : Word → Word → Type
  | nil (w : Word) : Path w w
  | cons {u v w : Word} (step : Step u v) (tail : Path v w) : Path u w

/-- Exact charged edit count of the actual sequence. -/
def Path.length {u v : Word} : Path u v → ℕ
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- The height restriction charges every intermediate word, including endpoints. -/
def Path.Within {u v : Word} : Path u v → ℕ → Prop
  | .nil w, L => w.length ≤ L
  | @Path.cons u _ _ _ tail, L => u.length ≤ L ∧ tail.Within L

/-- The tree distance, expressed with ordinary natural subtraction. -/
def distance (u v : Word) : ℕ := u.length + v.length - 2 * (lcp u v).length

private theorem distance_nil_left (v : Word) : distance [] v = v.length := by
  simp [distance, lcp]

private theorem distance_nil_right (u : Word) : distance u [] = u.length := by
  cases u <;> simp [distance, lcp]

private theorem distance_cons (a b : Bool) (u v : Word) :
    distance (a :: u) (b :: v) =
      if a = b then distance u v else (a :: u).length + (b :: v).length := by
  have h₁ := (lcp_prefix_left u v).length_le
  have h₂ := (lcp_prefix_right u v).length_le
  by_cases h : a = b <;> simp [distance, lcp, h] <;> omega

private theorem append_lipschitz (u v : Word) (b : Bool) :
    distance u (v ++ [b]) ≤ distance u v + 1 ∧
      distance u v ≤ distance u (v ++ [b]) + 1 := by
  induction u generalizing v with
  | nil => simp [distance_nil_left]; omega
  | cons a u ih =>
    cases v with
    | nil =>
      simp only [List.nil_append, distance_nil_right, distance_cons]
      split_ifs <;> simp [distance_nil_right] <;> omega
    | cons c v =>
      simp only [List.cons_append, distance_cons]
      by_cases h : a = c
      · simpa [h] using ih v
      · simp [h]; omega

private theorem distance_self (u : Word) : distance u u = 0 := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa [distance_cons] using ih

private theorem distance_symm (u v : Word) : distance u v = distance v u := by
  induction u generalizing v with
  | nil => simp [distance_nil_left, distance_nil_right]
  | cons a u ih =>
    cases v with
    | nil => simp [distance_nil_left, distance_nil_right]
    | cons b v =>
      simp only [distance_cons]
      by_cases h : a = b
      · simp [h, ih]
      · simp [h, Ne.symm h, Nat.add_comm]

/-- Every actual update sequence costs at least the endpoint tree distance. -/
private theorem path_lower_bound {u v : Word} (p : Path u v) :
    distance u v ≤ p.length := by
  induction p with
  | nil w => simp [distance_self, Path.length]
  | @cons u z v step tail ih =>
    have h : distance u v ≤ distance z v + 1 := by
      cases step with
      | append base bit =>
        rw [distance_symm u v, distance_symm (u ++ [bit]) v]
        exact (append_lipschitz v u bit).2
      | pop base bit =>
        rw [distance_symm (z ++ [bit]) v, distance_symm z v]
        exact (append_lipschitz v z bit).1
    simp only [Path.length]
    omega

private def Path.join {u v w : Word} (p : Path u v) (q : Path v w) : Path u w :=
  match p with
  | .nil _ => q
  | .cons step tail => .cons step (tail.join q)

private theorem Path.join_length {u v w : Word} (p : Path u v) (q : Path v w) :
    (p.join q).length = p.length + q.length := by
  induction p with
  | nil => simp [Path.join, Path.length]
  | cons step tail ih => simp [Path.join, Path.length, ih, Nat.add_right_comm]

private theorem Path.within_mono {u v : Word} {L M : ℕ} (p : Path u v)
    (h : p.Within L) (hLM : L ≤ M) : p.Within M := by
  induction p with
  | nil => exact h.trans hLM
  | cons step tail ih => exact ⟨h.1.trans hLM, ih h.2⟩

private theorem Path.join_within {u v w : Word} {L : ℕ} (p : Path u v)
    (q : Path v w) (hp : p.Within L) (hq : q.Within L) :
    (p.join q).Within L := by
  induction p with
  | nil => exact hq
  | cons step tail ih => exact ⟨hp.1, ih q hp.2 hq⟩

private theorem Path.start_within {u v : Word} {L : ℕ} (p : Path u v)
    (hp : p.Within L) : u.length ≤ L := by
  cases p with
  | nil => exact hp
  | cons => exact hp.1

private theorem Step.reverse {u v : Word} (s : Step u v) : Step v u := by
  cases s with
  | append base bit => exact .pop _ bit
  | pop base bit => exact .append _ bit

private def Path.reverse {u v : Word} (p : Path u v) : Path v u :=
  match p with
  | .nil w => .nil w
  | @Path.cons u _ _ step tail => tail.reverse.join (.cons step.reverse (.nil u))

private theorem Path.reverse_length {u v : Word} (p : Path u v) :
    p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons step tail ih => simp [Path.reverse, Path.join_length, Path.length, ih]

private theorem Path.reverse_within {u v : Word} {L : ℕ} (p : Path u v)
    (hp : p.Within L) : p.reverse.Within L := by
  induction p with
  | nil => exact hp
  | @cons u v w step tail ih =>
    exact Path.join_within _ _ (ih hp.2) ⟨Path.start_within tail hp.2, hp.1⟩

private theorem append_path (w s : Word) :
    ∃ p : Path w (w ++ s), p.length = s.length ∧ p.Within (w.length + s.length) := by
  induction s generalizing w with
  | nil =>
    rw [List.append_nil]
    simp only [List.length_nil, Nat.add_zero]
    exact ⟨.nil w, rfl, Nat.le_refl _⟩
  | cons b s ih =>
    obtain ⟨p, hlen, hp⟩ := ih (w ++ [b])
    have result : ∃ q : Path w ((w ++ [b]) ++ s),
        q.length = (b :: s).length ∧ q.Within (w.length + (b :: s).length) := by
      refine ⟨Path.cons (.append w b) p, ?_, ?_⟩
      · simpa [Path.length] using hlen
      · constructor
        · simp
        · simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    rw [List.append_assoc, List.singleton_append] at result
    exact result

/-- The longest common prefix is certified from the words themselves. Every actual
POP/APPEND path has at least the displayed distance, and an actual attaining path
keeps every intermediate word within the larger endpoint length. -/
theorem shortest_pop_append (u v : Word) :
    (lcp u v <+: u ∧ lcp u v <+: v ∧
      ∀ w : Word, w <+: u → w <+: v → w <+: lcp u v) ∧
    (∀ p : Path u v, distance u v ≤ p.length) ∧
    ∃ p : Path u v, p.length = distance u v ∧ p.Within (max u.length v.length) := by
  refine ⟨⟨lcp_prefix_left u v, lcp_prefix_right u v,
    fun _ hp hq => prefix_lcp hp hq⟩, fun p => path_lower_bound p, ?_⟩
  obtain ⟨s, hs⟩ := lcp_prefix_left u v
  obtain ⟨t, ht⟩ := lcp_prefix_right u v
  obtain ⟨p, hplen, hp⟩ := append_path (lcp u v) s
  obtain ⟨q, hqlen, hq⟩ := append_path (lcp u v) t
  have hu : (lcp u v).length + s.length = u.length := by rw [← List.length_append, hs]
  have hv : (lcp u v).length + t.length = v.length := by rw [← List.length_append, ht]
  have hd : s.length + t.length = distance u v := by unfold distance; omega
  have hp' : p.Within (max u.length v.length) := p.within_mono hp (by omega)
  have hq' : q.Within (max u.length v.length) := q.within_mono hq (by omega)
  have result : ∃ r : Path ((lcp u v) ++ s) ((lcp u v) ++ t),
      r.length = distance u v ∧ r.Within (max u.length v.length) := by
    refine ⟨p.reverse.join q, ?_, p.reverse.join_within q (p.reverse_within hp') hq'⟩
    rw [Path.join_length, Path.reverse_length, hplen, hqlen, hd]
  rw [hs, ht] at result
  exact result

#print axioms shortest_pop_append

end D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
