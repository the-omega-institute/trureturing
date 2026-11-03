/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty, mathlib/module/Mathlib.Combinatorics.Quiver.Path.Vertices]
   utility: none
   digest: Directed Jaco paths retain their actual minimum-length cardinality in finite truncations. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.Fintype.List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty

/-- Positive source labels, with precisely the original forward arcs. -/
def directed : Quiver ℕ+ where
  Hom a b := PLift (a.val < b.val ∧ b.val ≤ jacoRight a.val)

attribute [local instance] directed

private instance (a b : ℕ+) : Subsingleton (a ⟶ b) := inferInstanceAs (Subsingleton (PLift _))

/-- A path in the induced truncation, retaining the original edge sequence. -/
def TruncatedPath (r : ℕ) (a b : ℕ+) :=
  {p : Quiver.Path a b // ∀ v ∈ p.vertices, v.val ≤ r}

/-- Actual shortest directed paths in the target vertex's own truncation. -/
def Shortest (n : ℕ+) :=
  {p : TruncatedPath n.val 1 n // ∀ q : TruncatedPath n.val 1 n,
    p.val.length ≤ q.val.length}

/-- Cardinality of actual minimum-edge-length paths; index zero is unused. -/
noncomputable def psi (n : ℕ) : ℕ :=
  if hn : 0 < n then Nat.card (Shortest ⟨n, hn⟩) else 0

/-- Infinite outdegree, rather than an outdegree truncated at the target. -/
def outdegree (n : ℕ) : ℕ := jacoRight n - n

/-- The complete original directed Proposition 4.4, with both adjacent comparisons. -/
def claim : Prop :=
  ∀ k : ℕ, 7 ≤ k → ∀ i : ℕ, Nat.fib i < k → k ≤ Nat.fib (i + 1) →
    ((outdegree (k - 1) ≠ outdegree k ∧ outdegree k ≠ outdegree (k + 1)) ↔
      (psi (k - 1) ≠ psi k ∧ psi k ≠ psi (k + 1)))

private theorem vertices_bounds {a b : ℕ+} (p : Quiver.Path a b) :
    ∀ v ∈ p.vertices, a.val ≤ v.val ∧ v.val ≤ b.val := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
      intro v hv
      rcases (Quiver.Path.mem_vertices_cons p e).mp hv with hv | rfl
      · exact ⟨(ih v hv).1, le_trans (ih v hv).2 (Nat.le_of_lt e.down.1)⟩
      · exact ⟨le_trans (ih a p.start_mem_vertices).1
          (le_trans (ih a p.start_mem_vertices).2 (Nat.le_of_lt e.down.1)), le_rfl⟩

private def splitLast {a b : ℕ+} (p : Quiver.Path a b) :
    Option (Σ c : {c : ℕ+ // c.val < b.val}, Quiver.Path a c.val) :=
  match p with
  | .nil => none
  | @Quiver.Path.cons _ _ _ c _ q e => some ⟨⟨c, e.down.1⟩, q⟩

private theorem splitLast_injective (a b : ℕ+) :
    Function.Injective (@splitLast a b) := by
  intro p q h
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e => simp [splitLast] at h
  | @cons c p e =>
      cases q with
      | nil => simp [splitLast] at h
      | @cons d q f =>
          simp only [splitLast, Option.some.injEq] at h
          have hc : c = d := congrArg (fun s => s.fst.val) h
          subst d
          have hp : p = q := by cases h; rfl
          subst q
          congr
          exact Subsingleton.elim _ _

private theorem path_finite (a b : ℕ+) : Finite (Quiver.Path a b) := by
  induction b using (measure (fun b : ℕ+ => b.val)).induction with
  | h b ih =>
      letI : Finite {c : ℕ+ // c.val < b.val} :=
        Finite.of_injective (fun c => (⟨c.val.val, c.property⟩ : Fin b.val)) (by
          intro c d h
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg Fin.val h)
      letI (c : {c : ℕ+ // c.val < b.val}) : Finite (Quiver.Path a c.val) :=
        ih c.val c.property
      exact Finite.of_injective splitLast (splitLast_injective a b)

private def truncate {a b : ℕ+} (r : ℕ) (hb : b.val ≤ r)
    (p : Quiver.Path a b) : TruncatedPath r a b :=
  ⟨p, fun v hv => le_trans (vertices_bounds p v hv).2 hb⟩

private def truncationEquiv (r : ℕ) (a b : ℕ+) (hb : b.val ≤ r) :
    TruncatedPath r a b ≃ Quiver.Path a b where
  toFun := Subtype.val
  invFun := truncate r hb
  left_inv p := Subtype.ext rfl
  right_inv _ := rfl

private theorem consecutive_arc (n : ℕ+) :
    n.val + 1 ≤ jacoRight n.val := by
  rw [endpoint_eq_beatty]
  have := (beatty_bounds n.val n.property).1
  omega

private theorem path_nonempty (n : ℕ+) : Nonempty (Quiver.Path (1 : ℕ+) n) := by
  obtain ⟨n, hn⟩ := n
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hz : n = 0
      · subst n
        exact ⟨.nil⟩
      · obtain ⟨p⟩ := ih (by omega)
        exact ⟨p.cons (PLift.up ⟨by simp; omega, consecutive_arc ⟨n, by omega⟩⟩)⟩

private theorem shortest_nonempty (n : ℕ+) : Nonempty (Shortest n) := by
  obtain ⟨p⟩ := path_nonempty n
  let P : ℕ → Prop := fun l => ∃ p : TruncatedPath n.val 1 n, p.val.length = l
  have hex : ∃ l, P l := ⟨p.length, truncate n.val le_rfl p, rfl⟩
  obtain ⟨q, hq⟩ := Nat.find_spec hex
  refine ⟨⟨q, ?_⟩⟩
  intro r
  have hr := Nat.find_min' hex (show P r.val.length from ⟨r, rfl⟩)
  omega

/-- Every own-truncation shortest-path set is finite and nonempty; later
truncations preserve the full directed path set, including each edge length. -/
theorem path_count_foundations (n : ℕ+) :
    Finite (Shortest n) ∧ Nonempty (Shortest n) ∧ 0 < psi n.val ∧
    (∀ r : ℕ, n.val ≤ r → ∃ e : TruncatedPath r 1 n ≃ TruncatedPath n.val 1 n,
      ∀ p, (e p).val.length = p.val.length) := by
  letI := path_finite (1 : ℕ+) n
  haveI : Finite (TruncatedPath n.val 1 n) := inferInstance
  haveI : Finite (Shortest n) := inferInstance
  haveI := shortest_nonempty n
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · simpa [psi, n.property] using Nat.card_pos (α := Shortest n)
  · intro r hr
    exact ⟨(truncationEquiv r 1 n hr).trans (truncationEquiv n.val 1 n le_rfl).symm,
      fun _ => rfl⟩

#print axioms path_count_foundations

end D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount
