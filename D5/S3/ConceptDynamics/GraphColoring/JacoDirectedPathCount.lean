/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty, mathlib/module/Mathlib.Combinatorics.Quiver.Path.Vertices]
   utility: none
   digest: Directed Jaco paths retain their actual minimum-length cardinality in finite truncations. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-! Directed edge sequences, minimum edge lengths, and finite truncations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty

/-- Positive source labels, with precisely the original forward arcs. -/
@[instance_reducible] def directed : Quiver ℕ+ where
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
  by
    cases p with
    | nil => exact none
    | @cons c d q e => exact some ⟨⟨c, e.down.1⟩, q⟩

private theorem splitLast_injective (a b : ℕ+) :
    Function.Injective (@splitLast a b) := by
  intro p q h
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e => simp [splitLast] at h
  | @cons c b p e =>
      cases q with
      | nil => simp [splitLast] at h
      | @cons d b q f =>
          simp only [splitLast, Option.some.injEq] at h
          have hc : c = d := congrArg (fun s => s.fst.val) h
          subst d
          have hp : p = q := by cases h; rfl
          subst q
          congr
          exact Subsingleton.elim _ _

private theorem path_finite (a b : ℕ+) : Finite (Quiver.Path a b) := by
  induction b using (measure (fun b : ℕ+ => b.val)).wf.induction with
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
        exact ⟨p.cons (PLift.up ⟨by exact Nat.lt_succ_self n, consecutive_arc ⟨n, by omega⟩⟩)⟩

private theorem shortest_nonempty (n : ℕ+) : Nonempty (Shortest n) := by
  classical
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
  haveI : Finite (TruncatedPath n.val 1 n) := by unfold TruncatedPath; infer_instance
  haveI : Finite (Shortest n) := by unfold Shortest; infer_instance
  haveI := shortest_nonempty n
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · simpa only [psi, dif_pos n.property] using (Nat.card_pos (α := Shortest n))
  · intro r hr
    exact ⟨(truncationEquiv r 1 n hr).trans (truncationEquiv n.val 1 n le_rfl).symm,
      fun _ => rfl⟩

#print axioms path_count_foundations

private theorem endpoint_strict : StrictMono jacoRight :=
  strictMono_nat_of_lt_succ fun n => by
    have := jacoRight_succ_ge n
    omega

private theorem out_at_endpoint (m : ℕ) : beattyOut (jacoRight m) = m := by
  have hle : beattyOut (jacoRight m) ≤ m := by
    apply (beatty_threshold _ _).mp
    rw [← endpoint_eq_beatty]
  apply Nat.le_antisymm hle
  by_contra h
  have hlt : beattyOut (jacoRight m) < m := by omega
  have hreach : jacoRight m ≤ jacoRight (beattyOut (jacoRight m)) := by
    rw [endpoint_eq_beatty (beattyOut (jacoRight m))]
    exact (beatty_threshold _ _).mpr le_rfl
  exact (not_lt_of_ge hreach) (endpoint_strict hlt)

private theorem endpoint_fib (l : ℕ) :
    jacoRight (Nat.fib (l + 2)) = Nat.fib (l + 3) := by
  induction l with
  | zero => change jacoRight 1 = 2; decide +kernel
  | succ l ih =>
      have h := out_at_endpoint (Nat.fib (l + 2))
      rw [ih] at h
      rw [show l + 1 + 2 = l + 3 by omega, endpoint_eq_beatty, h]
      have hf := Nat.fib_add_two (l + 2)
      omega

private theorem reachable_prefix (l : ℕ) (n : ℕ+) :
    (∃ p : Quiver.Path (1 : ℕ+) n, p.length ≤ l) ↔ n.val ≤ Nat.fib (l + 2) := by
  induction l generalizing n with
  | zero =>
      constructor
      · rintro ⟨p, hp⟩
        have he := p.eq_of_length_zero (by omega)
        subst n
        decide
      · intro hn
        have hn1 : n = 1 := by
          apply Subtype.ext
          have hpos := n.property
          norm_num at hn ⊢
          omega
        subst n
        exact ⟨.nil, le_rfl⟩
  | succ l ih =>
      constructor
      · rintro ⟨p, hp⟩
        cases p with
        | nil =>
            exact Nat.fib_pos.mpr (by omega)
        | @cons c n p e =>
            have hlen : p.length ≤ l := by
              change p.length + 1 ≤ l + 1 at hp
              omega
            have hc := (ih c).mp ⟨p, hlen⟩
            calc
              n.val ≤ jacoRight c.val := e.down.2
              _ ≤ jacoRight (Nat.fib (l + 2)) := endpoint_strict.monotone hc
              _ = Nat.fib (l + 1 + 2) := by simpa [Nat.add_assoc] using endpoint_fib l
      · intro hn
        by_cases hold : n.val ≤ Nat.fib (l + 2)
        · obtain ⟨p, hp⟩ := (ih n).mpr hold
          exact ⟨p, by omega⟩
        · let M : ℕ+ := ⟨Nat.fib (l + 2), Nat.fib_pos.mpr (by omega)⟩
          obtain ⟨p, hp⟩ := (ih M).mpr le_rfl
          have e : M ⟶ n := PLift.up ⟨by dsimp [M]; omega, by
            change n.val ≤ jacoRight (Nat.fib (l + 2))
            rw [endpoint_fib]
            simpa [Nat.add_assoc] using hn⟩
          exact ⟨p.cons e, Nat.add_le_add_right hp 1⟩

/-- The vertices reachable in at most l directed edges are exactly the positive
prefix ending at F_(l+2), and this is the same threshold for every shortest path. -/
theorem fibonacci_distance (l : ℕ) (n : ℕ+) :
    ((∃ p : TruncatedPath n.val 1 n, p.val.length ≤ l) ↔
      n.val ≤ Nat.fib (l + 2)) ∧
    (∀ p : Shortest n, p.val.val.length ≤ l ↔ n.val ≤ Nat.fib (l + 2)) := by
  constructor
  · constructor
    · rintro ⟨p, hp⟩
      exact (reachable_prefix l n).mp ⟨p.val, hp⟩
    · intro hn
      obtain ⟨p, hp⟩ := (reachable_prefix l n).mpr hn
      exact ⟨truncate n.val le_rfl p, hp⟩
  · intro p
    constructor
    · intro hp
      exact (reachable_prefix l n).mp ⟨p.val.val, hp⟩
    · intro hn
      obtain ⟨q, hq⟩ := (reachable_prefix l n).mpr hn
      exact le_trans (p.property (truncate n.val le_rfl q)) hq

#print axioms fibonacci_distance

end D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount
