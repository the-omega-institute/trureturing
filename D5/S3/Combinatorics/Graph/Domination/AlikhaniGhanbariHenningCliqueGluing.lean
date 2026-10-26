/- GID: D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Clique gluing satisfies the Alikhani-Ghanbari-Henning strong domination bound. -/

/-
admission_basis: open-problem-resolution (#19327; Proved)
escape_witness: none
Direct frozen dependencies: none for every declaration below.
proof_shape: IsStrongDominatingSet: bind-only; consumers: strongDominationNumber,
  claim, restriction_bound, strongDominationNumber_le, strongDominationNumber_attained.
proof_shape: strongDominationNumber: bind-only; consumers: claim,
  strongDominationNumber_le, strongDominationNumber_attained, result.
proof_shape: embedRight: bind-only; consumers: glue, embedRight_clique,
  embedRight_outside, embedRight_eq_inl, embedRight_injective, rightEmbedding.
proof_shape: glue: bind-only; consumers: claim, glue_adj, result.
proof_shape: X: bind-only; consumers: sigmaXY, restriction_bound, boundary_positive.
proof_shape: sigmaXY: bind-only; consumers: claim, result.
proof_shape: claim: bind-only; consumer: result.
proof_shape: embedRight_clique: bind-only; consumers: embedRight_eq_inl,
  embedRight_injective, result.
proof_shape: embedRight_outside: bind-only; consumers: embedRight_eq_inl,
  embedRight_injective, glue_adj_right_outside, result.
proof_shape: embedRight_eq_inl: bind-only; consumers: embedRight_injective,
  glue_adj_left_outside.
proof_shape: embedRight_injective: bind-only; consumers: rightEmbedding,
  glue_adj, glue_adj_right_outside.
proof_shape: rightEmbedding: bind-only; consumers: glue_degree_right_outside, result.
proof_shape: glue_adj: bind-only; consumers: glue_adj_left_outside, glue_adj_right_outside.
proof_shape: glue_adj_left_outside: bind-only; consumers: glue_degree_left_outside, result.
proof_shape: glue_adj_right_outside: bind-only; consumers: glue_degree_right_outside, result.
proof_shape: degree_eq_of_local_embedding: bind-only; consumers:
  glue_degree_left_outside, glue_degree_right_outside.
proof_shape: glue_degree_left_outside: bind-only; consumer: result.
proof_shape: glue_degree_right_outside: bind-only; consumer: result.
proof_shape: offSide: bind-only; consumers: mem_offSide, restriction_bound, result.
proof_shape: mem_offSide: bind-only; consumers: restriction_bound, result.
proof_shape: restriction_bound: content; consumer: result; constructs a repaired set.
proof_shape: strongDominationNumber_le: bind-only; consumer: result.
proof_shape: strongDominationNumber_attained: bind-only; consumer: result.
proof_shape: boundary_positive: bind-only; consumer: result; uses Walk.exists_boundary_dart.
proof_shape: result: content; repairs both restrictions and counts their sizes.
The labels on definitions describe encodings, not additional mathematical theorems.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19524.

The source is Alikhani, Ghanbari and Henning, Strong domination number of graphs
from primary subgraphs, Quaestiones Mathematicae 49(2), Problem 1, p. 202,
DOI 10.2989/16073606.2025.2574046. The claim retains the source hypotheses;
subtraction is in integers. The auxiliary vertex type is written directly as
V1 ⊕ {w : V2 // w ∉ Set.range B}, without a type alias.
The general sharpness family and bounds in finer parameters are not asserted.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Inv
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Binding conventions for S. Alikhani, N. Ghanbari and M. A. Henning, "Strong domination number of graphs from
primary subgraphs", Quaestiones Mathematicae 49(2) (2026) 195–211, DOI 10.2989/16073606.2025.2574046: strong
dominating sets, the strong domination number γst, the Kr-gluing G1 ∪Kr G2 identifying r-cliques A and B with
u_i identified with v_i, the sets X_i = N_{G1}(u_i) \ A and Y_i = N_{G2}(v_i) \ B, the sum Σ_{X,Y}, and
Inequality (4) of Problem 1. -/

namespace D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing

open Finset

/-- A set `D` is a strong dominating set of `G` if for every vertex `x ∈ V(G) \ D` there is a vertex `y ∈ D`
with `xy ∈ E(G)` and `deg(x) ≤ deg(y)`. -/
def IsStrongDominatingSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    Prop :=
  ∀ x, x ∉ D → ∃ y ∈ D, G.Adj x y ∧ G.degree x ≤ G.degree y

/-- The strong domination number `γst(G)`: the minimum cardinality of a strong dominating set of `G`. -/
noncomputable def strongDominationNumber {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ D : Finset V, IsStrongDominatingSet G D ∧ D.card = k}

/-- The image of a vertex of `G2` in `G1 ∪Kr G2`: `v_i` becomes `u_i`, every other vertex stays. -/
noncomputable def embedRight {r : ℕ} {V1 V2 : Type*} [DecidableEq V2] (A : Fin r ↪ V1) (B : Fin r ↪ V2) (w : V2) :
    (V1 ⊕ {w : V2 // w ∉ Set.range B}) :=
  if h : w ∈ Set.range B then .inl (A (B.invOfMemRange ⟨w, h⟩)) else .inr ⟨w, h⟩

/-- `G1 ∪Kr G2`: the union of `G1` and `G2` with the cliques `A` and `B` identified, `u_i` with `v_i`; the edges of
the identified clique appear once. -/
noncomputable def glue {r : ℕ} {V1 V2 : Type*} [DecidableEq V2] (G1 : SimpleGraph V1) (G2 : SimpleGraph V2)
    (A : Fin r ↪ V1) (B : Fin r ↪ V2) : SimpleGraph ((V1 ⊕ {w : V2 // w ∉ Set.range B})) :=
  SimpleGraph.fromRel fun p q =>
    (∃ a b, p = .inl a ∧ q = .inl b ∧ G1.Adj a b) ∨
      (∃ a b, p = embedRight A B a ∧ q = embedRight A B b ∧ G2.Adj a b)

/-- `X_i = N_{G1}(u_i) \ A`. -/
def X {r : ℕ} {V1 : Type*} [Fintype V1] [DecidableEq V1] (G1 : SimpleGraph V1) [DecidableRel G1.Adj]
    (A : Fin r ↪ V1) (i : Fin r) : Finset V1 :=
  G1.neighborFinset (A i) \ univ.map A

/-- `Σ_{X,Y} = Σ_{i=1}^r |X_i| + Σ_{i=1}^r |Y_i|`, with `Y_i = N_{G2}(v_i) \ B`. -/
def sigmaXY {r : ℕ} {V1 V2 : Type*} [Fintype V1] [DecidableEq V1] [Fintype V2] [DecidableEq V2]
    (G1 : SimpleGraph V1) [DecidableRel G1.Adj] (G2 : SimpleGraph V2) [DecidableRel G2.Adj]
    (A : Fin r ↪ V1) (B : Fin r ↪ V2) : ℕ :=
  ∑ i, (X G1 A i).card + ∑ i, (X G2 B i).card

open Classical in
/-- Problem 1, Inequality (4): for `r ≥ 2` and connected graphs `G1`, `G2` both of order at least `r + 1` that contain
`r`-cliques `A = {u_1, …, u_r}` and `B = {v_1, …, v_r}`, the `Kr`-gluing `G` identifying `u_i` with `v_i` satisfies
`γst(G) ≥ γst(G1) + γst(G2) − 1 − Σ_{X,Y}`. -/
def claim : Prop :=
  ∀ (r : ℕ), 2 ≤ r →
    ∀ (V1 V2 : Type) [Fintype V1] [DecidableEq V1] [Fintype V2] [DecidableEq V2]
      (G1 : SimpleGraph V1) (G2 : SimpleGraph V2) (A : Fin r ↪ V1) (B : Fin r ↪ V2),
      G1.Connected → G2.Connected → r + 1 ≤ Fintype.card V1 → r + 1 ≤ Fintype.card V2 →
      G1.IsClique (Set.range A) → G2.IsClique (Set.range B) →
      (strongDominationNumber G1 : ℤ) + strongDominationNumber G2 - 1 - sigmaXY G1 G2 A B ≤
        strongDominationNumber (glue G1 G2 A B)

end D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing

namespace D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing
open Finset

section Embeddings
variable {r : ℕ} {V1 V2 : Type*} [DecidableEq V2]
variable (A : Fin r ↪ V1) (B : Fin r ↪ V2)

private theorem embedRight_clique (i : Fin r) : embedRight A B (B i) = Sum.inl (A i) := by
  simp [embedRight, Function.Embedding.right_inv_of_invOfMemRange]

private theorem embedRight_outside (w : V2) (hw : w ∉ Set.range B) :
    embedRight A B w = Sum.inr ⟨w, hw⟩ := by
  simp [embedRight, hw]

private theorem embedRight_eq_inl (w : V2) (a : V1) :
    embedRight A B w = Sum.inl a ↔ ∃ i, w = B i ∧ a = A i := by
  constructor
  · intro h
    by_cases hw : w ∈ Set.range B
    · obtain ⟨i, rfl⟩ := hw
      rw [embedRight_clique] at h
      exact ⟨i, rfl, (Sum.inl.inj h).symm⟩
    · rw [embedRight_outside A B w hw] at h
      cases h
  · rintro ⟨i, rfl, rfl⟩
    exact embedRight_clique A B i

private theorem embedRight_injective : Function.Injective (embedRight A B) := by
  intro w z h
  by_cases hw : w ∈ Set.range B
  · obtain ⟨i, rfl⟩ := hw
    rw [embedRight_clique] at h
    obtain ⟨j, hz, hij⟩ := (embedRight_eq_inl A B z (A i)).mp h.symm
    have : i = j := A.injective hij
    simpa [this] using hz.symm
  · rw [embedRight_outside A B w hw] at h
    by_cases hz : z ∈ Set.range B
    · obtain ⟨i, rfl⟩ := hz
      rw [embedRight_clique] at h
      cases h
    · rw [embedRight_outside A B z hz] at h
      exact congrArg Subtype.val (Sum.inr.inj h)

private noncomputable def rightEmbedding : V2 ↪ (V1 ⊕ {w : V2 // w ∉ Set.range B}) :=
  ⟨embedRight A B, embedRight_injective A B⟩

private theorem glue_adj (G1 : SimpleGraph V1) (G2 : SimpleGraph V2)
    (p q : (V1 ⊕ {w : V2 // w ∉ Set.range B})) :
    (glue G1 G2 A B).Adj p q ↔
      (∃ a b, p = .inl a ∧ q = .inl b ∧ G1.Adj a b) ∨
      (∃ a b, p = embedRight A B a ∧ q = embedRight A B b ∧ G2.Adj a b) := by
  rw [glue, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hpq, h | h⟩
    · exact h
    · rcases h with ⟨a, b, hq, hp, hab⟩ | ⟨a, b, hq, hp, hab⟩
      · exact Or.inl ⟨b, a, hp, hq, hab.symm⟩
      · exact Or.inr ⟨b, a, hp, hq, hab.symm⟩
  · intro h
    refine ⟨?_, Or.inl h⟩
    rcases h with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩
    · exact fun h => hab.ne (Sum.inl.inj h)
    · exact fun h => hab.ne (embedRight_injective A B h)

private theorem glue_adj_left_outside (G1 : SimpleGraph V1) (G2 : SimpleGraph V2)
    (a : V1) (ha : a ∉ Set.range A) (p : (V1 ⊕ {w : V2 // w ∉ Set.range B})) :
    (glue G1 G2 A B).Adj (.inl a) p ↔ ∃ b, p = .inl b ∧ G1.Adj a b := by
  rw [glue_adj]
  constructor
  · rintro (⟨x, y, h, rfl, hxy⟩ | ⟨x, y, h, hp, hxy⟩)
    · cases Sum.inl.inj h
      exact ⟨y, rfl, hxy⟩
    · obtain ⟨i, hx, hi⟩ := (embedRight_eq_inl A B x a).mp h.symm
      exact (ha ⟨i, hi.symm⟩).elim
  · rintro ⟨b, rfl, hab⟩
    exact Or.inl ⟨a, b, rfl, rfl, hab⟩

private theorem glue_adj_right_outside (G1 : SimpleGraph V1) (G2 : SimpleGraph V2)
    (w : V2) (hw : w ∉ Set.range B) (p : (V1 ⊕ {w : V2 // w ∉ Set.range B})) :
    (glue G1 G2 A B).Adj (embedRight A B w) p ↔
      ∃ z, p = embedRight A B z ∧ G2.Adj w z := by
  rw [glue_adj]
  constructor
  · rintro (⟨x, y, h, hp, hxy⟩ | ⟨x, y, h, hp, hxy⟩)
    · rw [embedRight_outside A B w hw] at h
      cases h
    · have hx : w = x := embedRight_injective A B h
      subst x
      exact ⟨y, hp, hxy⟩
  · rintro ⟨z, rfl, hwz⟩
    exact Or.inr ⟨w, z, rfl, rfl, hwz⟩
end Embeddings

private theorem degree_eq_of_local_embedding {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : V ↪ W) (x : V)
    (h : ∀ p, H.Adj (f x) p ↔ ∃ y, p = f y ∧ G.Adj x y) :
    H.degree (f x) = G.degree x := by
  classical
  have he : H.neighborFinset (f x) = (G.neighborFinset x).map f := by
    ext p
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map]
    simpa only [and_comm, eq_comm] using h p
  rw [← SimpleGraph.card_neighborFinset_eq_degree, he, Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree]

section Degrees
variable {r : ℕ} {V1 V2 : Type*} [Fintype V1] [Fintype V2]
variable [DecidableEq V1] [DecidableEq V2]
variable (G1 : SimpleGraph V1) (G2 : SimpleGraph V2)
variable [DecidableRel G1.Adj] [DecidableRel G2.Adj]
variable (A : Fin r ↪ V1) (B : Fin r ↪ V2)

omit [DecidableEq V1] [DecidableRel G2.Adj] in
open Classical in
private theorem glue_degree_left_outside (a : V1) (ha : a ∉ Set.range A) :
    (glue G1 G2 A B).degree (.inl a) = G1.degree a := by
  exact degree_eq_of_local_embedding G1 (glue G1 G2 A B)
    ⟨Sum.inl, Sum.inl_injective⟩ a (glue_adj_left_outside A B G1 G2 a ha)

omit [DecidableEq V1] [DecidableRel G1.Adj] in
open Classical in
private theorem glue_degree_right_outside (w : V2) (hw : w ∉ Set.range B) :
    (glue G1 G2 A B).degree (embedRight A B w) = G2.degree w := by
  exact degree_eq_of_local_embedding G2 (glue G1 G2 A B)
    (rightEmbedding A B) w (glue_adj_right_outside A B G1 G2 w hw)
end Degrees
end D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing

namespace D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing
open Finset

private noncomputable def offSide {r : ℕ} {V W : Type*} [Fintype V]
    (D : Finset W) (A : Fin r ↪ V) (f : V ↪ W) : Finset V := by
  classical
  exact univ.filter (fun x => x ∉ Set.range A ∧ f x ∈ D)

private theorem mem_offSide {r : ℕ} {V W : Type*} [Fintype V]
    (D : Finset W) (A : Fin r ↪ V) (f : V ↪ W) (x : V) :
    x ∈ offSide D A f ↔ x ∉ Set.range A ∧ f x ∈ D := by
  classical
  simp only [offSide, mem_filter, mem_univ, true_and]

private theorem restriction_bound {r : ℕ} {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (A : Fin r ↪ V) (f : V ↪ W) (hr : 0 < r)
    (hClique : G.IsClique (Set.range A))
    (hlocal : ∀ x, x ∉ Set.range A → ∀ p,
      H.Adj (f x) p ↔ ∃ y, p = f y ∧ G.Adj x y)
    (hdeg : ∀ x, x ∉ Set.range A → H.degree (f x) = G.degree x)
    (D : Finset W) (hD : IsStrongDominatingSet H D)
    (hit : Prop) [Decidable hit] (hHit : ∀ i, f (A i) ∈ D → hit) :
    ∃ S : Finset V, IsStrongDominatingSet G S ∧
      S.card ≤ (offSide D A f).card + 1 + if hit then ∑ i, (X G A i).card else 0 := by
  classical
  obtain ⟨j, hj, hmax⟩ := (univ : Finset (Fin r)).exists_max_image
    (fun i => G.degree (A i)) ⟨⟨0, hr⟩, mem_univ _⟩
  let E : Finset V := univ.biUnion (X G A)
  let K : Finset V := if hit then E else ∅
  let S : Finset V := (offSide D A f ∪ {A j}) ∪ K
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    have hxparts : x ∉ offSide D A f ∧ x ≠ A j ∧ x ∉ K := by
      simpa only [S, mem_union, mem_singleton, not_or, and_assoc] using hx
    by_cases hxa : x ∈ Set.range A
    · obtain ⟨i, rfl⟩ := hxa
      refine ⟨A j, ?_, hClique (Set.mem_range_self i) (Set.mem_range_self j) hxparts.2.1,
        hmax i (mem_univ i)⟩
      simp [S]
    · have hfx : f x ∉ D := by
        intro h
        exact hxparts.1 ((mem_offSide D A f x).mpr ⟨hxa, h⟩)
      obtain ⟨w, hwD, hxw, hdegrees⟩ := hD (f x) hfx
      obtain ⟨y, rfl, hxy⟩ := (hlocal x hxa w).mp hxw
      have hya : y ∉ Set.range A := by
        rintro ⟨i, rfl⟩
        have hh : hit := hHit i hwD
        have hxE : x ∈ E := by
          apply mem_biUnion.mpr
          refine ⟨i, mem_univ i, ?_⟩
          simp only [X, mem_sdiff, SimpleGraph.mem_neighborFinset, mem_map,
            mem_univ, true_and]
          exact ⟨hxy.symm, fun ⟨i, hi⟩ => hxa ⟨i, hi⟩⟩
        exact hxparts.2.2 (by simpa [K, hh] using hxE)
      refine ⟨y, ?_, hxy, ?_⟩
      · have hy : y ∈ offSide D A f := (mem_offSide D A f y).mpr ⟨hya, hwD⟩
        exact mem_union_left _ (mem_union_left _ hy)
      · simpa only [hdeg x hxa, hdeg y hya] using hdegrees
  · have hc : S.card ≤ (offSide D A f).card + 1 + K.card := by
      calc
        S.card ≤ (offSide D A f ∪ {A j}).card + K.card := card_union_le _ _
        _ ≤ ((offSide D A f).card + ({A j} : Finset V).card) + K.card :=
          Nat.add_le_add_right (card_union_le _ _) _
        _ = (offSide D A f).card + 1 + K.card := by simp
    have hK : K.card ≤ if hit then ∑ i, (X G A i).card else 0 := by
      by_cases hh : hit
      · simp only [K, ite_eq_left hh]
        exact card_biUnion_le
      · simp [K, hh]
    exact hc.trans (Nat.add_le_add_left hK _)

private theorem strongDominationNumber_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (hD : IsStrongDominatingSet G D) : strongDominationNumber G ≤ D.card := by
  exact Nat.sInf_le (s := {k | ∃ E : Finset V, IsStrongDominatingSet G E ∧ E.card = k})
    ⟨D, hD, rfl⟩

private theorem strongDominationNumber_attained {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : Finset V, IsStrongDominatingSet G D ∧ D.card = strongDominationNumber G := by
  classical
  have hne : {k | ∃ D : Finset V, IsStrongDominatingSet G D ∧ D.card = k}.Nonempty :=
    ⟨Fintype.card V, univ, (fun x hx => (hx (mem_univ x)).elim), by simp⟩
  exact Nat.sInf_mem hne

private theorem boundary_positive {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Fin r ↪ V)
    (hr : 0 < r) (hconn : G.Connected) (horder : r + 1 ≤ Fintype.card V) :
    1 ≤ ∑ i, (X G A i).card := by
  classical
  have hout : ∃ v, v ∉ Set.range A := by
    by_contra! h
    have hsurj : Function.Surjective A := fun v => h v
    have hc := Fintype.card_le_of_surjective A hsurj
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨v, hv⟩ := hout
  let i : Fin r := ⟨0, hr⟩
  obtain ⟨p⟩ := hconn (A i) v
  have hedge : ∃ j x, x ∉ Set.range A ∧ G.Adj (A j) x := by
    obtain ⟨d, _, hdA, hdout⟩ := p.exists_boundary_dart (Set.range A)
      (Set.mem_range_self i) hv
    obtain ⟨j, hj⟩ := hdA
    exact ⟨j, d.snd, hdout, hj.symm ▸ d.adj⟩
  obtain ⟨j, x, hx, hjx⟩ := hedge
  have hmem : x ∈ X G A j := by
    simp only [X, mem_sdiff, SimpleGraph.mem_neighborFinset, mem_map, mem_univ,
      true_and]
    exact ⟨hjx, hx⟩
  have hp : 1 ≤ (X G A j).card := card_pos.mpr ⟨x, hmem⟩
  exact hp.trans (Finset.single_le_sum (fun i _ => Nat.zero_le ((X G A i).card)) (mem_univ j))

end D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing

namespace D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing
open Finset

theorem result : claim := by
  classical
  intro r hr V1 V2 _ _ _ _ G1 G2 A B hconn1 hconn2 horder1 horder2 hClique1 hClique2
  let H := glue G1 G2 A B
  obtain ⟨D, hD, hDcard⟩ := strongDominationNumber_attained H
  let f1 : V1 ↪ (V1 ⊕ {w : V2 // w ∉ Set.range B}) := ⟨Sum.inl, Sum.inl_injective⟩
  let f2 := rightEmbedding A B
  let hit : Prop := ∃ i, (Sum.inl (A i) : (V1 ⊕ {w : V2 // w ∉ Set.range B})) ∈ D
  have hrpos : 0 < r := lt_of_lt_of_le (Nat.zero_lt_succ 1) hr
  obtain ⟨S1, hS1, hc1⟩ := restriction_bound G1 H A f1 hrpos hClique1
    (fun x hx p => glue_adj_left_outside A B G1 G2 x hx p)
    (fun x hx => glue_degree_left_outside G1 G2 A B x hx)
    D hD hit (fun i hi => ⟨i, hi⟩)
  obtain ⟨S2, hS2, hc2⟩ := restriction_bound G2 H B f2 hrpos hClique2
    (fun x hx p => glue_adj_right_outside A B G1 G2 x hx p)
    (fun x hx => glue_degree_right_outside G1 G2 A B x hx)
    D hD hit (by
      intro i hi
      refine ⟨i, ?_⟩
      simpa only [f2, rightEmbedding, Function.Embedding.coeFn_mk, embedRight_clique] using hi)
  have hmin1 := strongDominationNumber_le G1 S1 hS1
  have hmin2 := strongDominationNumber_le G2 S2 hS2
  let C : Finset V1 := D.toLeft.filter (fun a => a ∈ Set.range A)
  have hleft : offSide D A f1 = D.toLeft.filter (fun a => a ∉ Set.range A) := by
    ext a
    simp only [mem_offSide, mem_filter, mem_toLeft]
    change (a ∉ Set.range A ∧ Sum.inl a ∈ D) ↔ (Sum.inl a ∈ D ∧ a ∉ Set.range A)
    exact and_comm
  have hright : (offSide D B f2).card = D.toRight.card := by
    apply Finset.card_bij (fun w hw => ⟨w, ((mem_offSide D B f2 w).mp hw).1⟩)
    · intro w hw
      have hm := ((mem_offSide D B f2 w).mp hw).2
      simpa only [f2, rightEmbedding, Function.Embedding.coeFn_mk,
        embedRight_outside A B w ((mem_offSide D B f2 w).mp hw).1, mem_toRight] using hm
    · intro a ha b hb hab
      exact congrArg Subtype.val hab
    · intro w hw
      refine ⟨w.val, ?_, ?_⟩
      · have hm : embedRight A B w.val ∈ D := by
          simpa only [embedRight_outside A B w.val w.property, mem_toRight] using hw
        exact (mem_offSide D B f2 w.val).mpr ⟨w.property, hm⟩
      · exact Subtype.ext rfl
  have hcount : (offSide D A f1).card + (offSide D B f2).card + C.card = D.card := by
    have hsplit := @Finset.card_filter_add_card_filter_not V1 D.toLeft
      (fun a => a ∈ Set.range A) _ _
    have hsum := Finset.card_toLeft_add_card_toRight (u := D)
    rw [hleft, hright]
    dsimp only [C]
    omega
  have hnat : strongDominationNumber G1 + strongDominationNumber G2 ≤
      strongDominationNumber H + 1 + sigmaXY G1 G2 A B := by
    by_cases hh : hit
    · have hC : 1 ≤ C.card := by
        obtain ⟨i, hi⟩ := hh
        apply card_pos.mpr
        refine ⟨A i, ?_⟩
        simp only [C, mem_filter, mem_toLeft]
        exact ⟨hi, Set.mem_range_self i⟩
      simp only [ite_eq_left hh] at hc1 hc2
      dsimp only [sigmaXY]
      omega
    · have hsig : 1 ≤ sigmaXY G1 G2 A B := by
        have hX := boundary_positive G1 A hrpos hconn1 horder1
        dsimp only [sigmaXY]
        omega
      simp only [ite_eq_right hh, Nat.add_zero] at hc1 hc2
      omega
  have hz : (strongDominationNumber G1 : ℤ) + strongDominationNumber G2 ≤
      (strongDominationNumber H : ℤ) + 1 + sigmaXY G1 G2 A B := by
    exact Nat.ToInt.of_le rfl rfl hnat
  dsimp only [H] at hz
  omega

end D5.S3.Combinatorics.Graph.Domination.AlikhaniGhanbariHenningCliqueGluing
