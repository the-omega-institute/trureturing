/- GID: D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/LeafSupportJoin
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Joining leaf supports splits dominating sets by copy; domination polynomials multiply. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#203)
escape_witness: dominating_iff (a set dominates the join exactly when each slice dominates its
  copy, the support being dominated inside its copy through the leaf), with domEquiv.
proof_shape:
  domPoly, joinAdj, join, slice: definitions; consumers: the lemmas below.
  dominating_iff: content; consumers: domEquiv, leaf_support_join.
  domEquiv: content; consumers: domEquiv_card, domPoly_join, leaf_support_join.
  domPoly_join: content; consumer: leaf_support_join.
  join_connected: bind-only helper (Reachable.map along two graph homomorphisms); consumer:
    leaf_support_join.
  join_adj_same: bind-only helper; consumers: dominating_iff, join_connected.
  mem_slice: bind-only helper; consumers: dominating_iff, domEquiv, domEquiv_card.
  domEquiv_card: bind-only helper; consumers: domPoly_join, leaf_support_join.
  leaf_support_join: content.
Direct frozen dependencies: D5/S3/Combinatorics/Graph/DominatingSetAverage (domSets,
  mem_domSets), D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination (IsDominating).
Search record (§3.1): MinusFourReassembly.reassembly with k = 0 gives the pointwise integer
  evaluation of the product for Fin-labelled decompositions, root–root edges allowed; its
  bijection configEquiv and dominating_assemble_iff are private and pass through root-state
  messages. Reusing them would need a Σ→Fin relabelling, the Decomposition laws and polynomial
  extensionality, and still not give the explicit restriction/union bijection or the ℤ[x]
  identity, so the direct Σ-type proof is kept. MinusFourReassembly's private
  support_replication_* treat copies joined to a new hub, and
  RatherBookRootRefutation.dominationPolynomial is real-valued, so domPoly is the integer
  polynomial here.
-/

import D5.S3.Combinatorics.Graph.DominatingSetAverage
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.BigOperators

/-! # Leaf-support joining and the domination polynomial product

Let `H_i` be finite simple graphs with vertices `v_i, w_i` such that the only neighbour of `w_i`
is `v_i`. For a simple graph `F` on the copy indices, `J_F` is the disjoint union of the `H_i`
with the extra edges `v_i v_j` for `ij ∈ E(F)`. A set of vertices dominates `J_F` exactly when
each of its slices dominates the corresponding `H_i`: the new edges only touch the supports
`v_i`, and `v_i` is already dominated inside its copy by the leaf condition at `w_i`. Restriction
and disjoint union are inverse size-preserving bijections, so `D(J_F, x) = ∏ D(H_i, x)`, and
`J_F` is connected when every `H_i` and `F` is connected and there is at least one copy.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.LeafSupportJoin

open Finset Polynomial
open D5.S3.Combinatorics.Graph.DominatingSetAverage

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-- The domination polynomial `D(G, x) = ∑_S x^{|S|}` over the dominating sets of `G`. -/
def domPoly {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) : ℤ[X] :=
  ∑ S ∈ domSets G, (X : ℤ[X]) ^ S.card

/-- The adjacency of the join: edges of each copy, and `v_i v_j` for `ij ∈ E(F)`. -/
def joinAdj (H : ∀ i, SimpleGraph (V i)) (v : ∀ i, V i) (F : SimpleGraph ι)
    (a b : Σ i, V i) : Prop :=
  (∃ h : a.1 = b.1, (H b.1).Adj (h ▸ a.2) b.2) ∨ (F.Adj a.1 b.1 ∧ a.2 = v a.1 ∧ b.2 = v b.1)

/-- The leaf-support join `J_F`. -/
def join (H : ∀ i, SimpleGraph (V i)) (v : ∀ i, V i) (F : SimpleGraph ι) :
    SimpleGraph (Σ i, V i) where
  Adj := joinAdj H v F
  symm := ⟨by
    rintro ⟨i, x⟩ ⟨j, y⟩ (⟨h, hxy⟩ | ⟨hF, hx, hy⟩)
    · simp only at h
      subst h
      exact Or.inl ⟨rfl, hxy.symm⟩
    · exact Or.inr ⟨hF.symm, hy, hx⟩⟩
  loopless := ⟨by
    rintro ⟨i, x⟩ (⟨h, hxx⟩ | ⟨hF, -, -⟩)
    · exact (H i).irrefl hxx
    · exact F.irrefl hF⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
lemma join_adj_same (H : ∀ i, SimpleGraph (V i)) (v : ∀ i, V i) (F : SimpleGraph ι) (i : ι)
    (x y : V i) : (join H v F).Adj ⟨i, x⟩ ⟨i, y⟩ ↔ (H i).Adj x y := by
  constructor
  · rintro (⟨_, h⟩ | ⟨hF, -, -⟩)
    · exact h
    · exact absurd hF F.irrefl
  · exact fun h => Or.inl ⟨rfl, h⟩

/-- The slice of a vertex set in copy `i`. -/
def slice (S : Finset (Σ i, V i)) (i : ι) : Finset (V i) :=
  univ.filter fun x => (⟨i, x⟩ : Σ i, V i) ∈ S

omit [Fintype ι] in
@[simp] lemma mem_slice (S : Finset (Σ i, V i)) (i : ι) (x : V i) :
    x ∈ slice S i ↔ (⟨i, x⟩ : Σ i, V i) ∈ S := by
  simp [slice]

/-- A set dominates the join exactly when each slice dominates its copy. -/
lemma dominating_iff (H : ∀ i, SimpleGraph (V i)) (v w : ∀ i, V i)
    (hw : ∀ i (u : V i), (H i).Adj (w i) u ↔ u = v i) (F : SimpleGraph ι)
    (S : Finset (Σ i, V i)) :
    S ∈ domSets (join H v F) ↔ ∀ i, slice S i ∈ domSets (H i) := by
  simp only [mem_domSets]
  constructor
  · intro hS i x
    have hwv : (H i).Adj (w i) (v i) := (hw i (v i)).mpr rfl
    -- the support is dominated inside its copy, through the leaf `w i`
    have hsupp : v i ∈ (slice S i : Set (V i)) ∨
        ∃ y ∈ (slice S i : Set (V i)), (H i).Adj (v i) y := by
      rcases hS ⟨i, w i⟩ with h | ⟨⟨j, y⟩, hy, hadj⟩
      · exact Or.inr ⟨w i, by simpa using h, hwv.symm⟩
      · rcases hadj with ⟨h, hadj⟩ | ⟨-, hwv', -⟩
        · simp only at h
          subst h
          have hyv : y = v i := (hw i y).mp hadj
          subst hyv
          exact Or.inl (by simpa using hy)
        · exact absurd hwv' (fun e => (H i).irrefl (e ▸ hwv))
    rcases hS ⟨i, x⟩ with h | ⟨⟨j, y⟩, hy, hadj⟩
    · exact Or.inl (by simpa using h)
    · rcases hadj with ⟨h, hadj⟩ | ⟨-, hx, -⟩
      · simp only at h
        subst h
        exact Or.inr ⟨y, by simpa using hy, hadj⟩
      · simp only at hx
        subst hx
        exact hsupp
  · intro hS ⟨i, x⟩
    rcases hS i x with h | ⟨y, hy, hadj⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨⟨i, y⟩, by simpa using hy, (join_adj_same H v F i x y).mpr hadj⟩

/-- Restriction and disjoint union are inverse size-preserving bijections between the dominating
sets of the join and the tuples of dominating sets of the copies. -/
def domEquiv (H : ∀ i, SimpleGraph (V i)) (v w : ∀ i, V i)
    (hw : ∀ i (u : V i), (H i).Adj (w i) u ↔ u = v i) (F : SimpleGraph ι) :
    ↥(domSets (join H v F)) ≃ (∀ i, ↥(domSets (H i))) where
  toFun S i := ⟨slice S.1 i, (dominating_iff H v w hw F S.1).mp S.2 i⟩
  invFun f := ⟨univ.sigma fun i => (f i).1, by
    rw [dominating_iff H v w hw F]
    intro i
    convert (f i).2
    ext x
    simp⟩
  left_inv S := by
    apply Subtype.ext
    ext ⟨i, x⟩
    simp
  right_inv f := by
    funext i
    apply Subtype.ext
    ext x
    simp

lemma domEquiv_card (H : ∀ i, SimpleGraph (V i)) (v w : ∀ i, V i)
    (hw : ∀ i (u : V i), (H i).Adj (w i) u ↔ u = v i) (F : SimpleGraph ι)
    (S : ↥(domSets (join H v F))) :
    ∑ i, ((domEquiv H v w hw F S) i).1.card = S.1.card := by
  have : S.1 = univ.sigma fun i => slice S.1 i := by
    ext ⟨i, x⟩
    simp
  conv_rhs => rw [this, Finset.card_sigma]
  rfl

/-- The domination polynomial of the join is the product of those of the copies. -/
lemma domPoly_join (H : ∀ i, SimpleGraph (V i)) (v w : ∀ i, V i)
    (hw : ∀ i (u : V i), (H i).Adj (w i) u ↔ u = v i) (F : SimpleGraph ι) :
    domPoly (join H v F) = ∏ i, domPoly (H i) := by
  unfold domPoly
  rw [Finset.prod_univ_sum]
  rw [← Finset.sum_coe_sort (domSets (join H v F)),
    ← Finset.sum_coe_sort (Fintype.piFinset fun i => domSets (H i))]
  refine Fintype.sum_equiv ((domEquiv H v w hw F).trans
    ((Equiv.subtypePiEquivPi).symm.trans
      (Equiv.subtypeEquivRight (fun f => by simp [Fintype.mem_piFinset])))) _ _ ?_
  intro S
  rw [← domEquiv_card H v w hw F S, Finset.prod_pow_eq_pow_sum]
  rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
/-- The join of connected copies along a connected graph with at least one vertex is
connected. -/
lemma join_connected [Nonempty ι] (H : ∀ i, SimpleGraph (V i)) (v : ∀ i, V i)
    (F : SimpleGraph ι) (hH : ∀ i, (H i).Connected) (hF : F.Connected) :
    (join H v F).Connected := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨i₀, v i₀⟩, ?_⟩
  rintro ⟨j, y⟩
  let g : F →g join H v F := {
    toFun := fun i => ⟨i, v i⟩
    map_rel' := fun h => Or.inr ⟨h, rfl, rfl⟩ }
  let c : H j →g join H v F := {
    toFun := fun x => ⟨j, x⟩
    map_rel' := fun h => (join_adj_same H v F j _ _).mpr h }
  exact ((hF i₀ j).map g).trans ((hH j (v j) y).map c)

/-- For copies `H_i` (`i < r`) with leaves `w_i` whose only neighbour is `v_i`, and any simple
graph `F` on the copy indices: a set dominates the join `J_F` iff every slice dominates its copy;
restriction and disjoint union are inverse size-preserving bijections between the dominating
sets; `D(J_F, x) = ∏ D(H_i, x)` in `ℤ[x]` (the empty product is `1`); and for `r ≥ 1`, if every
`H_i` and `F` is connected, so is `J_F`. -/
theorem leaf_support_join (r : ℕ) (V : Fin r → Type) [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] (H : ∀ i, SimpleGraph (V i)) (v w : ∀ i, V i)
    (hw : ∀ i (u : V i), (H i).Adj (w i) u ↔ u = v i) (F : SimpleGraph (Fin r)) :
    (∀ S : Finset (Σ i, V i), S ∈ domSets (join H v F) ↔ ∀ i, slice S i ∈ domSets (H i)) ∧
    (∃ e : ↥(domSets (join H v F)) ≃ (∀ i, ↥(domSets (H i))),
      (∀ S, (e.symm S).1 = univ.sigma fun i => (S i).1) ∧
      ∀ S, ∑ i, (e S i).1.card = S.1.card) ∧
    domPoly (join H v F) = ∏ i, domPoly (H i) ∧
    (1 ≤ r → (∀ i, (H i).Connected) → F.Connected → (join H v F).Connected) := by
  refine ⟨dominating_iff H v w hw F, ⟨domEquiv H v w hw F, fun _ => rfl,
    domEquiv_card H v w hw F⟩, domPoly_join H v w hw F, fun hr hH hF => ?_⟩
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact join_connected H v F hH hF

end

end D5.S3.Combinatorics.Graph.Domination.LeafSupportJoin
