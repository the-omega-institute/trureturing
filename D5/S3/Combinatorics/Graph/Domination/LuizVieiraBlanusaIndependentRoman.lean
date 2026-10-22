/- GID: D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.claim; result=D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.result; claim=D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.claim
   digest: At k=21 the first Blanusa snark has Roman minimum ≤108 and independent Roman minimum 110. -/

/-
admission_basis: open-problem-resolution (#19801; Refuted)
escape_witness: none; the public result is the designated refutation result (basis=refutes) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Direct frozen dependencies: D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem.private_of_not_dominated_erase (statement_id sha256:b37a0be5b83d8b98c2c136896ed573e158ed489cff531665d9175b151bac921d); D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting.privateNeighbors (statement_id sha256:c556e52ec4c8f4a818ccb913850918fd22bf3c0486e64b0e258fcb9987a121e6).
proof_shape: result: bind-only; escape_witness: none; consumer: admission settlement.
proof_shape: claim: definition; consumer: result.
proof_shape: activeNbrs, IsRomanDom, IsIndepRomanDom, weight, gammaRoman, indepRoman, Vert, a, b, c, d, x, w, y, z, blockOneEdges, blockTwoEdges, linkEdges, blockEdges, linkVerts, linkGraphEdges, verts, edges, snark: source definitions.
proof_shape: all private declarations: bind-only; consumers are the next proof declarations on the live path, ending at result.
The claim keeps the preregistered Roman-domination expressions literally; proofs use the imported frozen graph-counting owners.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Sym.Sym2
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting
import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem
import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.LuizVieiraBlanusaIndependentRoman

open Finset

/- Source: A. G. Luiz and F. A. S. Vieira, "Independent [k]-Roman Domination on Graphs", arXiv:2406.11688v1; Discuss. Math. Graph Theory 45 (2025), 1249–1272, DOI 10.7151/dmgt.2580. The claim quotes the source closing conjecture: "another interesting line of research is finding other classes of graphs with ∆(G) ≤ 3 for which γ[kR](G) = i[kR](G) for k ≥ 2. In fact, we conjecture that this property holds for all generalized Blanuša snarks." -/

section Roman

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `AN_f(v) = {u ∈ N(v) : f(u) > 0}`, the active neighbours of `v`. -/
def activeNbrs (f : V → ℕ) (v : V) : Finset V :=
  (G.neighborFinset v).filter (fun u => 0 < f u)

/-- A [k]-Roman dominating function: `f : V → {0, 1, …, k + 1}` such that every `v` with `f(v) < k` has
`Σ_{u ∈ N[v]} f(u) ≥ k + |AN_f(v)|`. -/
def IsRomanDom (k : ℕ) (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ k + 1) ∧
    ∀ v, f v < k → k + (activeNbrs G f v).card ≤ f v + ∑ u ∈ G.neighborFinset v, f u

/-- An independent [k]-Roman dominating function: the vertices with positive label are pairwise nonadjacent. -/
def IsIndepRomanDom (k : ℕ) (f : V → ℕ) : Prop :=
  IsRomanDom G k f ∧ ∀ u v, 0 < f u → 0 < f v → ¬ G.Adj u v

/-- The weight `ω(f) = Σ_v f(v)`. -/
def weight (f : V → ℕ) : ℕ := ∑ v, f v

/-- `γ[kR](G)`: the minimum weight of a [k]-Roman dominating function. -/
noncomputable def gammaRoman (k : ℕ) : ℕ := sInf {w | ∃ f, IsRomanDom G k f ∧ weight f = w}

/-- `i[kR](G)`: the minimum weight of an independent [k]-Roman dominating function. -/
noncomputable def indepRoman (k : ℕ) : ℕ := sInf {w | ∃ f, IsIndepRomanDom G k f ∧ weight f = w}

end Roman

section Blanusa

/-- Vertex labels: the ten vertices of a block `B₀ᵗ` (`blk 0` to `blk 9`) and the eight vertices of each copy
`L_j` of the block `L` (`lnk j 0` to `lnk j 7`). -/
inductive Vert
  | blk : Fin 10 → Vert
  | lnk : ℕ → Fin 8 → Vert
  deriving DecidableEq

open Vert

/-- Border vertices of `B₀ᵗ` (Figure 5): `a`, `b`, `c`, `d`. -/
def a : Vert := blk 0
def b : Vert := blk 6
def c : Vert := blk 3
def d : Vert := blk 9

/-- Border vertices of `L_j` (Figure 5(c)): `x_j`, `y_j`, `w_j`, `z_j`. -/
def x (j : ℕ) : Vert := lnk j 0
def w (j : ℕ) : Vert := lnk j 2
def y (j : ℕ) : Vert := lnk j 5
def z (j : ℕ) : Vert := lnk j 7

/-- `E(B₀¹)` (Figure 5(a)): top row `a = 0, 1, 2, c = 3`, middle row `4, 5`, bottom row `b = 6, 7, 8, d = 9`. -/
def blockOneEdges : Finset (Sym2 Vert) :=
  {s(blk 0, blk 1), s(blk 1, blk 2), s(blk 2, blk 3), s(blk 3, blk 9), s(blk 9, blk 8), s(blk 8, blk 7),
   s(blk 7, blk 6), s(blk 6, blk 4), s(blk 4, blk 0), s(blk 1, blk 7), s(blk 2, blk 5), s(blk 5, blk 8),
   s(blk 4, blk 5)}

/-- `E(B₀²)` (Figure 5(b)): top row `a = 0, 1, c = 3`, the vertex `2` below `1`, middle row `4, 5, 7`, bottom row
`b = 6, 8, d = 9`. -/
def blockTwoEdges : Finset (Sym2 Vert) :=
  {s(blk 0, blk 1), s(blk 1, blk 3), s(blk 1, blk 2), s(blk 2, blk 8), s(blk 2, blk 5), s(blk 0, blk 4),
   s(blk 4, blk 6), s(blk 4, blk 5), s(blk 5, blk 7), s(blk 3, blk 7), s(blk 7, blk 9), s(blk 6, blk 8),
   s(blk 8, blk 9)}

/-- `E(L_j)` (Figure 5(c)): top row `x_j = 0, 1, w_j = 2`, middle row `3, 4`, bottom row `y_j = 5, 6, z_j = 7`. -/
def linkEdges (j : ℕ) : Finset (Sym2 Vert) :=
  {s(lnk j 0, lnk j 1), s(lnk j 1, lnk j 2), s(lnk j 2, lnk j 4), s(lnk j 4, lnk j 7), s(lnk j 7, lnk j 6),
   s(lnk j 6, lnk j 5), s(lnk j 5, lnk j 3), s(lnk j 3, lnk j 0), s(lnk j 1, lnk j 6), s(lnk j 3, lnk j 4)}

/-- The edges of `B₀ᵗ`. -/
def blockEdges (t : ℕ) : Finset (Sym2 Vert) := if t = 1 then blockOneEdges else blockTwoEdges

/-- `V(L_j)`. -/
def linkVerts (j : ℕ) : Finset Vert := (univ : Finset (Fin 8)).image (lnk j)

/-- `E(LG_i) = E(L_{i−1}) ∪ E(L_i) ∪ {w_{i−1} y_i, z_{i−1} x_i}` (Figure 8). -/
def linkGraphEdges (i : ℕ) : Finset (Sym2 Vert) :=
  linkEdges (i - 1) ∪ linkEdges i ∪ {s(w (i - 1), y i), s(z (i - 1), x i)}

/-- `V(Bᵢᵗ)`: `V(B₁ᵗ) = V(B₀ᵗ) ∪ V(L₁)`, `V(B₂ᵗ) = V(B₀ᵗ) ∪ V(L₁) ∪ V(L₂)`, and
`V(Bᵢᵗ) = V(Bᵗ_{i−2}) ∪ V(LGᵢ)` for `i ≥ 3`. -/
def verts : ℕ → Finset Vert
  | 0 => (univ : Finset (Fin 10)).image blk
  | 1 => (univ : Finset (Fin 10)).image blk ∪ linkVerts 1
  | 2 => (univ : Finset (Fin 10)).image blk ∪ linkVerts 1 ∪ linkVerts 2
  | i + 3 => verts (i + 1) ∪ (linkVerts (i + 2) ∪ linkVerts (i + 3))

/-- `E(Bᵢᵗ)` (Section 4): the edge sets of `B₁ᵗ` and `B₂ᵗ` as listed, and for `i ≥ 3`
`E(Bᵢᵗ) = (E(Bᵗ_{i−2}) \ E^out_{i−2}) ∪ E(LGᵢ) ∪ E^in_i` with `E^out_{i−2} = {a z_{i−2}, b w_{i−2}}` and
`E^in_i = {w_{i−2} y_{i−1}, z_{i−2} x_{i−1}, a z_i, b w_i}`. -/
def edges (t : ℕ) : ℕ → Finset (Sym2 Vert)
  | 0 => blockEdges t
  | 1 =>
    if t = 1 then blockEdges t ∪ linkEdges 1 ∪ {s(c, y 1), s(d, x 1), s(a, z 1), s(b, w 1)}
    else blockEdges t ∪ linkEdges 1 ∪ {s(b, w 1), s(a, z 1), s(c, y 1), s(d, x 1)}
  | 2 =>
    if t = 1 then blockEdges t ∪ linkEdges 1 ∪ linkEdges 2 ∪
      {s(c, y 1), s(d, x 1), s(w 1, y 2), s(z 1, x 2), s(a, z 2), s(b, w 2)}
    else blockEdges t ∪ linkEdges 1 ∪ linkEdges 2 ∪
      {s(b, w 2), s(a, z 2), s(c, y 1), s(d, x 1), s(z 1, x 2), s(w 1, y 2)}
  | i + 3 =>
    (edges t (i + 1) \ {s(a, z (i + 1)), s(b, w (i + 1))}) ∪ linkGraphEdges (i + 3) ∪
      {s(w (i + 1), y (i + 2)), s(z (i + 1), x (i + 2)), s(a, z (i + 3)), s(b, w (i + 3))}

/-- The generalized Blanuša snark `Bᵢᵗ`, on its vertex set `V(Bᵢᵗ)`. -/
def snark (t i : ℕ) : SimpleGraph {v // v ∈ verts i} :=
  SimpleGraph.fromRel fun u v => s(u.1, v.1) ∈ edges t i

private instance (t i : ℕ) : DecidableRel (snark t i).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (s(u.1, v.1) ∈ edges t i ∨ s(v.1, u.1) ∈ edges t i)))

/-- The closing conjecture: for every generalized Blanuša snark `Bᵢᵗ` (`t ∈ {1, 2}`, `i ≥ 1`) and every
`k ≥ 2`, `γ[kR](Bᵢᵗ) = i[kR](Bᵢᵗ)`. -/
def claim : Prop :=
  ∀ t i k : ℕ, (t = 1 ∨ t = 2) → 1 ≤ i → 2 ≤ k → gammaRoman (snark t i) k = indepRoman (snark t i) k

end Blanusa

open Finset

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

 private theorem card18 : Fintype.card {v // v ∈ verts 1} = 18 := by decide
 private theorem cubic18 (v : {v // v ∈ verts 1}) : ((snark 1 1).neighborFinset v).card = 3 := by
  revert v
  decide

 private theorem uniform_roman : IsRomanDom (snark 1 1) 21 (fun _ => 6) := by
  constructor
  · intro v; change 6 ≤ 22; omega
  · intro v hv
    have hc := cubic18 v
    simp [activeNbrs, hc]

 private theorem uniform_weight : weight (fun _ : {v // v ∈ verts 1} => 6) = 108 := by
  change (∑ _ : {v // v ∈ verts 1}, 6) = 108
  rw [sum_const, card_univ, card18]
  decide

 private theorem gamma_le : gammaRoman (snark 1 1) 21 ≤ 108 := by
  exact Nat.sInf_le ⟨fun _ => 6, uniform_roman, uniform_weight⟩


section General
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def covered (S : Finset V) : Finset V := S.biUnion (fun v => insert v (G.neighborFinset v))

omit [DecidableEq V] in
private theorem positive_ge {k : ℕ} {f : V → ℕ} (h : IsIndepRomanDom G k f)
    {v : V} (hv : 0 < f v) : k ≤ f v := by
  by_contra hn
  have hs : ∑ u ∈ G.neighborFinset v, f u = 0 := by
    apply sum_eq_zero
    intro u hu
    have hnu := h.2 v u hv
    have hadj := (G.mem_neighborFinset v u).mp hu
    by_contra hnzero
    exact hnu (by omega) hadj
  have hi := h.1.2 v (by omega)
  rw [hs] at hi
  omega

omit [DecidableEq V] in
private theorem support_dominates {k : ℕ} (hk : 0 < k) {f : V → ℕ}
    (h : IsRomanDom G k f) (v : V) :
    v ∈ (Set.toFinite (Function.support f)).toFinset ∨ ∃ u ∈ (Set.toFinite (Function.support f)).toFinset, G.Adj v u := by
  by_cases hp : 0 < f v
  · exact Or.inl (by simpa only [Set.Finite.mem_toFinset, Function.mem_support, Nat.pos_iff_ne_zero] using hp)
  · right
    by_contra hn
    have hs : ∑ u ∈ G.neighborFinset v, f u = 0 := by
      apply sum_eq_zero
      intro u hu
      have hadj := (G.mem_neighborFinset v u).mp hu
      by_contra hz
      exact hn ⟨u, by simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hz, hadj⟩
    have hi := h.2 v (by omega)
    rw [hs] at hi
    omega

private theorem covered_card_le (hc : ∀ v, (G.neighborFinset v).card ≤ 3) (S : Finset V) :
    (covered G S).card ≤ 4 * S.card := by
  simpa only [covered, Nat.mul_comm] using
    (Finset.card_biUnion_le_card_mul S (fun v => insert v (G.neighborFinset v)) 4
      (fun v _ => (Finset.card_insert_le v (G.neighborFinset v)).trans
        (Nat.add_le_add_right (hc v) 1)))

private theorem support_card_bound (hc : ∀ v, (G.neighborFinset v).card ≤ 3)
    {k : ℕ} (hk : 0 < k) {f : V → ℕ} (h : IsRomanDom G k f) :
    Fintype.card V ≤ 4 * ((Set.toFinite (Function.support f)).toFinset).card := by
  have hcov : (univ : Finset V) ⊆ covered G ((Set.toFinite (Function.support f)).toFinset) := by
    intro v hv
    rcases support_dominates G hk h v with hs | ⟨u, hu, hadj⟩
    · exact mem_biUnion.mpr ⟨v, hs, mem_insert_self _ _⟩
    · exact mem_biUnion.mpr ⟨u, hu, mem_insert_of_mem ((G.mem_neighborFinset u v).mpr hadj.symm)⟩
  have hi := card_le_card hcov
  rw [card_univ] at hi
  exact hi.trans (covered_card_le G hc _)


open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem

private theorem private_neighbor_of_cover_bound
    (hc : ∀ v, (G.neighborFinset v).card ≤ 3) (S : Finset V)
    (hS : G.IsDominating (S : Set V))
    (hsize : 1 + 4 * (S.card - 1) < Fintype.card V) (s : V) (hs : s ∈ S) :
    ∃ u ∈ privateNeighbors G S, G.Adj s u := by
  classical
  by_contra hn
  have hdom (u : V) (hus : u ≠ s) :
      u ∈ S.erase s ∨ ∃ w ∈ S.erase s, G.Adj u w := by
    by_contra hnu
    have hp := private_of_not_dominated_erase G S s u hS hs hus hnu
    exact hn ⟨u, hp⟩
  have hcov : (univ : Finset V).erase s ⊆ covered G (S.erase s) := by
    intro u hu
    rcases hdom u (mem_erase.mp hu).1 with hm | ⟨w, hw, hadj⟩
    · exact mem_biUnion.mpr ⟨u, hm, mem_insert_self _ _⟩
    · exact mem_biUnion.mpr ⟨w, hw,
        mem_insert_of_mem ((G.mem_neighborFinset w u).mpr hadj.symm)⟩
  have hi := (card_le_card hcov).trans (covered_card_le G hc _)
  rw [card_erase_of_mem (mem_univ s), card_univ, card_erase_of_mem hs] at hi
  omega

private theorem private_label_ge {k : ℕ} (hk : 0 < k) {f : V → ℕ}
    (h : IsRomanDom G k f) {s u : V} (hs : 0 < f s)
    (hu : u ∈ privateNeighbors G ((Set.toFinite (Function.support f)).toFinset)) (hadj : G.Adj s u) : k + 1 ≤ f s := by
  classical
  have hp := (mem_filter.mp hu).2
  have hzero : f u = 0 := by
    have hn := hp.1
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hn
  have hcard : (((Set.toFinite (Function.support f)).toFinset).filter (G.Adj u)).card = 1 := by
    rw [← Finset.filter_congr_decidable ((Set.toFinite (Function.support f)).toFinset) (G.Adj u)
      (fun w => Classical.propDecidable (G.Adj u w))]
    exact hp.2
  have hsc : s ∈ ((Set.toFinite (Function.support f)).toFinset).filter (G.Adj u) :=
    mem_filter.mpr ⟨by simpa only [Set.Finite.mem_toFinset, Function.mem_support, Nat.pos_iff_ne_zero] using hs, hadj.symm⟩
  have huniq (w : V) (hw : 0 < f w) (haw : G.Adj u w) : w = s := by
    exact card_le_one.mp (Nat.le_of_eq hcard) w
      (mem_filter.mpr ⟨by simpa only [Set.Finite.mem_toFinset, Function.mem_support, Nat.pos_iff_ne_zero] using hw, haw⟩) s hsc
  have hact : activeNbrs G f u = {s} := by
    ext w
    simp only [activeNbrs, mem_filter, SimpleGraph.mem_neighborFinset, mem_singleton]
    constructor
    · rintro ⟨ha, hw⟩
      exact huniq w hw ha
    · rintro rfl
      exact ⟨hadj.symm, hs⟩
  have hsum : ∑ w ∈ G.neighborFinset u, f w = f s := by
    apply sum_eq_single s
    · intro w hw hws
      by_contra hz
      exact hws (huniq w (by omega) ((G.mem_neighborFinset u w).mp hw))
    · intro hn
      exact False.elim (hn ((G.mem_neighborFinset u s).mpr hadj.symm))
  have hi := h.2 u (by omega)
  rw [hact, card_singleton, hzero, hsum] at hi
  omega

omit [DecidableEq V] in
private theorem weight_ge_support_mul {f : V → ℕ} {m : ℕ}
    (h : ∀ v ∈ (Set.toFinite (Function.support f)).toFinset, m ≤ f v) : m * ((Set.toFinite (Function.support f)).toFinset).card ≤ weight f := by
  have hsum := ((Set.toFinite (Function.support f)).toFinset).card_nsmul_le_sum f m h
  simpa [weight, nsmul_eq_mul, Nat.mul_comm] using
    hsum.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ ((Set.toFinite (Function.support f)).toFinset)))

end General

private theorem weight_lower {f : {v // v ∈ verts 1} → ℕ} (h : IsIndepRomanDom (snark 1 1) 21 f) :
    110 ≤ weight f := by
  have hc (v : {v // v ∈ verts 1}) : ((snark 1 1).neighborFinset v).card ≤ 3 := (cubic18 v).le
  have hb := support_card_bound (snark 1 1) hc (by decide : 0 < 21) h.1
  rw [card18] at hb
  have h5 : 5 ≤ ((Set.toFinite (Function.support f)).toFinset).card := by omega
  by_cases h6 : 6 ≤ ((Set.toFinite (Function.support f)).toFinset).card
  · have hw := weight_ge_support_mul (m := 21) (f := f) (fun v hv =>
        positive_ge (snark 1 1) h (by simpa only [Set.Finite.mem_toFinset, Function.mem_support, Nat.pos_iff_ne_zero] using hv))
    omega
  · have hcard : ((Set.toFinite (Function.support f)).toFinset).card = 5 := by omega
    have hw := weight_ge_support_mul (m := 22) (f := f) (by
      intro s hs
      obtain ⟨u, hu, hadj⟩ := private_neighbor_of_cover_bound (snark 1 1) hc ((Set.toFinite (Function.support f)).toFinset)
        (fun v => support_dominates (snark 1 1) (by decide : 0 < 21) h.1 v)
        (by rw [hcard, card18]; decide) s hs
      exact private_label_ge (snark 1 1) (by decide : 0 < 21) h.1 (by simpa only [Set.Finite.mem_toFinset, Function.mem_support, Nat.pos_iff_ne_zero] using hs) hu hadj)
    omega


private def witness (v : {v // v ∈ verts 1}) : ℕ :=
  if v.1 = Vert.blk 1 ∨ v.1 = Vert.blk 4 ∨ v.1 = Vert.blk 9 ∨
    v.1 = Vert.lnk 1 4 ∨ v.1 = Vert.lnk 1 6 then 22 else 0

private theorem witness_irdf : IsIndepRomanDom (snark 1 1) 21 witness := by
  unfold IsIndepRomanDom IsRomanDom
  decide

private theorem witness_weight : weight witness = 110 := by decide

private theorem indep_eq : indepRoman (snark 1 1) 21 = 110 := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le ⟨witness, witness_irdf, witness_weight⟩
  · apply le_csInf (show {w | ∃ f, IsIndepRomanDom (snark 1 1) 21 f ∧ weight f = w}.Nonempty from
      ⟨110, witness, witness_irdf, witness_weight⟩)
    rintro w ⟨f, hf, rfl⟩
    exact weight_lower hf

theorem result : ¬ LuizVieiraBlanusaIndependentRoman.claim := by
  intro h
  have heq := h 1 1 21 (Or.inl rfl) (by decide) (by decide)
  have hu := gamma_le
  rw [heq, indep_eq] at hu
  omega


end LuizVieiraBlanusaIndependentRoman
