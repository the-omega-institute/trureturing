/- GID: D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14
   generality: I
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.claim; result=D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.result; claim=D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.claim
   digest: A connected 14-vertex DDMOG with 23 edges refutes the proposed 24-edge lower bound. -/

/-
result:
  proof_shape: bind-only (finite certificates, existing connectivity, integer normalization).
  escape_witness: none.
  admission_basis: open-problem-resolution (#25620; Refuted).
  Direct frozen dependencies: none.

All declarations have proof_shape: bind-only and escape_witness: none.
Direct frozen dependencies for every declaration: none.
Consumers: weight -> IsDDMLabeling; IsConsecutiveLabeling -> IsDDMLabeling;
IsDDMLabeling, edgeCount -> claim, result; claim -> result;
arcs -> witness, witness_adj_decidable; witness, labels -> result;
witness_adj_decidable -> witness_oriented, witness_edges, witness_connected;
underlying_adj_decidable, underlying_eq -> witness_connected; labels_consecutive, witness_weights -> witness_ddm;
witness_oriented, witness_ddm, witness_edges, witness_connected -> result.
The claim inlines the preregistered orientation and underlying-graph expressions;
the proof uses Digraph.toSimpleGraphInclusive through the consumed underlying_eq.
Neighborhood sets are inlined in weight; no forwarding definitions are introduced.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! A 23-edge certificate for the fourteen-vertex DDMOG minimality conjecture. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.AceskaLortRippergerSparsest14

open scoped BigOperators

open Classical in
/-- The source vertex weight: incoming label sum minus outgoing label sum. -/
noncomputable def weight {V : Type} [Fintype V] (D : Digraph V) (f : V → ℤ) (x : V) : ℤ :=
  (∑ y, if y ∈ {y | D.Adj y x} then f y else 0) -
    (∑ y, if y ∈ {y | D.Adj x y} then f y else 0)

/-- A bijective labeling by the consecutive integer labels 1,...,|V|. -/
def IsConsecutiveLabeling {V : Type} [Fintype V] (f : V → ℤ) : Prop :=
  Set.BijOn f Set.univ (Set.Icc (1 : ℤ) (Fintype.card V : ℤ))

/-- Section 1.1: a DDM labeling is consecutive bijective and has one common natural weight. -/
def IsDDMLabeling {V : Type} [Fintype V] (D : Digraph V) (f : V → ℤ) : Prop :=
  IsConsecutiveLabeling f ∧ ∃ k : ℕ, ∀ x : V, weight D f x = (k : ℤ)

open Classical in
/-- Number of directed edges, which equals the number of underlying edges for an orientation. -/
noncomputable def edgeCount {V : Type} [Fintype V] (D : Digraph V) : ℕ :=
  Fintype.card {e : V × V // D.Adj e.1 e.2}

/-- The fixed-order conjecture in the conclusion: every connected 14-vertex DDMOG has at least
24 edges. The source's DDM labeling definition retains its explicit common natural constant. -/
def claim : Prop :=
  ∀ (D : Digraph (Fin 14)) (f : Fin 14 → ℤ),
    Std.Asymm D.Adj →
      (SimpleGraph.fromRel (fun u v => D.Adj u v ∨ D.Adj v u)).Connected →
      IsDDMLabeling D f → 24 ≤ edgeCount D

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def arcs : Finset (Fin 14 × Fin 14) :=
  {(0,4), (0,11), (1,4), (1,10), (2,8), (3,2), (3,12), (4,2),
   (5,3), (5,9), (6,1), (6,11), (7,0), (7,10), (8,0), (8,1),
   (9,3), (9,12), (10,9), (11,7), (12,13), (13,5), (13,6)}

private def witness : Digraph (Fin 14) := ⟨fun u v => (u,v) ∈ arcs⟩

private def labels (v : Fin 14) : ℤ := (v.val : ℤ) + 1

private instance witness_adj_decidable : DecidableRel witness.Adj :=
  inferInstanceAs (DecidableRel (fun u v : Fin 14 => (u,v) ∈ arcs))

private instance underlying_adj_decidable : DecidableRel witness.toSimpleGraphInclusive.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel witness.Adj).Adj)

private theorem underlying_eq {V : Type} (D : Digraph V) :
    SimpleGraph.fromRel (fun u v => D.Adj u v ∨ D.Adj v u) =
      D.toSimpleGraphInclusive := by
  ext u v
  simp only [SimpleGraph.fromRel_adj, Digraph.toSimpleGraphInclusive]
  tauto

private theorem witness_oriented : Std.Asymm witness.Adj := by
  apply asymm_def.mpr
  decide +kernel

private theorem labels_consecutive : IsConsecutiveLabeling labels := by
  let shift : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding 1)
  let shiftedFin : Fin 14 ↪ ℤ := Fin.valEmbedding.trans shift
  have image_eq : shiftedFin '' Set.univ = Set.Icc (1 : ℤ) (↑(14 : ℕ)) := by
    rw [← Finset.coe_univ, ← Finset.coe_map, ← Finset.coe_Icc,
      show shiftedFin = Fin.valEmbedding.trans shift from rfl, ← Finset.map_map,
      Fin.map_valEmbedding_univ, Nat.Iio_eq_range, Int.Icc_eq_finset_map,
      add_sub_cancel_right, Int.toNat_natCast]
  have labels_eq : (shiftedFin : Fin 14 → ℤ) = labels := by
    funext v
    change (1 : ℤ) + (v.val : ℤ) = (v.val : ℤ) + 1
    exact add_comm _ _
  have bijective := shiftedFin.injective.bijOn_image (s := Set.univ)
  rw [image_eq, labels_eq] at bijective
  simpa only [IsConsecutiveLabeling, Fintype.card_fin] using bijective

private theorem witness_weights : ∀ x : Fin 14, weight witness labels x = 0 := by
  intro x
  fin_cases x <;>
    norm_num [weight, witness, arcs, labels, Fin.sum_univ_succ]

private theorem witness_ddm : IsDDMLabeling witness labels := by
  exact ⟨labels_consecutive, 0, witness_weights⟩

private theorem witness_edges : edgeCount witness = 23 := by
  classical
  unfold edgeCount
  rw [Fintype.card_subtype]
  decide +kernel

private theorem witness_connected :
    (SimpleGraph.fromRel (fun u v => witness.Adj u v ∨ witness.Adj v u)).Connected := by
  rw [underlying_eq]
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, ?_⟩
  have h0 : witness.toSimpleGraphInclusive.Reachable 0 0 := SimpleGraph.Reachable.refl _
  have h4 : witness.toSimpleGraphInclusive.Reachable 0 4 :=
    (show witness.toSimpleGraphInclusive.Adj 0 4 from by decide +kernel).reachable
  have h11 : witness.toSimpleGraphInclusive.Reachable 0 11 :=
    (show witness.toSimpleGraphInclusive.Adj 0 11 from by decide +kernel).reachable
  have h7 : witness.toSimpleGraphInclusive.Reachable 0 7 :=
    (show witness.toSimpleGraphInclusive.Adj 0 7 from by decide +kernel).reachable
  have h8 : witness.toSimpleGraphInclusive.Reachable 0 8 :=
    (show witness.toSimpleGraphInclusive.Adj 0 8 from by decide +kernel).reachable
  have h2 : witness.toSimpleGraphInclusive.Reachable 0 2 :=
    h8.trans (show witness.toSimpleGraphInclusive.Adj 8 2 from by decide +kernel).reachable
  have h1 : witness.toSimpleGraphInclusive.Reachable 0 1 :=
    h8.trans (show witness.toSimpleGraphInclusive.Adj 8 1 from by decide +kernel).reachable
  have h10 : witness.toSimpleGraphInclusive.Reachable 0 10 :=
    h1.trans (show witness.toSimpleGraphInclusive.Adj 1 10 from by decide +kernel).reachable
  have h6 : witness.toSimpleGraphInclusive.Reachable 0 6 :=
    h1.trans (show witness.toSimpleGraphInclusive.Adj 1 6 from by decide +kernel).reachable
  have h13 : witness.toSimpleGraphInclusive.Reachable 0 13 :=
    h6.trans (show witness.toSimpleGraphInclusive.Adj 6 13 from by decide +kernel).reachable
  have h12 : witness.toSimpleGraphInclusive.Reachable 0 12 :=
    h13.trans (show witness.toSimpleGraphInclusive.Adj 13 12 from by decide +kernel).reachable
  have h5 : witness.toSimpleGraphInclusive.Reachable 0 5 :=
    h13.trans (show witness.toSimpleGraphInclusive.Adj 13 5 from by decide +kernel).reachable
  have h3 : witness.toSimpleGraphInclusive.Reachable 0 3 :=
    h5.trans (show witness.toSimpleGraphInclusive.Adj 5 3 from by decide +kernel).reachable
  have h9 : witness.toSimpleGraphInclusive.Reachable 0 9 :=
    h5.trans (show witness.toSimpleGraphInclusive.Adj 5 9 from by decide +kernel).reachable
  intro v
  fin_cases v <;> assumption

theorem result : ¬ claim := by
  intro h
  have hb := h witness labels witness_oriented witness_connected witness_ddm
  rw [witness_edges] at hb
  omega


end D5.S3.Combinatorics.EdgeLabeling.AceskaLortRippergerSparsest14
