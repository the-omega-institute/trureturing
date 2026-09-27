/- GID: D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree
   generality: I
   mirror-B: D5/B/S3/Factorization/Combinatorics/LoopyGeneralizedDegree
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.claim; result=D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result; claim=D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.claim
   digest: Two eight-vertex looped trees carry one ordinary Loopy polynomial and two generalized degree polynomials. -/
import D5.S3.Factorization.Combinatorics.LoopyEvaluator
import Mathlib.Data.Finset.Powerset
set_option autoImplicit false
namespace D5.S3.Factorization.Combinatorics.LoopyGeneralizedDegree
open scoped BigOperators
open D5.S3.Factorization.Combinatorics.LoopyDegreeSequence

/-- Edges with both endpoints in `S`, together with the accumulated loops carried by `S`.
A loop lies inside `S` exactly when its vertex does, and never crosses. -/
def inside (E : List Edge) (ell : Nat → Nat) (S : Finset Nat) : Nat :=
  (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).length + ∑ v ∈ S, ell v

/-- Edges with exactly one endpoint in `S`. -/
def crossing (E : List Edge) (S : Finset Nat) : Nat :=
  (E.filter fun e => (e.1 ∈ S) ≠ (e.2 ∈ S)).length

/-- The exponent triples of the generalized degree polynomial, one per subset of the vertex
set: the size of the subset, the number of edges inside it, and the number of edges with
exactly one endpoint in it. Two graphs have the same generalized degree polynomial exactly
when these multisets agree. -/
def gdTriples (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) :
    Multiset (Nat × Nat × Nat) :=
  V.powerset.val.map fun S => (S.card, inside E ell S, crossing E S)

/-- The eight vertices carrying both graphs. -/
def V : Finset Nat := {0, 1, 2, 3, 4, 5, 6, 7}

/-- A tree with one loop at vertex `1`, the loop written as the pending edge `(1, 1)`. -/
def EG : List Edge := [(1, 1), (0, 1), (0, 5), (1, 2), (1, 4), (2, 3), (5, 6), (5, 7)]

/-- A tree with one loop at vertex `4`. -/
def EH : List Edge := [(4, 4), (0, 1), (0, 4), (0, 7), (1, 2), (2, 3), (4, 5), (4, 6)]

/-- The ordinary Loopy polynomial determines the generalized degree polynomial. -/
def claim : Prop :=
  ∀ (V W : Finset Nat) (E F : List Edge) (ell eta : Nat → Nat),
    Valid V E ell → Valid W F eta → loopy V E ell = loopy W F eta →
      gdTriples V E ell = gdTriples W F eta

set_option maxRecDepth 8000 in
/-- The two eight-vertex looped trees refute the claim. Their encodings retain every endpoint
and store no loops away from the vertex set; their ordinary Loopy polynomials agree after the
deletion-contraction recursion is run to its `2^7` leaves; and their exponent-triple multisets
differ, because the subsets of size two spanning two inside edges and two crossing edges number
one for the first graph and two for the second. -/
theorem result : ¬ claim := by
  intro h
  have hG : Valid V EG (fun _ => 0) := ⟨by decide, fun _ _ => rfl⟩
  have hH : Valid V EH (fun _ => 0) := ⟨by decide, fun _ _ => rfl⟩
  have hL : loopy V EG (fun _ => 0) = loopy V EH (fun _ => 0) := by
    simp +decide [loopy, loopyAux, V, EG, EH, contractEdge, contractVertex, contractLoops,
      addLoop, Function.update, Finset.prod_insert, Finset.erase_insert_of_ne,
      Finset.mem_insert, Finset.mem_singleton]
    ring
  exact absurd (h V V EG EH (fun _ => 0) (fun _ => 0) hG hH hL) (by decide)

end D5.S3.Factorization.Combinatorics.LoopyGeneralizedDegree
