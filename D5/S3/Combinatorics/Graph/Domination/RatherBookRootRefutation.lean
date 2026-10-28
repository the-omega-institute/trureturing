/- GID: D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.claim; result=D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.result; claim=D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.claim
   digest: The complete all-positive-order book domination-root conjecture fails at the four-cycle. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverage
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-!
Bilal Ahmad Rather, arXiv:2604.08998v1/v2, Section 5, Conjecture 5.4:
even orders have a double zero, a simple root below -2 and a simple root
between -1/2 and zero; odd orders have a double zero and two distinct simple
roots between -1/2 and zero, with no other real roots. Section 2 defines the
books for every n >= 1 by gluing n four-cycles along one edge.

The model below keeps that entire domain and both complete root classifications.
Only the legal order-one book is needed to contradict the universal assertion.
The amended assertion restricted to n >= 2 is outside this result.

proof_shape: result and consumed finite-count helpers: bind-only.
admission_basis: open-problem-resolution; preregistration issue #23025.
escape_witness: null. The C4 enumeration and positive quadratic are prior mathematics.
The sole public theorem is the designated refutation; private helpers are consumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.RatherBookRootRefutation

open Finset Polynomial
open D5.S3.Combinatorics.Graph.DominatingSetAverage

/-- The common edge is 0--1. Page i is 0--1--(2i+2)--(2i+3)--0.
The vertex type has exactly the two shared vertices and two new vertices per page. -/
def pageForward (n : ℕ) (u v : Fin (2 * n + 2)) : Prop :=
  (u.val = 0 ∧ v.val = 1) ∨ ∃ i : Fin n,
    (u.val = 1 ∧ v.val = 2 * i.val + 2) ∨
    (u.val = 2 * i.val + 2 ∧ v.val = 2 * i.val + 3) ∨
    (u.val = 2 * i.val + 3 ∧ v.val = 0)

instance (n : ℕ) (u v : Fin (2 * n + 2)) : Decidable (pageForward n u v) := by
  unfold pageForward
  infer_instance

/-- The actual simple undirected shared-edge four-cycle book, for every order. -/
def bookGraph (n : ℕ) : SimpleGraph (Fin (2 * n + 2)) where
  Adj u v := pageForward n u v ∨ pageForward n v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro v h
    have hn : ¬ pageForward n v v := by
      rintro (⟨h0, h1⟩ | ⟨i, hi⟩)
      · omega
      · rcases hi with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
    exact h.elim hn hn⟩

instance (n : ℕ) : DecidableRel (bookGraph n).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Ordinary domination polynomial, summed over the owner's actual dominating subsets.
No independence, certification predicate, source formula or numerical certificate is used. -/
noncomputable def dominationPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ[X] :=
  ∑ S ∈ domSets G, (X : ℝ[X]) ^ S.card

/-- Exact multiplicity and exhaustive real-root classification. -/
def FourRealRoots (p : ℝ[X]) (a b : ℝ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
  p.IsRoot 0 ∧ p.IsRoot a ∧ p.IsRoot b ∧
  p.rootMultiplicity 0 = 2 ∧ p.rootMultiplicity a = 1 ∧ p.rootMultiplicity b = 1 ∧
  ∀ r : ℝ, p.IsRoot r ↔ r = 0 ∨ r = a ∨ r = b

/-- The whole published Conjecture 5.4, on all n >= 1, including both parity clauses. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (Even n → ∃ a b : ℝ,
      a < -2 ∧ -(1 / 2 : ℝ) < b ∧ b < 0 ∧
      FourRealRoots (dominationPolynomial (bookGraph n)) a b) ∧
    (Odd n → ∃ a b : ℝ,
      -(1 / 2 : ℝ) < a ∧ a < 0 ∧ -(1 / 2 : ℝ) < b ∧ b < 0 ∧
      FourRealRoots (dominationPolynomial (bookGraph n)) a b)

private theorem book_one_eq_cycle : bookGraph 1 = SimpleGraph.cycleGraph 4 := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide +kernel

private theorem cycle_domSets : domSets (SimpleGraph.cycleGraph 4) =
    ({ {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
       {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3} } :
      Finset (Finset (Fin 4))) := by
  have h : ∀ S : Finset (Fin 4),
      (∀ v, v ∈ S ∨ ∃ w ∈ S, (SimpleGraph.cycleGraph 4).Adj v w) ↔
      S ∈ ({ {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
             {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3} } :
        Finset (Finset (Fin 4))) := by decide +kernel
  ext S
  rw [mem_domSets]
  exact h S

private theorem book_one_polynomial : dominationPolynomial (bookGraph 1) =
    6 * X ^ 2 + 4 * X ^ 3 + X ^ 4 := by
  rw [book_one_eq_cycle]
  unfold dominationPolynomial
  rw [cycle_domSets]
  norm_num [Finset.sum_insert, Finset.sum_singleton]
  <;> ring

/-- Literal negation of the entire closed conjecture, using its legal B1 = C4 boundary. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨a, b, _, _, _, _, hr⟩ := (h 1 (by decide)).2 (by decide)
  obtain ⟨ha, _, _, _, hroot, _⟩ := hr
  have hp : (dominationPolynomial (bookGraph 1)).eval a =
      a ^ 2 * ((a + 2) ^ 2 + 2) := by
    rw [book_one_polynomial]
    simp only [eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
    ring
  have hpos : 0 < a ^ 2 * ((a + 2) ^ 2 + 2) :=
    mul_pos (sq_pos_of_ne_zero ha) (by positivity)
  exact (ne_of_gt hpos) (hp.symm.trans hroot)

end D5.S3.Combinatorics.Graph.Domination.RatherBookRootRefutation
