/- GID: D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/KimberlingCombWienerDeterminantRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Data.Int.Interval]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.claim; result=D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.result; claim=D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.claim
   digest: At n = 3, the comb index 1 differs from the matrix count 2, refuting the A192023 comment. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.KimberlingCombWienerDeterminantRefutation

/-!
OEIS A192023 names the Wiener index of the comb graph with `2m` vertices,
offset one. Clark Kimberling's comment of 2012-03-31 conjectures:
"for n>2, A192023(n-2) is the number of 2 X 2 matrices with all terms in
{1,2,...,n} and determinant 2n."

The graph and index below implement the literal definition, not the
sequence's cubic formula. Non-diagonal elements of `Sym2 V` encode each
unordered pair of distinct vertices exactly once. The summand is Mathlib's
shortest-walk distance, lifted using its symmetry. For disconnected graphs
Mathlib's natural distance is zero; the refutation uses the connected comb
with two vertices and one edge, so this convention is immaterial here.

Integer quadruples `(a,b,c,d)` correspond bijectively to the matrices
`[[a,b],[c,d]]`, whose determinant is `a*d-b*c` (`Matrix.det_fin_two`).
Entries are restricted to the integer interval `[1,n]` before filtering.
The n=3 certificate counts the two matrices `[[3,1],[3,3]]` and
`[[3,3],[1,3]]`, whereas the comb with two vertices has Wiener index one.
This refutes only the literal comment; it does not repair its indexing or
claim first discovery. The entry and revision history were checked on
2026-09-13; revision #24 still contains the comment.
-/

/-- The comb on `2m` vertices: consecutive left vertices form the spine,
and the right vertex at each index is pendant from the corresponding left
vertex. `fromRel` adds reverse edges and excludes loops. -/
def comb (m : ℕ) : SimpleGraph (Fin m ⊕ Fin m) :=
  SimpleGraph.fromRel fun u =>
    Sum.elim
      (fun i => Sum.elim (fun j => i.val + 1 = j.val) (fun j => i = j))
      (fun _ => fun _ => False) u

/-- Sum of graph distances over unordered pairs of distinct vertices,
encoded as the non-diagonal elements of the symmetric square. -/
noncomputable def wienerIndex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Sym2 V)).filter (fun p => ¬ p.IsDiag),
    Sym2.lift ⟨G.dist, fun u v => G.dist_comm (u := u) (v := v)⟩ p

/-- Number of `2 x 2` integer matrices with entries in `{1,...,n}` and
determinant `2n`, using the row-major quadruple dictionary `(a,b,c,d)`
for `[[a,b],[c,d]]` and determinant `a*d-b*c`. -/
def matrixCount (n : ℕ) : ℕ :=
  let entries := Finset.Icc (1 : ℤ) (n : ℤ)
  ((entries ×ˢ (entries ×ˢ (entries ×ˢ entries))).filter
    (fun q => q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 2 * (n : ℤ))).card

/-- The literal 2012 OEIS conjecture, with `A192023(n-2)` interpreted by
its defining comb graph Wiener index rather than by a closed formula. -/
def claim : Prop :=
  ∀ n : ℕ, 2 < n → wienerIndex (comb (n - 2)) = matrixCount n

/-- At the first allowed input, `n=3`, the comb has Wiener index one,
but exactly two matrices have entries in `{1,2,3}` and determinant six. -/
theorem result : ¬ claim := by
  have hpairs :
      (Finset.univ : Finset (Sym2 (Fin 1 ⊕ Fin 1))).filter (fun p => ¬ p.IsDiag) =
        {s(Sum.inl 0, Sum.inr 0)} := by decide
  have hwiener : wienerIndex (comb 1) = 1 := by
    change (∑ p ∈ (Finset.univ : Finset (Sym2 (Fin 1 ⊕ Fin 1))).filter
      (fun p => ¬ p.IsDiag), Sym2.lift _ p) = 1
    rw [hpairs, Finset.sum_singleton, Sym2.lift_mk]
    apply SimpleGraph.dist_eq_one_iff_adj.mpr
    simp [comb, SimpleGraph.fromRel, Sum.elim]
  have hcount : matrixCount 3 = 2 := by decide
  intro hclaim
  have hbad : wienerIndex (comb 1) = matrixCount 3 := hclaim 3 (by decide)
  have hneq : (1 : ℕ) ≠ 2 := by decide
  exact hneq (hwiener.symm.trans (hbad.trans hcount))

#print axioms comb
#print axioms wienerIndex
#print axioms matrixCount
#print axioms claim
#print axioms result

end D5.S0.Certificates.KimberlingCombWienerDeterminantRefutation
