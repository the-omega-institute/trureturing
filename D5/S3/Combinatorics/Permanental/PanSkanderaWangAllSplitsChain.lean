/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: TNN minors and Bruhat chain steps decrease permutation monomials. -/

/- Mathematical classification: data and predicate definitions only.
   admission_basis: none (definition support for the all-split result)
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     none (the frozen PSW theorem is used through the supporting modules).
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic



open Finset Matrix Equiv

namespace PSW

/-- Every square minor with increasing rows and columns is nonnegative. -/
def TNN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, ∀ r c : Fin k ↪o Fin n, 0 ≤ (A.submatrix r c).det

/-- Permanent of the principal submatrix on the specified literal index set. -/
noncomputable def principalPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) : ℝ :=
  (A.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))).permanent

/-- Fin indices are zero-based, so `i+1` is the index printed in the paper. -/
def evenIndices (n : ℕ) : Finset (Fin n) := univ.filter (fun i => (i.val + 1) % 2 = 0)

def prefixIndices (n h : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val < h)

noncomputable def monomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Perm (Fin n)) : ℝ :=
  ∏ k, A k (w k)

end PSW
