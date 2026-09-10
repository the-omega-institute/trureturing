/- GID: D5/S0/Certificates/ChapotonConjectureFiveFourRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/ChapotonConjectureFiveFourRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Div, mathlib/module/Mathlib.Data.Nat.Factorial.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/ChapotonConjectureFiveFourRefutation.claim; result=D5/S0/Certificates/ChapotonConjectureFiveFourRefutation.result; claim=D5/S0/Certificates/ChapotonConjectureFiveFourRefutation.claim
   digest: Refutes only printed equation (5.5), Conjecture 5.4 in arXiv:2001.01449v1, at n=2; literature-attested, new_counterexample_claimed=false. No claim that the authors' intended proposition is false or its proof has a gap; the corrected version proved in later literature is outside scope. No verdict on Proposition 5.2. No priority claimed for the determinant value or identification of this off-by-one. -/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.ChapotonConjectureFiveFourRefutation

open Polynomial
open scoped BigOperators

/-!
Chapoton and Han, *On the roots of the Poupard and Kreweras polynomials*,
arXiv:2001.01449v1, printed page 9, Conjecture 5.4, equation (5.5):
"For all n >= 0", with entries indexed by "0 <= i <= n and 0 <= j <= n".
Thus the literal matrix has order n+1. The immediately following (5.6),
labelled M_6, prints six rows and six columns: these conventions disagree.
The preceding "Assuming this conjecture" refers to Conjecture 5.3 (divisibility),
not to a restriction on n. Rational entries implement the printed scaling
without presupposing that global divisibility conjecture; every division at
the witness is exact. No n=2 exclusion is added to claim.

The index of x^i(1+x)^j is 2i+j, not its degree i+j (page 2).
Equation (2.1) at D=0 defines nzero below. Section 5.1, page 7, defines rho
as the constant term after the last nonzero operator iterate on the fixed
index space: floor(d/2) steps. The index remains explicit even when outer
coefficients vanish. In particular rho(1)=1 and rho(c(1+x))=c, since index
0 or 1 requires zero steps. rho is not treated as globally linear on Q[x].
The rendered source pages 2, 3, 7 and 9 were checked on 2026-09-10.

Independent integer reconstructions used (2.1) with monic polynomial long
division and the Leibniz determinant, and (2.2) with symmetric-basis geometric
products and Bareiss elimination. All 36 entries of (5.6) match. Additional
controls are d_0=d_1=1, the printed order-six determinant 2751882854400,
and the page 7 iterate example. All 770 divisions have verified zero remainder.
The witness gives rho values [1,1,2; 1,2,6; 2,8,36]; after scaling columns
by [1,1,1/2], its determinant is 4, while (5.5) at n=2 is (1!)^2=1.

Literature-attested correction: Guo-Niu Han, *Dilated Hankel determinants*,
arXiv:2607.08279v1, section 26, pages 80-84. Equation (26.2) explicitly uses
an N by N matrix, 0 <= i,j <= N-1. Theorem 26.1, equation (26.4), proves
the factorial product for N>=1; its proof is on page 84. Remark 26.4 also
proves the divisibility. This silently corrects the earlier indexing; it
does not explicitly claim to identify an erratum. new_counterexample_claimed=false.
Only printed (5.5) at n=2 is refuted. We do not claim the authors' intended
proposition is false or its proof has a gap. The later corrected theorem is
outside scope. Proposition 5.2 is a separate question and receives no verdict.
Neither first discovery of this determinant value nor first identification
of the off-by-one is claimed.

Mathlib plus the definitions and normalization suffice; no frozen theorem
or external oracle supplies the numerical fact. Admission: escape-witness,
section 3.2 form (2), the public result produced by its live numerical
computation. The refutes utility is separate from that three-way basis.
-/

/-- Equation (2.1) with D=0, on a polynomial of fixed palindromic index d. -/
noncomputable def nzero (d : ℕ) (P : ℚ[X]) : ℚ[X] :=
  ((X ^ d + 1) * C (P.eval 1) - 2 * P) /ₘ (X - 1) ^ 2

/-- Section 5.1's final constant term after floor(d/2) index-lowering steps.
This total definition is used only at the polynomial's specified index. -/
noncomputable def rho : ℕ → ℚ[X] → ℚ
  | 0, P => P.coeff 0
  | 1, P => P.coeff 0
  | d + 2, P => rho d (nzero (d + 2) P)

/-- The entry formula, with the fixed index 2i+j and rational scaling. -/
noncomputable def entry (i j : ℕ) : ℚ :=
  rho (2 * i + j) (X ^ i * (1 + X) ^ j) / 2 ^ (j / 2)

/-- The printed inclusive bounds produce an (n+1) by (n+1) matrix. -/
noncomputable def printedMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  Matrix.of (fun i j => entry i.val j.val)

/-- Equation (5.5), with factors indexed by k=1,...,n-1 and empty product one. -/
def printedProduct (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.Ico 1 n, (Nat.factorial (n - k) : ℚ) ^ (if k % 2 = 1 then 2 else 4)

/-- The full printed universal assertion, including every natural n>=0. -/
def claim : Prop :=
  ∀ n : ℕ, Matrix.det (printedMatrix n) = printedProduct n

-- This private wrapper reuses Mathlib's exact monic-division cancellation.
-- Each concrete numerator identity below is independently checked by ring.
private theorem nzero_eq (d : ℕ) (P Q : ℚ[X])
    (h : (X ^ d + 1) * C (P.eval 1) - 2 * P = (X - 1) ^ 2 * Q) :
    nzero d P = Q := by
  unfold nzero
  rw [h]
  exact Polynomial.mul_divByMonic_cancel_left Q
    (by simpa using (monic_X_sub_C (1 : ℚ)).pow 2)

/-- The n=2 specialization requires 1, but its definition gives determinant 4. -/
theorem result : ¬ claim := by
  intro h
  have s02 : nzero 2 ((1 + X) ^ 2) = 2 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s10 : nzero 2 X = 1 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s11 : nzero 3 (X * (1 + X)) = 2 + 2 * X := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s12 : nzero 4 (X * (1 + X) ^ 2) = 4 + 6 * X + 4 * X ^ 2 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s12b : nzero 2 (4 + 6 * X + 4 * X ^ 2) = 6 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s20 : nzero 4 (X ^ 2) = (1 + X) ^ 2 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s21 : nzero 5 (X ^ 2 * (1 + X)) = 2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s21b : nzero 3 (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3) = 8 + 8 * X := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s22 : nzero 6 (X ^ 2 * (1 + X) ^ 2) =
      4 + 8 * X + 10 * X ^ 2 + 8 * X ^ 3 + 4 * X ^ 4 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s22b : nzero 4 (4 + 8 * X + 10 * X ^ 2 + 8 * X ^ 3 + 4 * X ^ 4) =
      26 + 36 * X + 26 * X ^ 2 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have s22c : nzero 2 (26 + 36 * X + 26 * X ^ 2) = 36 := by
    apply nzero_eq
    norm_num [map_ofNat]
    ring
  have det_two : Matrix.det (printedMatrix 2) = 4 := by
    change Matrix.det (Matrix.of (fun i j : Fin 3 => entry i.val j.val)) = 4
    rw [Matrix.det_fin_three]
    norm_num [entry, rho,
      s02, s10, s11, s12, s12b, s20, s21, s21b, s22, s22b, s22c]
  have required := h 2
  rw [det_two] at required
  norm_num [printedProduct] at required

#print axioms claim
#print axioms result

end D5.S0.Certificates.ChapotonConjectureFiveFourRefutation
