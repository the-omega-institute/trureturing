/- GID: D5/S0/Certificates/CiglerConjectureSevenFiveRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/CiglerConjectureSevenFiveRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/CiglerConjectureSevenFiveRefutation.claim; result=D5/S0/Certificates/CiglerConjectureSevenFiveRefutation.result; claim=D5/S0/Certificates/CiglerConjectureSevenFiveRefutation.claim
   digest: Refutes only the printed second line of (7.11), Conjecture 7.5 in arXiv:1801.05608v3, at k=n=1; literature-attested, new_counterexample_claimed=false. No claim that the intended proposition is false or its proof has a gap; no verdict on the first line or Conjecture 7.6 (the reported 7.6 counterexample was a transcription error). No priority claimed for the determinant values or identification of the printing error. -/

import D5.S0.Certificates.MotzkinConvolutionHankelRefutation
import D5.S0.Certificates.CatalanConjectureSevenRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.CiglerConjectureSevenFiveRefutation

open D5.S0.Certificates.MotzkinConvolutionHankelRefutation (hankel)
open D5.S0.Certificates.CatalanConjectureSevenRefutation (convolutionPower)

/-!
Johann Cigler, *Catalan numbers, Hankel determinants and Fibonacci polynomials*,
arXiv:1801.05608v3, printed page 30, Conjecture 7.5, equation (7.11):
"For k > 0 we have"
`D(kn,2k) = D(kn+1,2k) = (-1)^{n*binom(k,2)} (n+1)^{k-1},`
`D(2kn-1,2k) + D(2kn+2,2k) = -k(2k-3)(2n+1)^{k-1}.`
The rendered PDF pages 2, 26 and 30 were visually checked on 2026-09-10.
There is no printed k >= 2 restriction or lower bound on n.

Page 2 defines D(n,r) as the determinant of the n by n matrix with entries
C^(r)_(i+j), and calls C^(r)_m = r/(2m+r) * binom(2m+r,m) convolution powers
of Catalan numbers. The imported convolutionPower is exactly Cauchy
multiplication of Mathlib's Catalan sequence; hankel has the identical
unshifted i+j convention and empty determinant one. We reuse both definitions.
The coefficient owner is present but unfrozen at this lane's base; the hankel
owner is frozen. Natural subtraction totalizes the index at n=0; our witness
k=n=1 has positive indices 1 and 4, so no truncated subtraction is involved.

Independent exact checks used the printed binomial formula with Bareiss
elimination, and C=1+x*C^2 with Cauchy multiplication and the full Leibniz sum.
Both give coefficients 1,2,5,14,42,132,429, D(1,2)=1 and D(4,2)=1.
All 21 positive controls agree with printed formulas: D(m,2), 0<=m<=6;
Theorem 7.3's D(m,4), 0<=m<=7; and the page 30 D(m,8) list, 0<=m<=5.
All divisions were exact and no floating point was used.

Provenance is literature-attested; new_counterexample_claimed=false.
Pages 2 and 26 already print D(n,2)=1. At k=1 the FIRST line of (7.11)
on page 30 also implies the two determinant values; its SECOND line requires
their sum to be 1. Thus the obstruction is already implicit in this paper.
Only that printed second line at k=n=1 is refuted. We do not claim that the
author's intended proposition is false or its proof has a gap. We give no
verdict on the first line or Conjecture 7.6; the reported 7.6 counterexample
was a transcription error, not a counterexample. We claim neither first
discovery of the values nor first identification of this printing error.

The proof uses the existing definitions and kernel computation, with no
frozen numerical determinant theorem or external oracle. The finite
computations are local to result. Admission basis: escape-witness, section
3.2 form (2); the live numerical computation produces the refutation.
The refutes utility is separate from this three-way admission classification.
-/

/-- The entire printed second line: every positive natural k and every natural n.
The factor 2k-3 is evaluated in the integers, retaining its negative value at k=1. -/
def claim : Prop :=
  ∀ k : ℕ, 0 < k → ∀ n : ℕ,
    hankel (convolutionPower (2 * k)) (2 * k * n - 1) +
      hankel (convolutionPower (2 * k)) (2 * k * n + 2) =
        -(k : ℤ) * (2 * (k : ℤ) - 3) * (2 * (n : ℤ) + 1) ^ (k - 1)

set_option maxHeartbeats 2000000 in
-- The allowance covers 24 permutations and recursive Catalan/Cauchy coefficient evaluation.
set_option maxRecDepth 10000 in
/-- At k=n=1 the printed equality requires 1, while the two determinants sum to 2. -/
theorem result : ¬ claim := by
  intro h
  have det_one : hankel (convolutionPower 2) 1 = 1 := by
    decide +kernel
  have det_four : hankel (convolutionPower 2) 4 = 1 := by
    decide +kernel
  have required := h 1 (by decide) 1
  change hankel (convolutionPower 2) 1 + hankel (convolutionPower 2) 4 =
    -(1 : ℤ) * (2 * 1 - 3) * (2 * 1 + 1) ^ (1 - 1 : ℕ) at required
  rw [det_one, det_four] at required
  norm_num at required

#print axioms claim
#print axioms result

end D5.S0.Certificates.CiglerConjectureSevenFiveRefutation
