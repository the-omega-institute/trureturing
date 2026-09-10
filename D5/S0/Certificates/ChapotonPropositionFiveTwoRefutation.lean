/- GID: D5/S0/Certificates/ChapotonPropositionFiveTwoRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/ChapotonPropositionFiveTwoRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/ChapotonPropositionFiveTwoRefutation.claim; result=D5/S0/Certificates/ChapotonPropositionFiveTwoRefutation.result; claim=D5/S0/Certificates/ChapotonPropositionFiveTwoRefutation.claim
   digest: Refutes only printed Proposition 5.2 in arXiv:2001.01449v1 at n=1, t=1; literature-attested, new_counterexample_claimed=false. No claim that the authors' intended proposition is false or its proof has a gap; P'_n=G_n is an interpretation, not the printed text. No verdict on Conjecture 5.4. No priority claimed for these values or for identifying the Q' to P' misprint. -/

import D5.S0.Certificates.ChapotonConjectureFiveFourRefutation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.ChapotonPropositionFiveTwoRefutation

open Polynomial
open scoped BigOperators
open D5.S0.Certificates.ChapotonConjectureFiveFourRefutation (rho)

/-!
Chapoton--Han, *On the roots of the Poupard and Kreweras polynomials*,
arXiv:2001.01449v1, printed page 8, Proposition 5.2:
"For every n >= 1, the polynomial Q'_n is the Kreweras polynomial G_n."
Rendered pages 2, 3, 7, 8 and 9 were checked on 2026-09-10. Equation (5.4)
defines Q', the next paragraph defines P'=Q'/(t-1), and the proposition
and proof nevertheless both print Q'. The published version, Moscow Journal
of Combinatorics and Number Theory 9 (2020), 163--172,
https://doi.org/10.2140/moscow.2020.9.163, retains exactly that Q' on page 171;
equation (5-4) and the vanishing assertion are on page 170, G_1=1+x on page 164.

The imported public rho is the fixed-index definition from section 5.1,
page 7: floor(d/2) iterations of N_0, then constant coefficient. The last
nonzero iterate is an operator on V_d, not the last nonzero value of each input.
The quotient in (5.4) has index 2n-1, even when its outer coefficients vanish.
For n=1 all three inputs use index 1 and therefore zero iterations. Thus
rho(1,c(1+x))=c is derived here, not cited as a separately printed equality.

Method A: integer coefficient arrays, monic long division, and (2.1) at D=0.
Method B: signed geometric sums for (5.4), symmetric-basis products from (2.2).
Both independently obtain coefficients [-1,0,1] for Q'_1. Each quotient is
checked by multiplication, with zero remainder. No floating point is used.
Controls (coefficient lists in ascending order; A and B both match):
 n  Q'_n                         P'_n = printed G_n (page 2)
 1  [-1,0,1]                     [1,1]
 2  [-2,-2,0,2,2]                [2,4,4,2]
 3  [-12,-12,-8,0,8,12,12]       [12,24,32,32,24,12]
 4  [-136,-136,-112,-64,0,64,112,136,136]
                                 [136,272,384,448,448,384,272,136]
The G controls also follow independently from (1.3) and (2.2) at D=2.
Section 5.1's example [1,1,1,1,1] -> [3,4,3] -> [4] matches. All 36 printed
entries of (5.6) match; these entries are controls only, no determinant verdict.
There are 1239 exact division checks and no control mismatches.

Only the printed proposition is refuted, using n=1,t=1. We do not claim that
the intended proposition is false or that its proof has a gap. P'_n=G_n is
the suggested reading, not a theorem asserted here for all n. No verdict on
Conjecture 5.4 is given. No priority for the values or the Q' to P' misprint
is claimed. The actual values are literature-attested by the printed G_1 and
Q'_n(1)=0 assertions; new_counterexample_claimed=false. No separate formal
erratum was located in the documented search scope as of 2026-09-10.

Mathlib plus the imported definitions and normalization suffice. No frozen
numerical theorem supplies this obstruction. Admission basis: escape-witness,
section 3.2 form (2), the result produced by the live computation below, as
specified in the implementation brief. Refutes is the separate use condition,
not a fourth admission basis. All finite equalities are proof-local.
-/

/-- Equation (5.4), including its fixed palindromic index 2n-1. -/
noncomputable def qPrime (n : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (2 * n + 1),
    C (rho (2 * n - 1) ((X ^ i - X ^ (2 * n - i)) /ₘ (X - 1))) * X ^ i

/-- The initial value and recurrence (1.3), iterated n-1 times for n>=1.
The total extension at n=0 is unused by the printed claim. -/
noncomputable def kreweras (n : ℕ) : ℚ[X] :=
  Nat.rec (1 + X)
    (fun k P => ((X ^ (2 * k + 5) + 1) * C (P.eval 1) -
      2 * X ^ 2 * P) /ₘ (X - 1) ^ 2) (n - 1)

/-- The full printed polynomial equality, with every n>=1 and no exclusion. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → qPrime n = kreweras n

/-- The computed value Q'_1(1)=0 contradicts G_1(1)=2. -/
theorem result : ¬ claim := by
  intro h
  have quotient_neg : ((1 - X ^ 2 : ℚ[X]) /ₘ (X - 1)) = -(1 + X) := by
    have factor : (1 - X ^ 2 : ℚ[X]) = (X - 1) * -(1 + X) := by ring
    rw [factor]
    exact Polynomial.mul_divByMonic_cancel_left _ (by simpa using monic_X_sub_C (1 : ℚ))
  have quotient_pos : ((X ^ 2 - 1 : ℚ[X]) /ₘ (X - 1)) = 1 + X := by
    have factor : (X ^ 2 - 1 : ℚ[X]) = (X - 1) * (1 + X) := by ring
    rw [factor]
    exact Polynomial.mul_divByMonic_cancel_left _ (by simpa using monic_X_sub_C (1 : ℚ))
  -- Index 1 means zero operator steps, including for the zero middle input.
  have rho_index_one (P : ℚ[X]) : rho 1 P = P.coeff 0 := by
    simp [rho]
  have q_one : qPrime 1 = X ^ 2 - 1 := by
    norm_num [qPrime, Finset.sum_range_succ, quotient_neg, quotient_pos, rho_index_one]
    ring
  have required := congrArg (Polynomial.eval (1 : ℚ)) (h 1 (by decide))
  rw [q_one] at required
  norm_num [kreweras] at required

#print axioms claim
#print axioms result

end D5.S0.Certificates.ChapotonPropositionFiveTwoRefutation
