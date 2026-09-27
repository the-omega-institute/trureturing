---
bibkey: ribenboim2005squareclasses
authors: Paulo Ribenboim
year: 2005
title: "FFF: (Favorite Fibonacci Flowers)"
doi: null
url: https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf
claim: "Statement (3.4) records the complete positive Fibonacci square classes; GSE uses its prime-power and ratio-25 consequences, not a newly assumed rigidity theorem."
strata_touched: []
license: citation-only
triage: anchor
---

# Square-class rigidity and explicit original-depth support bounds

## Exact classical source and scope

Paulo Ribenboim, *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly
43(1) (2005), 3-14. Statement (3.4), printed page 8, says that the only
nonsingleton positive-index square classes of Fibonacci values are
{1,2,12} and {3,6}. Reference [20] attributes this to the author's
*Square Classes of Fibonacci and Lucas Numbers*, Portugaliae Mathematica
46 (1989), 159-175. The 1989 paper's bibliographic record was verified;
its full proof was not independently read in this pass. The actual 2005
statement was read in parsed primary text. Requested images of its pages
8 and 9 failed; no successful visual-page check is claimed.

Statements (3.7)-(3.8), printed page 9, record a classical effective
fixed-squareclass bound and a finite closure under prime factors of the
entry ranks. The closure operation and general effective finiteness are
therefore prior work. Neither is counted as a new invention of GSE.
No unproved abc statement from the same paper is used.

The valuation input is Lengyel's classical theorem, restated in
Medina-Rowland, *p-regularity of the p-adic valuation of the Fibonacci
sequence*, Theorem 1.4, arXiv:0910.2907v4. Its original first-zero depth
is retained; its formulas for two and five are used separately.
The prime number theorem is used only for the final asymptotic corollary,
not for the exact divisor bound or finite procedure. The standard
prime-counting form is recorded by NIST DLMF Section 27.12:
https://dlmf.nist.gov/27.12 . Partial summation and removal of higher
prime powers give the equivalent Chebyshev form psi(x)~x.

## Consumer and actual addition

Section 10 (GSE) of
`docs/develop/theory/GOLDEN_CUBIC_BLOCK_PRIME_PERIODS.md` proves:

- for a finite rank-closed prime set H containing {2,3,5}, the condition
  that the squarefree kernel of F_n is supported in H forces
  n | 5*lcm_(p in H) rho(p);
- the same explicit divisor bound for the original external odd-depth
  support U(n) contained in a prescribed finite set S, using the existing
  OSE support descent in the migrated Andrejic companion;
- a finite divisor-enumeration procedure using exact square roots of the
  residual after removing H-prime factors, without full factorization
  of every large Fibonacci value;
- the uniform escape condition n not dividing 10*lcm(1,...,Y), where
  Y=max(5,floor((Q+1)/2)), forces an external odd-original-depth prime
  greater than Q. It is an odd-depth WSS prime only with the additional
  powerful-Fibonacci antecedent.

The proof combines nonsquare prime-power quotients with parity
cancellation in Q_positive^times modulo squares at the prime five.
The latter requires preserving rank-divisibility thresholds and uses
square-class rigidity at the ratio 25. The map n -> [F_n] is not treated
as a group homomorphism. PBC.3 already contains the nonsquare quotient
mechanism for primes at least seven; GSE retains that attribution and
checks two, three and five separately to obtain the explicit cutoff.
Global first-discovery priority for this bound has not been established.

## Recent Erdos methods: inspiration, not imported hypotheses

The curator's Problem 936 concerns finiteness of powerful values among
2^n+/-1 and n!+/-1:
https://www.erdosproblems.com/936 . The retrieved page is marked open,
last edited 31 October 2025, and records abc-conditional results. The
indexed copy is not represented as a new September 2026 status audit.
The exponential branch shares the multiplicity/first-lift issue with
Fibonacci WSS. No reduction solving one problem through the other is
asserted.

The primary repository `tadamcz/erdos126`, README blob
`ef92c4278100cf0063424710b4c352e5c2e31df6`, describes recently verified
proofs for the number of prime divisors of pairwise sums. Its accounts
use prime-power residues, negation orbits, signed kernels, and matching
or collision budgets to produce polynomial bounds. The README and its
statement/provenance were read; those Lean files were not recompiled
or imported here. The useful methodological comparison is to turn local
prime data into an actual global bound, beyond merely counting abstract
characters. No specific inequality from Erdos126 is a GSE premise.

Nat Sothanaphan, *Resolution of Erdos Problem #728: a writeup of
Aristotle's Lean proof*, arXiv:2601.07421v2:
https://arxiv.org/html/2601.07421v2 . Sections 3-4 reduce factorial
quotients to prime-by-prime valuations and use carry bounds and spike
control. This suggests preserving the exact bad valuation event rather
than replacing it with a coarse density analogy. That theorem is also
context only, with no factorial-to-WSS reduction.

## Formalization handoff and evidence boundary

The actual PR source already has FiniteFibonacciRankClosure,
FibonacciPrimeToIndexValuation and OriginalOddDepthSupport. The last
source displays its prime-index odd-factor premise explicitly. GSE's
square-class rigidity is a separate classical prerequisite, not already
proved by those Lean endpoints. A useful order of further formal work is:
prime-power quotient cancellation and its odd witness; the ratio-25
parity transport with rank thresholds; the exponent bounds n|5R_H;
then the uniform lcm and finite-set consequences.

No Lean source, frozen marker, atom coverage, or CI claim is added by
this note. Existing parallel scalar-contraction work in theory Section 9
is preserved. The new ordinary deductions do not produce a WSS prime,
decide a previously unknown WSS prime family, or exclude the entire
P^2Q^3 branch. Finite arithmetic certificates are supplemental to the
written general proof; synthetic higher depths are never WSS examples.
