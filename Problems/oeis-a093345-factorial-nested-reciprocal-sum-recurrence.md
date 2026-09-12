---
slug: oeis-a093345-factorial-nested-reciprocal-sum-recurrence
bibkey: mathar2014a093345
doi: null
url: https://oeis.org/A093345
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence
---

# Mathar's recurrence for the A093345 factorial nested reciprocal sum

## Problem

OEIS A093345, NAME (%N, verbatim):

> a(n) = n! * {1 + Sum[i=1..n, 1/i*Sum(j=0..i-1, 1/j!)]}.

COMMENT (%C, verbatim):

> Number of {12,2*1}-avoiding signed permutations in the hyperoctahedral group B_n.

FORMULA (%F, Jovovic, verbatim):

> E.g.f.: (exp(1)*(Ei(1, 1-x)-Ei(1, 1))+1)/(1-x). a(n) = n!*(1+Sum(A000522(i-1)/i!, i =1..n)). - _Vladeta Jovovic_, Apr 27 2004

FORMULA (%F, Mathar, verbatim; the sole conjecture targeted here):

> Conjecture: a(n) -2*n*a(n-1) +(n^2-2)*a(n-2) -(n-2)^2*a(n-3)=0. - _R. J. Mathar_, May 30 2014

The cited Mansour-West paper, *Avoiding 2-letter signed patterns* (2002),
Theorem 2.2 and equation (2.4), proves the enumeration by the nested sum,
not this third-order recurrence. The generating-function line supplies
context, not a separate resolution target. The entry has offset zero.

## Motivation

The conjecture gives a fixed-order recurrence for the factorial nested
reciprocal sum. The result applies at every natural index `n >= 3`, rather
than only to a finite list of sequence values.

## Gap

On 2026-09-13 the search and probe seats checked the current OEIS entry and
all 16 revisions; Mansour-West (arXiv:math/0207204); the zbMATH forward
citation surface for document 2041487, returning Goyt-Pudwell (2011,
arXiv:1103.0239); and identifier searches on the arXiv website,
MathOverflow API, GitHub unauthenticated code/commit search and Crossref.
The recurrence's proof or refutation was not found in the checked surfaces.
OpenAlex was not checked because of quota, and the arXiv export API timed
out. This is the bounded search report supplied in issue #7381, not an
exhaustive literature or first-publication-priority claim. Stage B directly
read the current OEIS internal entry on 2026-09-13 and confirmed the quoted
lines and revision #16; it did not repeat the full historical search.

## Route

Define the auxiliary prefix `b(m) = m! * Sum(j=0..m, 1/j!)`. Peeling off its
last term gives `b(m+1) = (m+1)*b(m) + 1`. Peeling off the outer sum's last
term gives `a(m+1) = (m+1)*a(m) + b(m)`. The latter uses `b(m)`, not
`b(m+1)`: the inner sum ends at `j=m` and the cancelled factor leaves `m!`.
Three consecutive updates for `a` and two for `b` eliminate the prefix;
rational algebra then gives the third-order recurrence for `n >= 3`.
The prefix and both updates remain local inside the proof.

## Falsifier

A natural index `n >= 3` at which the quoted recurrence's left-hand side
is nonzero for the exact NAME nested sum would refute the conjecture.
Failure of source-to-definition identification would invalidate the claimed
resolution. Finite exact computations support the identification but do not
replace the universal proof. All coefficients are rational; index
subtraction is natural subtraction, without truncation under `3 <= n`.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.lean`.
- Main theorem: `mathar_a093345 (n : Nat) (hn : 3 <= n)`.
- Public definition: `a : Nat -> Rat`, the NAME nested sum with outer
  `Finset.Icc 1 n` and inner `Finset.range i`.
- The probe reports std3: `propext`, `Classical.choice`, `Quot.sound`.
  The implementation also obtains the axiom closure through the canonical
  Lean report. No integrality theorem or public auxiliary is declared.
- Orchestrator-supplied exact rational check: all 120 terms at `0 <= n < 120`
  were integers, with initial values `1, 2, 6, 23, 108, 605, 3956`;
  zero recurrence mismatches at the 117 indices `3 <= n < 120`.
- Probe-supplied evidence: the same exact check at `n < 120` and a SymPy
  expansion of the elimination identity. These finite computations are
  supporting observations, not the universal theorem.
- Stage-B independent exact rational computation on 2026-09-13 reproduced
  all 120 integral terms and all 117 zero recurrence residuals, including
  the seven initial values above. It also checked `a(1)=a(0)+b(0)=2`, while
  the incorrectly shifted `a(0)+b(1)` is 3.

## Triage

`theorem`. The formal statement proves the complete Mathar recurrence
for the rational-valued NAME sequence, at every natural index at least three.

## ASSUMED-UNVERIFIED

The current OEIS quotations and attribution were directly read by Stage B.
The prior historical and literature-search results and the orchestrator's
and probe's numerical checks are supplied evidence. Stage B independently
repeated the exact rational finite check, but not the SymPy elimination.
Stage B did not read either cited paper or the full revision
history. No exhaustive literature or priority claim follows. The
signed-permutation interpretation, generating function and integrality are
not formalized here. Natural-language source-to-Lean identification is not
itself kernel-checked.
