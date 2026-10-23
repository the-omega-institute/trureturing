---
slug: oeis-a145110-granvik-redheffer-support-refutation
bibkey: granvik2008a145110
doi: null
url: https://oeis.org/A145110
triage: theorem
motivation_gids:
  - D5/S3/Arith/GranvikRedhefferSupport
---

# The A145110 conjectured Redheffer support counts

## Problem

OEIS A145110, NAME (verbatim):

> Number of elements in the Redheffer matrix that contribute to the Moebius function.

COMMENT conjecture line (verbatim):

> a(11) to a(30) are conjectured to be 11, 23, 13, 18, 19, 25, 17, 29, 19, 30, 26, 26, 23, 45, 27, 30, 32, 39, 29, 48. [From _Mats Granvik_, Dec 21 2008]

For `n≥2`, let `B_n` have rows and columns indexed by `1,…,n`. Its entry
is 1 exactly when `j=1` or `i` divides `j`, except that `B_n(n,n)=0`.
A position `(i,j)` contributes when there is a permutation `σ` of
`{1,…,n}` with `σ(i)=j` and `B_n(k,σ(k))=1` for every `k`. Let `a(n)`
be the number of such positions. Thus the conjecture is the conjunction
of the twenty displayed equalities, starting with `a(11)=11` and ending
with `a(30)=48`.

The entry's array for `n=8` is the transpose of this matrix convention and
contains 13 positions. At `n=1` the literal modified-matrix definition gives
0 against the entry's datum 1; that index is outside the conjectured list.

## Motivation

This is an explicit finite conjecture about a union of permutation supports.
It differs from counting contributing permutations and from evaluating their
signed sum. The usual Redheffer determinant is the Mertens function; changing
its last diagonal entry to zero gives the Möbius-function variant discussed
in A143104 and A008683. Determining its contributing positions isolates the
divisibility structure before cancellation of determinant terms.

## Gap

The pinned official A145110 export at commit
`72c53dd50967ac7166f7d31bf79be95174ec5bc6` and the current official GitHub
export both identify revision 7 and retain the conjectured values. The entry
records that N. J. A. Sloane moved these values from the data section to
comments. The direct OEIS endpoints returned HTTP 403, so the official GitHub
export supplies the checked text.

Wilf's versioned paper characterizes the contributing permutations of the
usual Redheffer matrix by division-chain cycles. Its first theorem counts
permutations by ordered factorizations; it does not state the cardinality of
the union of their matrix positions. The checked sources provide no
resolution of the twenty-value conjecture. This is a bounded source check,
not an exhaustive literature or publication-priority claim.

## Route

For every `n≥2`, the formalized count is

\[
a(n)=n-1+\sum_{d\mid n}\bigl(\tau(d)-1\bigr),
\]

where `τ(d)` is the number of positive divisors of `d`.

The last row forces `σ(n)=1` in every contributing permutation. The set of
divisors of `n` is preserved by the permutation. On the complementary set,
every permitted step is nondecreasing in its natural-number index. Assigning
weight zero to divisors and weight `k` to a nondivisor `k` gives nonnegative
weight increments whose sum is zero, since a permutation preserves the total
weight. Each increment therefore vanishes, and every nondivisor is fixed.

The contributing positions are consequently exactly three disjoint types:
the `n−2` diagonal positions other than `(1,1)` and `(n,n)`; the closing
position `(n,1)`; and the strict divisibility positions `(i,j)` with
`i<j` and `i` dividing `j` dividing `n`. Conversely, swap cycles along
`1→i→j→n→1`, with repeated endpoints omitted, provide witness
permutations for all strict divisibility positions. The transposition of
1 and `n` supplies the closing position and all the stated diagonal positions.
For each divisor `j` of `n`, precisely `τ(j)−1` smaller divisors can
precede it. Counting these positions proves the formula.

At `n=20`, the positive divisors are `1,2,4,5,10,20`, and the summands
`τ(d)−1` are `0,1,2,1,3,5`. The formula gives `19+12=31`, whereas the
conjecture requires 30.

## Falsifier

The conjecture includes `a(20)=30`, which contradicts the proved equality
`a(20)=31`. A derivation of the closed `claim` would therefore contradict
`result`. The support definition retains witness permutations of `B_20`;
counting permitted matrix entries alone would not establish the result.

## Evidence

- Source notes: `Library/Factorization/granvik2008a145110.md` and
  `Library/Factorization/wilf2004redheffer.md`.
- Formal module: `D5/S3/Arith/GranvikRedhefferSupport.lean`.
- The designated closed proposition is `claim : Prop`; the main theorem
  is `result : ¬ claim`. The module proves the support characterization
  and count for every `n≥2`, then derives `result` from the formula at
  `n=20`. A scoped Lean build checks these statements and proofs.
- Independent bipartite-matching computations for `2≤n≤30` reproduce
  the entry's `n=8` example and its data at `2≤n≤10`. They give 31 at
  index 20 and 25 at index 21, and agree with the other 18 conjectured
  values. These computations are supporting observations, not Lean proofs.

## Triage

Computed: precisely two of the twenty conjectured values differ from finite
matching counts: `a(20)` is 31 rather than 30, and `a(21)` is 25 rather than
26. The other eighteen values agree. The error has opposite signs at these
two indices, so a constant additive correction does not repair the list.

Proved: for every `n≥2`, the count is
`n−1+Σ_{d∣n}(τ(d)−1)`. It depends on strict divisibility pairs among the
divisors of `n`, together with the fixed diagonal positions and the closing
edge. The instance `a(20)=31` refutes the stated list. At 20 the eighteen
diagonal positions, one closing position and twelve strict-divisibility
positions total 31. The source supplies no derivation of its conjectured
value, so the cause of its numerical error is not identified.

Computed consequence: at 21 there are nineteen diagonal positions, one
closing position and five strict-divisibility positions, giving 25. The
comparison of all twenty values is supported by independent matching
computations; only the index 20 instance is needed for the formal refutation.
A position can occur in several contributing permutations but is counted
once. Neither the number of permutations nor their signed determinant sum
determines this union by itself.

Literature-attested: A143104 concerns the ambient Redheffer entries, and
A008683 records the Möbius function and the modified determinant. Correcting
the support counts changes neither sequence's defining statement, and
asserts no new bound on the Möbius or Mertens functions. Wilf's
ordered-factorization count concerns the number of determinant terms;
the support count asks which positions occur in at least one such term.

Open follow-ups include classifying the support after deleting other
diagonal entries, simultaneous diagonal deletions, and analogous support
counts for finite-poset Redheffer matrices. These extensions are outside the
proven characterization for the single deletion at `(n,n)`.

## ASSUMED-UNVERIFIED

The matching computations at indices other than 20 are supporting
observations and are not separate Lean theorem statements in this module.
The background determinant identities in A143104 and A008683 are cited
literature and are not re-proved here. Direct access to the live OEIS pages
was blocked by HTTP 403. Unindexed literature and source surfaces beyond the
cited official exports and Wilf's versioned paper remain unchecked; no
exhaustive novelty or publication-priority claim is made.
