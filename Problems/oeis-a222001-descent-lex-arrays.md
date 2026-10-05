---
slug: oeis-a222001-descent-lex-arrays
bibkey: hardin2013a222001
doi: null
url: https://oeis.org/A222001
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PermutationArrays/DescentLexCount
---

# Three-column permutation arrays with compatible row orders

## Problem

For every positive integer n, count the n by 3 arrays whose rows are
permutations of 1,2,3, whose downstep counts do not decrease down the rows,
and whose rows are lexicographically nonincreasing. Repeated rows are
allowed. OEIS A222001 publishes Colin Barker's conjectured answer
`2+(n+1)*(n+2)*(n+3)/6` and has offset `1,1`.

## Mathematical result

The six lexicographically increasing rows have descent counts
`0,1,1,1,1,2`. The two order requirements force a constant descent class.
The extreme classes each give one constant array; the middle class gives
all nonincreasing words of length n on its four actual permutations.
These are equivalent to length-n multisets on four symbols. Mathlib's
multiset cardinality theorem gives the binomial coefficient `choose(n+3,3)`
and hence the source cubic after adding the two constant arrays.

The native Lean endpoint is `DescentLexCount.count_arrays`, in
`D5/S3/Combinatorics/PermutationArrays/DescentLexCount.lean`. It quantifies
over every `n : ℕ` with `1 ≤ n` and counts the actual `Equiv.Perm (Fin 3)`
row arrays with literal adjacent descent and lexicographic predicates.
It assumes no recurrence or finite data agreement. At zero length the
actual count is one, and the displayed formula is inapplicable.

## Evidence limits

The Library note gives the exact source, source-symbol relabeling, carrier,
and counting suppliers. The observed source snapshot still labels the
formula a conjecture. Later or official status, model acceptance,
publication priority and worldwide uniqueness are unmeasured here.
Independent source and supplier reviews and canonical publication remain
separate obligations. Information-escape registration is unfinished under
the repository suspension; no declared-valid registration is claimed.
