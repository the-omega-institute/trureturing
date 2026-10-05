---
slug: oeis-a222001-descent-lex-arrays
bibkey: hardin2013a222001
doi: null
url: https://oeis.org/A222001
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays
---

# Three-column permutation arrays with compatible row orders

## Problem

For each positive integer `n`, count the actual `n` by 3 arrays whose rows are
permutations of `1,2,3`, whose adjacent-descent counts are nondecreasing along
the original row indices, and whose rows are lexicographically nonincreasing.
Rows may repeat. In the source carrier a row is `Equiv.Perm (Fin 3)` and the
source symbol in column `j` is `(r j).val + 1`, so the carrier is exactly the
six permutations of `1,2,3`. OEIS A222001 gives the formula
`2+(n+1)*(n+2)*(n+3)/6` with offset `1,1`.

## Motivation

The sequence was recorded by R. H. Hardin in 2013, and the displayed formula
is attributed to Colin Barker in 2018. The OEIS entry records that formula
under its Conjectures heading. The exact formal target is the compiled theorem
`D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays`, whose
motivation is this source count on the actual array carrier.

## Gap

The formal question is the all-positive-length cardinality of this carrier, not
an extrapolation from a finite prefix and not a recurrence or generating
function claim. The theorem supplies that exact cardinality while retaining the
source order predicates and allowing repeated rows.

## Route

In increasing lexicographic order the six rows are `123,132,213,231,312,321`,
with descent counts `0,1,1,1,1,2`. Lexicographic decrease makes the descent
count nonincreasing, while the source condition makes it nondecreasing, so the
count is constant along every array. The zero- and two-descent classes contain
only `123` and `321`, giving two distinct constant arrays when `n` is positive.
The one-descent class contains `132,213,231,312`; its admissible arrays are
exactly nonincreasing words on these four rows. Taking the multiset of their
entries and sorting it in decreasing order are inverse constructions, including
all repetitions. Thus the actual array carrier is equivalent to the disjoint
sum of two points and `Sym (Fin 4) n`. Mathlib's symmetric-multiset
cardinality and descending-factorial identities give the displayed cubic.

## Falsifier

The equality is scoped to `n ≥ 1`, to three columns, to actual permutation rows,
and to the two stated order predicates. Changing the carrier, imposing
row-distinctness, or changing either order condition would be a different
statement. At `n = 0` the actual carrier has one empty array, whereas the
displayed cubic evaluates to three, so the positive-length hypothesis cannot be
removed.

## Evidence

The endpoint is the Lean theorem
`D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays`:
for every `n : ℕ` with `1 ≤ n`,
`Nat.card (Arrays n) = 2 + (n + 1) * (n + 2) * (n + 3) / 6`.
`Arrays n` is defined from actual `Equiv.Perm (Fin 3)` rows and literal adjacent
descent and lexicographic predicates. The proof's decomposition and its
Mathlib counting and sorting suppliers are described in
`Library/PermutationPatterns/hardin2013a222001.md`; the source citation is OEIS
A222001.

## Triage

**Proved (formalized):** The native `count_arrays` endpoint counts the actual
`Arrays n` carrier for every `n ≥ 1`, allowing repeated permutation rows and
retaining both stated order predicates.

**Proved (formalized):** The constant-descent-class argument is the decisive
mechanism. The middle class is counted by a multiset equivalence, so repeated
rows retain their multiplicity.

**Proved (transient independent Lean boundary check):** At `n = 0` the actual
carrier has one empty array, while the displayed cubic evaluates to three.
This boundary check is not a new public endpoint.

**Open:** Analogous counts for longer column widths are not established here.

## ASSUMED-UNVERIFIED

The source note records the cited OEIS state and attribution only. Later
literature status, official acceptance, model acceptance, publication priority,
and worldwide uniqueness are unverified here, and no such claim is made.
Information-escape registration remains unfinished under the repository
suspension; no valid registration or delivery status is asserted.
