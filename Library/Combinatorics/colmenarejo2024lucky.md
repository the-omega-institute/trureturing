---
bibkey: colmenarejo2024lucky
authors: Laura Colmenarejo, Aleyah Dawkins, Jennifer Elder, Pamela E. Harris, Kimberly J. Harry, Selvi Kara, Dorian Smith, Bridget Eileen Tenner
year: 2024
title: "On the lucky and displacement statistics of Stirling permutations"
doi: 10.48550/arXiv.2403.03280
url: https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html
claim: "Corollary 41 bounds the number of nonzero entries of a displacement composition between n and 2n-1, and Problem 48 asks whether every count in that range is attained."
strata_touched:
  - D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum
license: citation-only
triage: anchor
---

# Colmenarejo--Dawkins--Elder--Harris--Harry--Kara--Smith--Tenner lucky and displacement statistics

## Verified locator

URL: https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html

DOI: 10.48550/arXiv.2403.03280

Version: *Journal of Integer Sequences* **27** (2024), Article 24.6.7. The
preprint arXiv:2403.03280v1, which has no later version, carries the same text
but numbers the problems of its last section 1 through 6 rather than 43 through
51, and its Table 2 runs to order eight rather than seven. The numbering below
is the journal numbering, so the version is load bearing. The eight authors and
the title match both records.

## Definitions

Definition 4 reads:

> A permutation of the multiset {1, 1, 2, 2, 3, 3, . . . , n, n} is a Stirling
> permutation of order n if every value j appearing between the two instances of
> i satisfies j > i.

`Q_n` denotes the set of Stirling permutations of order `n`, written as a word
`w(1) w(2) ⋯ w(2n)`. Such a word is read as a parking preference list on `2n`
spots: car `i` drives to spot `w(i)` and takes the first free spot at or after
it. Car `i` is lucky when it parks at `w(i)`, and `d(i)` is the spot it takes
minus `w(i)`. Definition 39 sets `dis(w) = (d(1), …, d(2n))`, the displacement
composition. So `d(i) = 0` exactly when car `i` is lucky, and the number of
nonzero entries of `dis(w)` is the number of unlucky cars.

## The statement in question

Corollary 41 reads:

> For every w ∈ Q_n, we have 1 ≤ |{i ∈ [2n] : d(i) = 0}| ≤ n.

Equivalently, the number of nonzero entries of `dis(w)` lies between `n` and
`2n - 1`. The article then says "The bound determined in Corollary 41, suggests
the following avenue of research" and states:

> Problem 48. Determine if, for i ∈ [n, 2n − 1], there exists w ∈ Q_n such that
> dis(w) has exactly i nonzero entries. Equivalently, can we always find a
> Stirling permutation with i unlucky cars?

The text immediately after Problem 48 points to Table 3 for the case `n = 3`,
and Problem 49 is posed as its follow-up: for `k ∈ [2, n - 1]`, count the
`w ∈ Q_n` whose displacement composition has `k` zero parts. Problem 49 asks for
the sizes of the fibres; Problem 48 asks only whether they are all nonempty.

## What the article already settles at the two ends

Theorem 13 gives `(n - 1)!` Stirling permutations whose displacement
composition has exactly one zero entry, and Corollary 45 gives `C_n` of them
with exactly `n` nonzero parts. So the two extreme counts `2n - 1` and `n` are
attained; Problem 48 is about the counts strictly between them.

Two further statements of the article constrain any answer. The displacement of
any Stirling permutation of order `n` sums to `n^2`, and the first entry of
`dis(w)` is always zero.

## Scope of the recorded answer

Every count in `[n, 2n - 1]` is attained. For `j` from `0` to `n - 1` take

    V(n, j) = (j+1)(j+1) (j+2)(j+2) ⋯ n n  j j (j-1)(j-1) ⋯ 1 1 ,

each value written twice in succession, the values above `j` ascending and the
values at most `j` descending. Equal letters are adjacent, so no value stands
between two equal letters and `V(n, j) ∈ Q_n`. Parking it leaves `j + 1` lucky
cars, hence `2n - j - 1` nonzero entries, and `j ↦ 2n - j - 1` carries
`[0, n - 1]` onto `[n, 2n - 1]`.

At `n = 3` the three words are `112233`, `223311` and `332211`, with
displacement compositions `(0,1,1,2,2,3)`, `(0,1,1,2,0,5)` and `(0,1,0,3,0,5)`;
each sums to `9 = 3^2`, as the article's displacement identity requires, and
they carry five, four and three nonzero entries.

## Bounded prior-resolution evidence

The journal article and the sole arXiv version were opened, together with
arXiv:2410.08057 (parking functions with a fixed set of lucky cars, which does
not treat Stirling permutations), arXiv:2507.17667 (symmetric decompositions and
Euler--Stirling statistics, which treats neither parking nor luck) and
arXiv:2508.13917. None records an answer to Problem 48, and no later version of
the article exists. Citation-index result pages were not reachable, so this is a
bounded negative finding and no worldwide priority claim is made.
