---
slug: greedy-fibonacci-average-closed-form
bibkey: fried2025proofs
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/GreedyFibonacciAverageClosedForm.result
---

# Closed Form for the Greedy Fibonacci-Average Sequence

## Problem

Fried, *Journal of Integer Sequences* **28** (2025), Article 25.4.3, Section 6,
writes:

> As mentioned earlier, we observed the statement of the previous theorem while
> working on a conjecture stated in A248982, which is defined to be the sequence
> of distinct least positive numbers such that the average of the first `n` terms
> is a Fibonacci number. Let `(a_n)_{n≥1}` be this sequence. Refining the
> conjecture stated in A248982 regarding a closed-form formula for `(a_n)`, it
> seems that, for `n ≥ 10`, we have
>
>     a_n = nF(n/2 + 3) − (n − 1)F(n/2 + 2),  if n is even;
>     a_n = F((n+1)/2 + 2),                    otherwise.
>
> A proof of this likely proceeds along similar lines as the previous theorem.

Here `F(1) = F(2) = 1`. The sequence entry A248982 carries two further standing
conjectures, both recorded by Colin Barker on 2014-10-19 and both still labelled
`Conjecture`: that `a(n) = 2a(n−2) + a(n−4) − 2a(n−6) − a(n−8)` for `n > 17`, and
that `a(2n+1) = F(n+3)` for `n > 4`. An `Empirical g.f.` equivalent to the first
is recorded alongside them.

## Motivation

The frozen theorem `D5/S3/Arith/GreedyFibonacciAverageClosedForm.result` settles
the displayed formula for every `n ≥ 10`. Both of Barker's conjectures follow:
the odd-index one is the second line read at `n = 2k+1`, and the order-eight
recurrence holds because each branch, as a function of the half index, is a
linear combination of `F(j+c)` and `jF(j+c)` and so satisfies the square of the
Fibonacci recurrence.

## Gap

The source reaches the formula from the sequence entry and offers no line of
attack beyond the remark that a proof "likely proceeds along similar lines as the
previous theorem" — that theorem being a rounding-formula induction with no
Fibonacci content. The obstacle it does name is the one immediately before: it
could not show that the two families produced at even and at odd indices are
disjoint, which is what the greedy rule needs in order to reject a repeat.

## Route

Write `X_j = F(j+2) + 2jF(j+1)`, which is the even branch of the displayed
formula, since
`2jF(j+3) − (2j−1)F(j+2) = 2j(F(j+3) − F(j+2)) + F(j+2) = F(j+2) + 2jF(j+1)`.
Write `s_n` for the sum of the first `n` terms; the greedy rule says `s_n = nF(m)`
for the least admissible `m`, with the resulting increment unused.

The whole formula follows from the two-step induction

    s_{2j} = 2j·F(j+3)   and   s_{2j+1} = (2j+1)·F(j+3)   for every j ≥ 5,

whose base is `s_10 = 10·F(8) = 210`, the first ten terms being
`1, 3, 2, 6, 13, 5, 26, 8, 53, 93`.

At an odd index `2j+1` the least `m` with `(2j+1)F(m) > s_{2j}` is `j+3`: a
smaller one fails because `(2j+1)F(j+2) ≤ 2jF(j+3)`, which reduces through the
recurrence to `F(j) ≤ (2j−1)F(j+1)`. The value is then `F(j+3)`.

At the following even index `2j+2` the choice `m = j+3` returns `F(j+3)` again,
which the distinctness condition rejects because it was just used. A smaller `m`
fails because `(2j+2)F(j+2) ≤ (2j+1)F(j+3)`, which reduces to `F(j) ≤ 2jF(j+1)`.
So `m = j+4` and the value is `(2j+2)F(j+4) − (2j+1)F(j+3) = X_{j+1}`.

Distinctness is where the frozen theorem
`D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result` enters: no `X_i` with
`i ≥ 1` is a Fibonacci number, so the even-index family never meets the
odd-index one. Within each family distinctness is monotonicity: `F` increases
from index three, and `X` increases because both of its summands do. The first
nine terms are excluded by size — `F(j+3) ≥ F(8) = 21` and `X_{j+1} ≥ X_6 = 177`,
while the only values among the first nine that are at least 21 are `26`, `53`
and `93`, none of them Fibonacci numbers.

## Falsifier

A single `n ≥ 10` at which the greedy rule departs from the displayed formula
refutes it. Inside the recorded proof the argument fails if some `X_i` is a
Fibonacci number, if `F(j) > (2j−1)F(j+1)` for some `j`, or if the tenth partial
sum differs from `210`.

## Evidence

A direct simulation of the greedy rule reproduces all 44 terms listed at A248982.
Against the displayed closed form it disagrees at exactly `n = 1, …, 9` and
agrees at every `n` from 10 through 80, which is the threshold the source states.
Barker's order-eight recurrence holds at every `n` from 18 through 80 and
`a(2n+1) = F(n+3)` at every `n ≥ 5`. The first value the closed form produces is
`a_10 = X_5 = F(7) + 10F(6) = 13 + 80 = 93`, the tenth term of the entry.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9397
before the module was written. The admission basis is `escape-witness` with
`proof_shape: content`; the declared escape content is the totality of the greedy
rule, the closed values of the partial sums, the two inequalities that exclude
smaller Fibonacci averages, the membership analysis that rules out repetition,
and the two greedy steps with their induction. The computational use is `none`:
the delivered statement is a universally quantified theorem with no bounded
enumeration, checker, numeric reduction or certified instance among its
declarations.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the journal article and its abstract page, the
sequence entry A248982 with its two standing conjectures, and the withdrawn
preprint arXiv:2509.26138 were opened. The entry links exactly two texts, Fried's
own preprint arXiv:2410.07237 — which states the formula as a conjecture — and
that withdrawn preprint. An arXiv full-text query for the sequence identifier
returned nothing further. The *Journal of Integer Sequences* assigns no DOI and
citation-index result pages were not reachable, so no worldwide priority claim is
made.

The `Empirical g.f.` recorded at the entry is stated there as empirical; it is
equivalent to Barker's order-eight recurrence together with the initial terms,
and only the recurrence is addressed here.
