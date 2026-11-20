---
slug: norton-threshold-differences
bibkey: berizelinsky2025norton
doi: 10.48550/arXiv.2505.08160
url: https://arxiv.org/abs/2505.08160v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.result
---

# The separation of Norton and perturbed thresholds

## Problem

Beri and Zelinsky, arXiv:2505.08160v2, page 8:

> Question 6. Is lim_{n→∞} a(n) − KS(n) = ∞?

Let p_n be the n-th prime, n≥1 and p_1=2. For α>1 define

$$
a_\alpha(n)=\min\left\{k\ge1:
  \prod_{r=n}^{n+k-1}\frac{p_r}{p_r-1}>\alpha\right\},\qquad a=a_2.
$$

Define KS(n) by replacing each factor with p_r/(p_r−1)+1/p_r² and
keeping the strict threshold 2. The target is convergence of the integer
difference a(n)−KS(n) to positive infinity. The positive-index definitions
and strict inequality are part of the statement.

## Motivation

The added factor is locally of order p⁻². Its cumulative logarithmic mass
can still advance the crossing by an unbounded number of primes because
the individual increments near the crossing are much smaller.

## Gap

The necessary comparisons concern the same starting prime and both actual
first-crossing endpoints. A tail estimate without a finite upper cutoff,
or endpoint estimates with an uncontrolled power loss, do not establish
the required separation.

## Route

The following paper argument describes the full comparison mechanism.
Its one-sided estimates suffice for the proved convergence. Write P=p_n,
A=p_{n+a(n)-1}, B=p_{n+KS(n)-1}, and

$$
w(q)=\log\frac q{q-1},\qquad
d(q)=\log\left(1+\frac{q-1}{q^3}\right).
$$

The perturbed logarithmic increment is exactly w(q)+d(q). Positivity
gives KS(n)≤a(n) and B≤A. Divergence of the prime reciprocal sum gives
existence of both crossings. Mertens' third error has the exact identity

$$
\sum_{q\le x\atop q\ {\rm prime}}w(q)
 =\log\log x+\gamma-E_3(x),\qquad E_3(x)=O(1/\log x).
$$

Subtracting two prefixes, with the starting prime included, therefore gives

$$
\sum_{P\le q\le x\atop q\ {\rm prime}}w(q)
 =\log\frac{\log x}{\log P}+O(1/\log P),\qquad x\ge P.
$$

At a first crossing the excess is positive and at most the last increment.
Moreover d(q)≍q⁻² and the full perturbation tail is O(1/P). These facts
give log A=2 log P+O(1) and log B=2 log P+O(1), hence A≍B≍P².

Let E_P(B) be the sum of d(q) over P≤q≤B. The finite prime-square-tail
estimate gives E_P(B)≍1/(P log P). In particular its lower bound retains
the actual finite endpoint B≍P²; it is not inferred from an infinite tail
without controlling the omitted primes. Writing u_A and u_B for the two
crossing excesses gives the exact relation

$$
\sum_{B<q\le A\atop q\ {\rm prime}}w(q)
 =E_P(B)+u_A-u_B.
$$

Both excesses are O(P⁻²), which is negligible beside 1/(P log P).
Each summand in (B,A] is comparable to P⁻². The number of these primes
is exactly a(n)−KS(n), so

$$
a(n)-KS(n)\asymp\frac P{\log P}\longrightarrow\infty.
$$

## Falsifier

Replacing the strict threshold by a weak one changes the crossing
excess convention. A lower bound for the infinite perturbation tail alone
does not bound E_P(B) below. The O(P⁻²) endpoint errors must be compared
with 1/(P log P), and the count must use the common starting index n.

## Evidence

Preregistration #32081 and the source quotations are attributed to the
dispatcher. The dispatcher's bounded literature check covered the following
sources and results; no independent PDF or network verification was performed
in this repair:

- arXiv:2505.08160 has only v2 in the checked record; Question 6 remains
  stated there.
- Zelinsky (2021), Propositions 2 and 3, proves a(n+1)≥a(n)+1 and divergence
  of the first difference. These propositions give neither a leading
  asymptotic term nor a count of the attained values.
- Zelinsky (2023) poses the general threshold problem again and lists
  Conjecture 27.
- Norton (1961), *Acta Arithmetica* 6, 365–374, Theorem 4, gives asymptotics
  for a(n) and its terminal prime, but no adjacent-difference theorem.
- The repository search found no pre-existing dossier for these questions.

This bounded check reported no prior settlement of the three exact targets.
Independent verification of the issue and source PDFs, exhaustive literature
coverage and worldwide priority remain unverified.

`BeriZelinskyQuestion6.result` proves in Lean that the integer difference
a(n)−KS(n) tends to positive infinity. Its proof establishes existence of
both strict crossings and KS(n)≤a(n). It uses `Mertens.E₃.abs_le` and the
defining prefix identity in `D5/S3/Weil/Mertens/Third.lean`, together with
`PrimeSquareTail.prime_square_tail_uniform` in
`D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail.lean`. The latter estimates
the finite sum over y<q≤z uniformly for z≥C y, with leading scale
1/(y log y).

The finite perturbation sum E=E_P(B) satisfies E≥d/(P log P) for some d>0.
The perturbed endpoint satisfies B≥cP² for some c>0. With D=a(n)−KS(n),
exact cancellation and the KS crossing excess give E≤(2D+3)/B. Thus
dcP/log P≤2D+3, which proves the convergence without requiring a separate
two-sided asymptotic for D. The result and its public endpoint and adjacent
growth helpers have axiom closure contained in `propext`, `Classical.choice`
and `Quot.sound`.

## Triage

- **Proved in Lean:** `BeriZelinskyQuestion6.result` answers Question 6
  affirmatively. Both threshold functions are well-defined, and KS(n)≤a(n)
  lies on the proof's active path. Eventual strict separation follows from
  the limit; strict separation for every n is a different assertion.
- **Proved in Lean:** `norton_endpoint_bounds` gives
  p_{n+a_α(n)-1}≍p_n^α for every fixed α>1. The perturbed endpoint also
  satisfies B≍P². The convergence proof uses a finite perturbation lower
  bound at B and exact cancellation of the shared starting interval.
- **Proved in Lean:** `norton_adjacent_cancellation` gives a constant c>0
  such that 1+a_α(n+1)−a_α(n)≥c p_n^{α−1} eventually. The separate
  Conjecture 27 dossier states the resulting growth quantifiers.
- **Paper derivation, not separately formalized:** the full comparisons
  a(n)−KS(n)≍P/log P and 1+a_α(n+1)−a_α(n)≍p_n^{α−1} include upper
  bounds beyond the formal lower-bound argument.
- **Paper derivation, not formalized:** the sharper prediction is
  a(n)−KS(n)∼n. Comparability alone proves the question and does not
  supply this leading constant.
- **Computed, floating point:** a sieve through 50,000,000 gives 3,001,134
  primes. Cumulative `log1p(1/(p−1))` and
  `log1p(1/(p−1)+1/p²)` sums, with the first prefix strictly above the
  starting prefix plus log 2, give the following readings. They are
  numerical checks, not exact certificates or uniform asymptotic proofs.

  | n | p_n | a(n) | KS(n) | (a−KS)/n | Δ(n)/p_n |
  | --- | --- | --- | --- | --- | --- |
  | 11 | 31 | 186 | 177 | 0.818 | 1.387 |
  | 51 | 233 | 5993 | 5953 | 0.784 | 1.124 |
  | 101 | 547 | 26878 | 26799 | 0.782 | 1.055 |
  | 201 | 1229 | 119941 | 119782 | 0.791 | 1.056 |
  | 401 | 2749 | 532891 | 532569 | 0.803 | 1.048 |
  | 801 | 6143 | 2352822 | 2352173 | 0.810 | 1.024 |

- **Computed, exact rational arithmetic:** at n=3 the first five perturbed
  factors have product 73039188560769/37066020992000, approximately
  1.9705160307<2. The first six have product
  4293081194294089/2058589781248000>2. Since every factor exceeds one,
  the stated definition gives KS(3)=6; the source entry 5 does not agree
  with that definition. This is an arithmetic correction to the supplied
  source entry, not an independent rereading of the PDF.
- **Unresolved:** the source's Question 5 assertion a(n)>KS(n) for every
  n is stronger than eventual positive separation and is not settled by
  the limit argument.
- **Unverified:** no complete scan of source results depending on
  Question 6 is supplied; no other source theorem is claimed to change.

## ASSUMED-UNVERIFIED

Source quotations and the bounded literature findings are attributed to
the dispatcher; independent source verification and worldwide priority
remain unverified. The stated two-sided and leading-constant asymptotics
are paper conclusions, distinct from the proved Lean convergence.
