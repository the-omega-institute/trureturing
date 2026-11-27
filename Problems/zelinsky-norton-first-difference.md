---
slug: zelinsky-norton-first-difference
bibkey: zelinsky2021totalprimefactors
doi: null
url: https://math.colgate.edu/~integers/v76/v76.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.result
---

# The positive values omitted by Norton first differences

## Problem

Zelinsky, Integers 21 (2021), article A76, Section 5, Question 5:

> Does a(n+1) − a(n) take on every positive integer value?

Here p_n is the n-th prime, p_1=2, and a(n) is the least k≥1 for which
the product of p_r/(p_r−1), over n≤r≤n+k−1, strictly exceeds 2.
The claim is

$$
\forall m\in\mathbb N,\quad
m>0\Longrightarrow\exists n\ge1,\quad a(n+1)-a(n)=m.
$$

The refutation retains natural subtraction; its eventual
comparison first establishes positivity, so no truncated negative value
is used to infer the asymptotic bound.

## Motivation

Unbounded first differences can still omit most positive integers.
Bounding how many starting indices can yield a difference at most X
distinguishes growth from surjectivity.

## Gap

A large difference occurring infinitely often does not imply that a
positive integer is omitted. A uniform lower bound in terms of p_n,
together with prime sparsity, is sufficient to bound the entire value set.

## Route

The following is a paper derivation. Put s_n=n+a(n)−1, Q_n=p_{s_n},
w(q)=log(q/(q−1)), and let ε_n be the crossing excess. Then

$$
\sum_{j=n}^{s_n}w(p_j)=\log2+\varepsilon_n,\qquad
0<\varepsilon_n\le w(Q_n).
$$

The Mertens prefix identity yields Q_n≍p_n². Subtracting the identities
for n and n+1 gives

$$
\sum_{j=s_n+1}^{s_{n+1}}w(p_j)
 =w(p_n)+\varepsilon_{n+1}-\varepsilon_n.
$$

The right side is comparable to 1/p_n because ε_n=O(p_n⁻²).
Consecutive starting primes are comparable, and all primes in the added
interval are comparable to p_n². The number of added terms is therefore

$$
s_{n+1}-s_n=1+a(n+1)-a(n)\asymp p_n.
$$

Consequently there are constants c>0 and n_0 such that the natural
difference Δ(n)=a(n+1)−a(n) satisfies Δ(n)≥c p_n for n≥n_0.
Let V(X) be the number of distinct positive integers m≤X attained by
some Δ(n), n≥1. Each late index producing such a value has p_n≤X/c;
the early indices contribute at most n_0 values. Thus

$$
V(X)\le n_0+\pi(X/c)=O(X/\log X)=o(X).
$$

The inequality counts a value once even when several indices produce it.
If the original claim held, V(X)=⌊X⌋ for every X≥1, contradicting the
zero density. In fact infinitely many positive integers are omitted.

## Falsifier

Showing Δ(n)→∞ alone does not establish zero density of its range.
The bound must apply to every sufficiently large n. Early indices must
remain as a finite additive contribution, and the count of attained
values can only be bounded above by the count of producing indices.

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

`ZelinskyNortonFirstDifference.result` proves in Lean the literal negation
`¬ claim`. It uses the proved `norton_endpoint_bounds` and
`norton_adjacent_cancellation`, whose Mertens input is `Mertens.E₃.abs_le`.
`Chebyshev.eventually_primeCounting_le` gives the prime-counting estimate
used to obtain Δ(n)≥2n for every sufficiently large n.

The refutation is a finite cardinal argument. Choose N such that Δ(n)≥2n
for n≥N. If every positive value occurred, then each m in {1,…,2N+1}
would occur at an index n in {1,…,N}: a larger index would force
Δ(n)≥2N+2. The image of these N indices cannot contain 2N+1 values.
This proves existence of an omitted positive value without identifying
a particular one. The result's axiom closure is contained in `propext`,
`Classical.choice` and `Quot.sound`. The density estimate V(X)=o(X)
is a paper consequence, not a separate formalized result here.

## Triage

- **Refuted in Lean:** `ZelinskyNortonFirstDifference.result` negates the
  source's claim that every positive integer occurs. Its proof obtains
  eventual Δ(n)≥2n and uses the finite cardinal contradiction above.
- **Proved in Lean:** endpoint localization and the adjacent-growth lower
  bound supply the asymptotic input to this refutation. The natural
  subtraction agrees with real subtraction on the eventual positive range.
- **Paper derivation, not separately formalized:** the two-sided comparison
  Δ(n)≍p_n and prime sparsity give V(X)=O(X/log X)=o(X), hence infinitely
  many omitted positive values. The formal refutation does not require
  this full density statement.
- **Paper derivation, not formalized:** the sharper prediction is
  Δ(n)∼p_n. The two-sided comparison is sufficient for the density argument
  and does not prove that leading constant.
- **Computed, floating point:** for n=11,51,101,201,401,801 the values of
  Δ(n)/p_n rounded to three decimals are respectively
  1.387,1.124,1.055,1.056,1.048,1.024. The threshold values and numerical
  method are recorded in the
  [threshold-separation dossier](norton-threshold-differences.md).
  These readings do not certify an asymptotic or classify the range.
- **Unresolved:** the argument does not identify the least omitted value
  or classify the attained set.
- **Proved in Lean:** the same adjacent-growth bound for every fixed α>1
  gives Conjecture 27's eventual growth. Surjectivity and divergence remain
  different properties.
- **Unverified:** no source theorem depending on an affirmative answer
  has been identified by an independent dependency scan.

## ASSUMED-UNVERIFIED

The source and bounded literature assertions are attributed to the
dispatcher. Independent source verification and worldwide priority remain
unverified. The density and leading-constant statements remain paper
conclusions, distinct from the proved Lean refutation.
