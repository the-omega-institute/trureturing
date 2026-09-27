---
slug: parisse-stirling-fibonacci-alternating-sum
bibkey: parisse2024hypersequences
doi: 10.5281/zenodo.13331499
url: https://math.colgate.edu/~integers/y70/y70.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.result
---

# The Alternating Stirling Weighted Sum of Even-Index Fibonacci and Lucas Numbers

## Problem

Parisse, *Integers* **24** (2024), Article A70, Section 4, states two conjectures.
The first, after Equation (4.7):

> Conjecture 1. For all ℓ ∈ N_0, we have
>
>     ∑_{m=0}^{ℓ} (-1)^m m! S(ℓ+1, m+1) F_{2(m+1)} = (-1)^ℓ ∑_{m=0}^{ℓ} m! S(ℓ, m) F_{m+2} .

The second, after Equation (4.9):

> Conjecture 2. For all ℓ ∈ N_0, we have
>
>     ∑_{m=0}^{ℓ} (-1)^m m! S(ℓ+1, m+1) L_{2(m+1)} = (-1)^ℓ ∑_{m=0}^{ℓ} m! S(ℓ, m) L_{m+2} .

Here `S(j, m)` is the Stirling number of the second kind, `F` the Fibonacci
numbers with `F_1 = F_2 = 1`, and `L` the Lucas numbers with `L_0 = 2`, `L_1 = 1`.
Both are the constant term of the article's own formula for the weighted sums
`∑_{k=0}^{n} k^ℓ F_k` and `∑_{k=0}^{n} k^ℓ L_k`, rewritten through Equation (3.14),
`c_{ℓ,m}(0) = (-1)^m m! S(ℓ+1, m+1)`.

The article's remarks fix the reading of the stacked bracket symbols. The
right-hand side of Conjecture 1 is named there as A000557, whose recorded formula
is `a(n) = ∑_{k=0..n} k! Stirling2(n, k) Fibonacci(k+2)`; the right-hand side of
Conjecture 2, times `-1`, is named as A263968, whose recorded formula is
`a(n) = (-1)^{n+1} ∑_{k=0..n} k! Lucas(k+2) Stirling2(n, k)`. Both readings are
therefore Stirling numbers of the second kind, not binomial coefficients.

## Motivation

The frozen theorem
`D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.result` settles both.
Neither identity depends on the initial values of the sequence, so the recorded
proof establishes the common statement for an arbitrary integer sequence
satisfying `u_{n+2} = u_n + u_{n+1}` and reads off the two conjectures as the
Fibonacci and Lucas instances.

## Gap

Issue 9415 records the screen carried out before write-up. The author's own sequel,
*Integers* **26** (2026), Article A36, published 2/20/26, was opened in full and
contains no occurrence of the word conjecture. The OEIS entries A000557 and
A263968 were opened; both link this article, and neither carries the alternating
identity among its formulas. A web pass over the two sequence numbers and the
article title returned no proof; the nearest recent item, arXiv:2511.10797 on
weighted sums of Lucas sequences, mentions neither Parisse nor Stirling numbers.
Citation-index result pages were not exhaustively reachable, so this is a bounded
negative finding.

## Route

Let `Q_n(X) = ∑_m m! S(n, m) X^m`. This is the classical Fubini polynomial, also
called the ordered Bell polynomial; `Q_n(1)` is the number of ordered partitions of an
`n`-element set. The Stirling recurrence `S(n+1, m) = m S(n, m) + S(n, m-1)` becomes the
differential recurrence

    Q_0 = 1 ,    Q_{n+1} = X(1 + X) Q_n' + X Q_n .

The first ingredient is the functional equation

    X · Q_n(-1 - X) = (-1)^n (1 + X) Q_n(X)    for n ≥ 1 ,

proved by induction: differentiating the statement at `n` and combining it with
the composite of the recurrence gives the statement at `n + 1` in one linear step.

The same equation drops out of the exponential generating function
`∑_n Q_n(x) t^n / n! = 1/(1 - x(e^t - 1))`, which is the standard one for the Fubini
polynomials. Substituting `x → -1-x` and multiplying by `x` gives
`x / ((1+x) e^t - x)`; substituting `t → -t` and multiplying by `1+x` gives
`(1+x) e^t / ((1+x) e^t - x)`. The two differ by the constant `-1`, which is exactly the
`n = 0` term, and that is why the equation carries the hypothesis `n ≥ 1`. The recorded
proof runs the induction rather than the generating function, which would need the formal
exponential series; the computation above is an independent check of the statement.

The second ingredient is the pairing `L_c(p) = ∑_k p_k u_{k+c}` of a polynomial
with a sequence satisfying `u_{n+2} = u_n + u_{n+1}`. It satisfies
`L_c(X p) = L_{c+1}(p)` by reindexing, `L_c((1+X) p) = L_{c+2}(p)` by the
recurrence, and

    L_1((1 + X)^m) = u_{2m+1} ,

which is the binomial index-doubling identity `∑_i C(m, i) u_{i+c} = u_{2m+c}`,
itself an induction that uses the recurrence alone.

The two ingredients meet as follows. Writing `c_k` for the coefficients of `Q_ℓ`,
the Stirling recurrence gives `m! S(ℓ+1, m+1) = c_{m+1} + c_m`, so the left-hand
side of the conjecture is `∑_m (-1)^m (c_{m+1} + c_m) u_{2m+2}`. Reindexing the
first part by `j = m + 1` and using `u_{2j+2} - u_{2j} = u_{2j+1}` collapses this
to `∑_k c_k (-1)^k u_{2k+1}`, which is exactly `L_1(Q_ℓ(-1 - X))`. The boundary
term at `j = 0` drops out because `Q_ℓ` has no constant term for `ℓ ≥ 1`, which
also gives `Q_ℓ = X P`. Cancelling `X` in the functional equation turns the
composite into `(-1)^ℓ (1 + X) P`, and then

    L_1(Q_ℓ(-1-X)) = (-1)^ℓ L_1((1+X) P) = (-1)^ℓ L_3(P) = (-1)^ℓ L_2(Q_ℓ) ,

the last expression being the right-hand side of the conjecture. The case `ℓ = 0`
is both sides equal to `u_2`.

## Falsifier

A different value of `S(ℓ+1, m+1)` for small `ℓ`, or a sign error in the
functional equation, would break the identity at once. The first common values of
the two sides of Conjecture 1 are `1, -2, 8, -50, 416, -4322, 53888, -783890`,
whose absolute values are A000557; the first values for Conjecture 2 are
`3, -4, 18, -112, 930, -9664`, which up to sign are A263968. The functional
equation can be checked at `n = 2`: `Q_2 = X + 2X^2`, and
`X(-1 - X + 2(1 + X)^2) = X(1 + 3X + 2X^2) = (1 + X)(X + 2X^2)`.

## Evidence

Both identities were checked numerically for `ℓ = 0` through `ℓ = 125` with no
mismatch before the formalisation was attempted.

The generalisation to an arbitrary sequence satisfying `u_{n+2} = u_n + u_{n+1}`
is not a strengthening for its own sake: the initial values never enter the
argument, and carrying them would require a separate treatment of the boundary
term for each sequence. The Lucas case is where this shows, since `L_0 = 2` is not
zero and the boundary term is killed instead by the vanishing constant term of
`Q_ℓ`.

## Triage

`theorem`; Tier 1 named external open questions, preregistered in issue 9415
before the probe. The admission basis is `escape-witness`; the classification is
`proof_shape: content`. The module reports `utility: none`: no declaration in it
is a bounded enumeration, a checker, a numeric reduction or a certified instance,
and the statement is a universally quantified identity rather than a finite
computation.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the article, its 2026 sequel, the OEIS entries
A000557 and A263968, and a web pass over the two sequence numbers and the article
title were opened; citation-index result pages were not exhaustively reachable, so
no worldwide priority claim is made.

The numerical range `ℓ ≤ 125` is a pre-formalisation check only and is superseded
by the recorded proof; it is stated here because it is what motivated the attempt,
not as evidence for the identity.
