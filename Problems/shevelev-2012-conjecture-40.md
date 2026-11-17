---
slug: shevelev-2012-conjecture-40
bibkey: shevelev2012ramanujanlabos
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/PrimeGap.exists_primeGap_ge
url: https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html
---

# Shevelev's Ramanujan–Labos separation conjecture

## Problem

V. Shevelev, *Ramanujan and Labos Primes, Their Generalizations, and
Classifications of Primes*, Journal of Integer Sequences 15 (2012), states:

> Conjecture 40. (cf. Proposition 18). lim sup_{n→∞} (R_n − L_n) = ∞.

Journal Definition 1 defines R_n as the largest prime satisfying
pi(R_n)-pi(R_n/2)=n, and proves equivalence to the least positive integer
g(n) such that every real x >= g(n) satisfies pi(x)-pi(x/2) >= n.
The encoding uses this threshold characterization, which is Definition 1
in the latest arXiv:0909.0715 version. The Labos minimum is journal
Definition 3 (latest-arXiv Definition 2): the least positive integer L_n
with pi(L_n)-pi(L_n/2)=n. Prime counting at real x is evaluated
at its floor. The exact equivalent tail assertion is: for every natural H,N
there is n >= N with 1 <= n and L_n+H<R_n. This is the target in
[issue #30258](https://github.com/the-omega-institute/trureturing/issues/30258).

## Motivation

The factorial prime-gap theorem `D5/S3/Arith/Primes/PrimeGap.exists_primeGap_ge`
provides the elementary prime-free-interval background. The present argument
requires the stronger placement of arbitrarily long composite intervals
centered at twice a prime, obtained from CRT and Dirichlet rather than from
a factorial alone.

## Gap

The essential analytic step is uniform growth of pi(2m)-pi(m) as m tends to
infinity. Mere infinitude of primes, or one Bertrand prime per interval,
does not establish nonemptiness of every Ramanujan defining set. The
frozen prime-number theorem supplies the needed growth through theta.

## Route

Reuse `EulerLayerRootCorrection.prime_number_limits`, whose theta limit
follows from `MediumPNT` and the Mathlib square-root estimate for psi minus
theta. Eventually theta(x) lies between 5x/6 and 7x/6. Hence

$$\theta(2m)-\theta(m)\ge m/2.$$

Each prime in (m,2m] contributes at most log(2m), so

$$\pi(2m)-\pi(m)\ge \frac{m}{2\log(2m)}\longrightarrow\infty.$$

Natural floor commutes with division by two, so this growth gives the
real-threshold nonemptiness. The integer count rises by at most one per
step and starts at zero; therefore every positive level below a later
value is attained.

For each nonzero integer offset in [-H,H], choose a fresh odd prime larger
than its absolute value and the previous modulus. Solve 2p+j=0 modulo
that prime. The CRT residue remains coprime to the new modulus, so
Dirichlet gives arbitrarily large prime p in that residue. The size bound
makes each divisor proper. The center 2p is composite as well.

In this window the upper prime count is constant. At twice p the lower
prime count gains p. For n=count(2p-1), the count at the left endpoint is
at least n, whereas the count at the right endpoint is strictly below n.
Consequently L_n lies at or before the left endpoint and R_n lies after
the right endpoint. Increasing the window bound beyond every R_j for j<N
forces n>=N and yields the full tail assertion.

## Falsifier

A fixed natural H and N for which no positive n>=N satisfies L_n+H<R_n
would falsify the assertion. Any proof that assumes defining-set
nonemptiness without proving growth, replaces the real tail by an integer
finite prefix, or drops the tail index N would not resolve this target.

## Evidence

The exact declarations are `ramanujanSet_nonempty`, `labosSet_nonempty`
and `result` in `D5/S3/Arith/Primes/ShevelevConjectureForty.lean`.
They retain the supplied definitions literally. The nontruncation inequality
is proved and used through the additive prime-count identity. Dyadic counting and growth are auxiliary declarations in the conclusion
module; the composite-window construction is a separate general module. The chosen minima are justified by nonemptiness.

## Triage

The mechanism is the downward count jump at twice a prime inside a
composite window, together with uniform dyadic prime-count growth.
Proposition 18 establishes limsup(R_(n+1)-L_n)=infinity. Conjecture 40,
proved by the same-index conclusion here, removes that index shift. No
version of Proposition 18 is assumed as a premise. Conjecture 41 asks for
infinitely many peculiar primes; it and the other classification conjectures
are neither proved nor refuted by this result.
The proof gives arbitrarily large absolute differences, without a claimed
positive relative lower bound for (R_n-L_n)/R_n or an effective rate in n.

## ASSUMED-UNVERIFIED

Independent current literature completeness and priority remain unchecked.
The publisher's Article 12.5.4 HTML and full-text TeX supply the statement,
numbering and comparison with Proposition 18. The minimum-threshold
characterization follows Definition 1 in the source, while the Labos minimum
is printed as Definition 3; the given Lean minima encode these forms.
