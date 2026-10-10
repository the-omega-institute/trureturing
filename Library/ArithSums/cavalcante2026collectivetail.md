---
bibkey: cavalcante2026collectivetail
authors: Claudemir de Souza Cavalcante
year: 2026
title: A Collective Tail Criterion for the Prime Exponents of a Hypothetical Least Counterexample to Robin's Inequality
doi: 10.5281/zenodo.20733714
url: https://doi.org/10.5281/zenodo.20733714
claim: The working paper combines least-counterexample structure with a collective exponent-defect budget and obtains explicit necessary valuation ranges; it does not prove Robin's inequality or supply a FIB-to-multiplicative transport.
strata_touched: []
license: CC-BY-4.0
triage: anchor
---

# Collective exponent tails for a hypothetical Robin counterexample

The source is Claudemir de Souza Cavalcante, *A Collective Tail Criterion for
the Prime Exponents of a Hypothetical Least Counterexample to Robin's
Inequality*, Zenodo record [20733714](https://doi.org/10.5281/zenodo.20733714),
17 June 2026. The deposited PDF is 9 pages and has SHA-256
`dd586ea45b57aecfbb05f74c11387f42d11bab791ea8777d6946094bbc78172b2`.
The source is reference input; it was not independently formalized here.

## The collective budget

Assume that $c>5040$ is the least integer violating Robin's strict inequality
in that range. For

$$
D(n)=\sum_{p\mid n}-\log\bigl(1-p^{-\nu_p(n)-1}\bigr),
$$

the paper combines the initial-prime support and non-increasing exponents of
a superabundant least counterexample with its explicit upper estimate for
$n/\varphi(n)$. It obtains

$$
D(c)<\log\left(1+\frac{0.0094243}{31.03^3}\right)
<\frac{94243}{298775737270}.
$$

The displayed decimal is replaced by the rational bound for the finite
certificates. The source uses Vega's lower bound on the largest prime factor
and the verified primorial range to ensure that the relevant prime intervals
are in the support of $c$.

## Tail criterion and supplied cutoffs

For a prime $q$, $r\ge1$, and $q\le X\le P^+(c)$, define

$$
T_r(q,X)=\sum_{q\le p\le X}-\log\bigl(1-p^{-(r+1)}\bigr).
$$

If $T_r(q,X)$ exceeds the budget above, monotonicity of the exponent vector
forces $\nu_p(c)\ge r+1$ for every prime $p\le q$. Exact integer certificates
in the source give

$$
\nu_p(c)\ge4\quad(p\le61),\qquad
\nu_p(c)\ge3\quad(p\le479),\qquad
\nu_p(c)\ge2\quad(p\le233911).
$$

These are necessary conditions under the least-counterexample hypothesis.
The paper explicitly leaves the remaining exponent patterns compatible with
the collective budget; no contradiction and no all-integer Robin bound is
claimed.

## Boundary for the FIB route

The result is multiplicative: it uses $\nu_p(c)$, initial prime support and
the same integer's divisor-sum factorization. A five-window address
$[null,2,3,2\,5,5]$ records additive Fibonacci inclusion and does not imply
any of these $p$-adic valuations. Existing modular observations can test the
necessary divisibility conditions on the same generated integer; see the
[combined-cutoff application](cavalcante2026blockexchange.md#application-through-the-existing-fib-crt-interface).
Such a filter does not recover the complete exponent vector, establish
superabundance, or pay the signed Robin tail. The source supplies stronger
conditional valuation inputs, rather than a new FIB estimate.
