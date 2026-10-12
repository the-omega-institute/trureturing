---
bibkey: erdos1945littlewoodofford
authors: Paul Erdős
year: 1945
title: On a lemma of Littlewood and Offord
doi: 10.1090/S0002-9904-1945-08454-7
url: https://users.renyi.hu/~p_erdos/1945-04.pdf
claim: "Theorem 1 bounds the number of signed sums of real coefficients of absolute value at least one in an open interval of length two by the central binomial coefficient; Theorem 3 treats longer intervals."
strata_touched: []
license: citation-only
triage: anchor
---

# Independent signed sums and the arithmetic small-ball interface

## Verified locator

DOI: <https://doi.org/10.1090/S0002-9904-1945-08454-7>.
The Crossref record identifies Erdős, this title, and *Bulletin of the
American Mathematical Society* 51, 898–902. The AMS PDF endpoint returns
HTTP 403; its Firecrawl proxy is unavailable with HTTP 402. The
[Rényi Institute author archive](https://users.renyi.hu/~p_erdos/1945-04.pdf)
returns the five-page original scan, with the same title, author and
printed pages. Theorems 1 and 3 were read on printed pp. 898–899
(PDF pp. 1–2).

## Classical statement and endpoint convention

For real coefficients $|a_i|\ge1$ and independent fair signs
$\varepsilon_i\in\{-1,1\}$, Theorem 1 gives

$$
\sup_x\mathbb P\!\left\{\sum_{i=1}^n a_i\varepsilon_i
\in(x,x+2)\right\}
\le 2^{-n}\binom n{\lfloor n/2\rfloor}.
$$

The interval is open. Its strict endpoint convention is necessary:
with $n=2$ and both coefficients one, the closed interval $[-2,0]$
contains probability $3/4$, exceeding $\binom21/4$.
Theorem 3 bounds an open interval of length $2r$, for integer $r>0$,
by $2^{-n}$ times the sum of the $r$ largest binomial coefficients.
Theorem 2 supplies an order $r/\sqrt n$ complex disk bound with an
absolute constant, rather than the sharp real coefficient above.

## Scope in the parity hidden-arrow model

The [spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses a fixed-size support prior and posterior centers depending on
the complete observation. Conditional rectangle counts have a
hypergeometric law, and the moving posterior center shares a
calibration denominator. Those variables are not the independent
fair signs in this theorem.

The classical result is an antecedent for inverse-square-root
concentration, not a published instance of the conditional bound
for $\operatorname{dist}(\ell(1/2-\mu_0),\mathbb Z)$.
That application needs the actual conditional kernel, a quantitative
calibration response and control of the moving center. No such bridge
is supplied by this paper. Its Hilbert-space conjecture is outside
the application considered here.
