---
bibkey: revesz1988oscillation
authors: Szilárd Gy. Révész
year: 1988
title: Effective oscillation theorems for a general class of real-valued remainder terms
doi: 10.4064/aa-49-5-481-505
url: https://doi.org/10.4064/aa-49-5-481-505
claim: The proof following Lemma 6 supplies a discrete real-power-sum fact, and Lemma 4 records the classical low-ordinate zero boundary; these facts are used in a signed Gaussian application to the complete Mertens primitive, without treating the paper's unsigned remainder theorem as a signed primitive theorem.
strata_touched: []
license: citation-only
triage: anchor
---

# A finite power-sum selection and its signed-primitive application

The primary is *Acta Arithmetica* 49(5), 481–505. The publisher's open
download resolves to the [ICM scan](https://matwbn.icm.edu.pl/ksiazki/aa/aa49/aa4954.pdf),
883,715 bytes, 13 PDF pages, SHA-256
`01c8e8a41018223d30c841f48282755502ca48387f4cfbf2eb852990704d420c`.
Printed pp.481–491 were visually inspected; the remaining proof was not
independently audited or Lean verified.

The proof following Lemma 6, printed p.488, uses the standard discrete
power-sum fact for roots of a real polynomial: one of the first
$d+1$ power sums of a degree-$d$ real polynomial is nonnegative.
Applying that fact to any $n-1$ complex numbers together with their
conjugates, and adjoining a designated number $1$, gives the loose
integer-index consequence

$$
z_1=1\quad\Longrightarrow\quad
\max_{1\le\nu\le2n+1}\Re\sum_{j=1}^n z_j^\nu\ge1.
$$

The $n=1$ case is immediate. This is a consumed application of the
existing Cassel step, not a new power-sum theorem. No modulus restriction
is imposed on the other $z_j$. Multiplicities remain in the sum.
Lemma 4, printed p.486, also records the first ordinates of the classical
Riemann zeros; the only consequence used is that all nontrivial zeros
have ordinate of absolute value greater than $10$.

The [complete positive-primitive localization, §479](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md)
uses this finite selection in the actual integrated zero spectrum and
pays the nonoscillatory polynomial-Gaussian envelope and every omitted
tail. Its explicit positive-primitive and literal-lcm conclusions are
repository paper applications, not conclusions stated in Révész's
article. The source's Theorem 1 is an absolute-value remainder estimate
in its stated logarithmic-derivative class; it is not substituted for
that signed application. Neither the source facts nor this application
construct an actual off-critical zero or prove RH.

## Verified locator

- DOI: https://doi.org/10.4064/aa-49-5-481-505
