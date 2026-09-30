---
bibkey: erdosnicolas1975repartition
authors: Paul Erdős; Jean-Louis Nicolas
year: 1975
title: Répartition des nombres superabondants
doi: 10.24033/bsmf.1793
url: https://www.numdam.org/item/BSMF_1975__103__65_0/
claim: The classical benefit is the nonnegative loss relative to a colossally abundant optimizer; the FIB price-loss expression is exactly this existing quantity.
strata_touched: []
license: citation-only
triage: anchor
---

# Répartition des nombres superabondants

Primary source: *Bulletin de la Société Mathématique de France* **103** (1975), 65–90, [Numdam article record](https://www.numdam.org/item/BSMF_1975__103__65_0/) and [original scan](https://www.numdam.org/item/10.24033/bsmf.1793.pdf). The relevant locator is §3, Proposition 5 and its proof, printed pp.73–74. This note records the definition and its scope; it is not a verification of every proof in the paper or a Lean result.

Let $Z(n)=\sigma(n)/n$, and let $N$ maximize $Z(n)n^{-\epsilon}$ for a fixed $\epsilon>0$. On printed p.74, the authors define, for an arbitrary positive integer $m$,

$$
\operatorname{ben}_{N,\epsilon}(m)
=\epsilon\log(m/N)-\log\frac{Z(m)}{Z(N)}
\ge0.
$$

The nonnegativity follows from the defining optimality of the same $N$ and $\epsilon$. If $L=\log m$, $F=\log Z(m)$, $L_0=\log N$, $F_0=\log Z(N)$, then

$$
F_0-\epsilon L_0-F+\epsilon L
=\operatorname{ben}_{N,\epsilon}(m).
$$

Thus a “price loss” with the same reference optimizer and price is exactly the classical benefit, not a new FIB invariant. In particular, a separately justified choice $N=5040$, $\epsilon=1/25$ has this meaning; this card does not independently establish that optimizer choice.

Proposition 5 is a near-extremal structural application. Its additional hypotheses are that $n$ is **superabundant** and it lies between $N$ and $NP$, where $P$ is the prime after the largest prime factor of $N$. Its proof uses a small benefit to control displacement of prime-exponent thresholds. The arbitrary-integer definition of benefit must not be confused with those stronger hypotheses on the integer to which Proposition 5 applies. An arbitrary Robin violation in a prescribed residue class is not automatically superabundant.

The proof points back to Proposition 4, p.120, of Nicolas's *Répartition des nombres hautement composés de Ramanujan*, *Canadian Journal of Mathematics* **23** (1971), 116–130. This antecedent was identified from the original bibliography but its full text was not checked in this source inspection; the exact displayed benefit above is directly visible in the 1975 primary source.

For the FIB Robin analysis, the valuation-increment source

$$
w_s(d)=\frac{b_s(d)}d,
\qquad b_s(p^j)=Z(p^j)^s-Z(p^{j-1})^s,
\qquad J_s(d)=\log\frac{\max_e w_s(e)}{w_s(d)}
$$

has a different objective. The classical support-loss method motivates its decomposition, but Proposition 5 supplies neither its uniform editing bound nor its power-sum or complementary-moment estimates without an additional argument. Conversely, the **unweighted** assertion that a growing reduced residue class has at most one sufficiently large Robin violation follows by a short classical support-loss argument applied to $n/\varphi(n)$, combined with prime-number and Mertens estimates. That synthesis requires no Fibonacci encoding and must not be advertised as a FIB-specific method or historical novelty. The project's weighted residual statement remains a separate assertion.
