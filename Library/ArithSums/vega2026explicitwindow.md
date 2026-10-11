---
bibkey: vega2026explicitwindow
authors: Frank Vega
year: 2026
title: An Explicit Window for Hypothetical Colossally Abundant Counterexamples to Robin's Criterion
doi: 10.20944/preprints202408.0348.v13
url: https://www.preprints.org/manuscript/202408.0348/v13
claim: The preprint gives an explicit primorial window for hypothetical colossally abundant Robin counterexamples and isolates an uncontrolled fractional-part sum; it does not provide a FIB source map or an unconditional RH proof.
strata_touched: []
license: CC BY 4.0 (source statement)
triage: anchor
---

# An explicit CA window and its residual obstruction

The inspected source is Frank Vega, [version 13 of the preprint](https://www.preprints.org/manuscript/202408.0348/v13), posted in May 2026. The manuscript is marked as not peer reviewed. This card records its stated results and their interface with the FIB Robin program; it is not a Lean verification or an independent audit of every cited estimate.

## The explicit window

Let (n>5040) be a colossally abundant number violating Robin's inequality, and let (p_k) be its largest prime factor. For (p_k>7{,}232{,}121{,}212), Theorem 1 states that, with

$$
N_k=\prod_{i=1}^{k}p_i,
$$

one has

$$
N_k\le n<N_k^{Y_k}.
$$

The source gives (Y_k	o1^+) and records (Y_k-1<0.00021) once
(p_k>e^{31.018189471}). Its Theorem 2 turns this into an equivalent RH test restricted to CA integers in these windows, using Robin's theorem that a false RH would yield infinitely many CA counterexamples.

## The remaining obstruction in the source

The Alaoglu--Erdős exponent formula writes the exponent of a prime (qle p_k) in a CA integer with parameter (arepsilon) as a floor of a smooth quantity (x_q(arepsilon)). Consequently the logarithmic size has the decomposition

$$
\log n
=S(\varepsilon)-F(\varepsilon)-\vartheta(p_k),
\qquad
F(\varepsilon)=\sum_{q\le p_k}\{x_q(\varepsilon)\}\log q.
$$

The source states that explicit Chebyshev and Mertens estimates control (S(arepsilon)) at the required scale, while the universal bound (0le F(arepsilon)<\vartheta(p_k)) is too weak by a factor of order (log^2 p_k). A uniform estimate for this joint fractional-part sum is left open. Thus the window theorem narrows the possible source but does not determine the Robin sign inside it.

## Interface with the FIB inventory

For the strict inventory already defined in the project, put

$$
P_-(t)=\prod_{p<t}p,
\qquad
N^-(t)=P_-(t)H_t.
$$

The project's repeated-layer estimate gives

$$
\log H_t=\sqrt2\,\sqrt t+o(\sqrt t),
\qquad
\log P_-(t)=t+o(t),
$$

and therefore

$$
\frac{\log N^-(t)}{\log P_-(t)}
=1+\frac{\sqrt2+o(1)}{\sqrt t}.
$$

When a strict-inventory point is also a CA point, this is the project's primorial-window coordinate. Consuming Vega's theorem would require comparing this exponent with the explicit (Y_k), matching (p_k) with the actual largest support prime, and transporting the residual (F(arepsilon)) to the same FIB source. The preprint supplies none of those FIB identifications. Its fractional-part obstruction is therefore a useful external description of the same signed-tail gap, not a proof of Robin or RH for the FIB family.
