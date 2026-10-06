---
bibkey: alamoudi2026subradicallysifted
authors: Yazan Alamoudi
year: 2026
title: "On subradically sifted sums related to Alladi's higher order duality between prime factors"
doi: null
url: "https://arxiv.org/abs/2601.10636v2"
claim: "Theorem 1.1 gives quantitative least-prime-factor sifted Möbius estimates in a specified subpower range; it is not a theorem about the FIB signed cofactor Newton panel with a fixed positive power cutoff."
strata_touched: []
license: citation-only
triage: anchor
---

# Sifted Möbius sums and their cutoff range

The retained primary version is [arXiv:2601.10636v2](https://arxiv.org/abs/2601.10636v2),
updated 2026-09-03 after the initial 2026-01-15 submission. The original
PDF has 29 pages and SHA-256
470461bef7714c725d3fe1d131e6cbf476b7d2bb58af230dccaf1bad9fc60e1d.
The arXiv record supplies no DOI or journal reference. The abstract,
introduction and Theorem 1.1 on printed pages 2–3 were inspected.
The full proof and later general-range estimates were not independently
audited or formalized. No source text or PDF is vendored.

Use \(j\) for the source's order parameter to distinguish it from the FIB
Newton index. Its sums are

\[
M_{j,\omega}(x,y)=
\sum_{\substack{n\le x\\p_1(n)>y}}
\mu(n)\binom{\omega(n)-1}{j-1},
\]

where \(p_1(n)\) is the least prime factor. Theorem 1.1 fixes positive
\(Y_0,\mathscr p,\varepsilon\) and restricts its expansion to

\[
1.9\le y\le
\min\!\left\{
Y_0\exp\!\left[
\frac{\mathscr p\log x}{(\log\log(x+1))^{1+\varepsilon}}
\right],\ x^{1/j}
\right\}.
\]

The statement keeps a uniform error constant independent of \(x,y\)
within those conditions. For any fixed \(a>0\), the displayed subpower
threshold is eventually smaller than \(x^a\). The abstract also announces
preliminary bounds for a wider range; those are not treated here as a
verified replacement for the main theorem's expansion.

[The FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§396 uses \(n=mp\), \(m\le D<p\), with \(D\) a fixed positive power of its
Newton scale. The cofactor may contain small primes, so this is not the
least-prime-factor sieve condition \(p_1(n)>y\). Its coefficient
\(e_n=(\mu*\beta)_n\) and smooth Newton kernel also differ from the displayed
source sum. The current primary theorem therefore does not directly settle
the actual joint estimate. This scope comparison does not claim that all
results in the paper, its references, or the wider literature have been
excluded.
