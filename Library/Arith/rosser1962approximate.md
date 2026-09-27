---
bibkey: rosser1962approximate
authors: "J. Barkley Rosser; Lowell Schoenfeld"
year: 1962
title: "Approximate formulas for some functions of prime numbers"
doi: 10.1215/ijm/1255631807
url: https://doi.org/10.1215/ijm/1255631807
claim: "Theorem 8, equations (3.28) and (3.29), gives explicit lower and upper bounds for the reciprocal prime product, implying the prime-product ratio used in the odd-cover large-prime continuation."
strata_touched: []
license: citation-only
triage: anchor
---

# Explicit reciprocal prime-product bounds

The source is *Illinois Journal of Mathematics* 6(1) (1962), pages
64–94. Crossref metadata confirms the title, authors, journal and DOI.
The inspected [public scan](http://denise.vella.chemla.free.fr/Rosser-Schoenfeld-1962.pdf)
has 31 pages and SHA-256
`8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556`.
The title page, printed page 70 (Theorem 8), and printed page 87
(its proof) were read from the scan. Publisher-served PDF bytes were
not available for comparison. No source text or images are vendored.

Write \(P(x)=\prod_{p\le x}p/(p-1)\). On printed page 70,
Theorem 8 states

\[
e^\gamma\log x\left(1-\frac1{2\log^2x}\right)<P(x)
\quad(x>1),\tag{3.28}
\]
\[
P(x)<e^\gamma\log x\left(1+\frac1{2\log^2x}\right)
\quad(x\ge286).\tag{3.29}
\]

These statements have no Riemann-hypothesis premise. This citation
verifies their text and applicability, not the paper's underlying
numerical tables or a Lean formalization of its proof.

For \(B\ge286\), integer \(\ell\ge3\), \(3^\ell\le B\)
and \(z\ge B\), divide the upper bound at \(z\) by the positive
lower bound at \(B\). Since \(\log B>\ell\), monotonicity of
\((1+u)/(1-u)\) for \(0\le u<1\) gives

\[
\prod_{B<p\le z}\frac p{p-1}
=\frac{P(z)}{P(B)}
\le\frac{\log z}{\log B}
 \frac{1+1/(2\log^2B)}{1-1/(2\log^2B)}
\le\frac{2\ell^2+1}{2\ell^2-1}\frac{\log z}{\log B}.
\]

This elementary consequence is the premise used in
[Chapter 32, JR20](../../docs/reports/erdos7-odd-covering/problem-details/32-conditional-root-measures-and-unrestricted-prime-tails.md)
and [Chapter 33, SH11](../../docs/reports/erdos7-odd-covering/problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md).
Their rational certificates evaluate its consumers; they do not
prove the cited analytic theorem.
