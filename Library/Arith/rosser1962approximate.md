---
bibkey: rosser1962approximate
authors: "J. Barkley Rosser; Lowell Schoenfeld"
year: 1962
title: "Approximate formulas for some functions of prime numbers"
doi: 10.1215/ijm/1255631807
url: https://doi.org/10.1215/ijm/1255631807
claim: "Theorem 8 gives explicit reciprocal prime-product bounds; Corollaries 1 and 3 give global and dyadic prime-count bounds used in actual Fibonacci cofactor Newton subseries."
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
[Chapter 32, JR20](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/32-conditional-root-measures-and-unrestricted-prime-tails.md)
and [Chapter 33, SH11](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md).
Their rational certificates evaluate its consumers; they do not
prove the cited analytic theorem.

## Dyadic prime-count lower bound

On printed page 69 (PDF page 6 of the same scan), Corollary 3 states

\[
\frac{3x}{5\log x}<\pi(2x)-\pi(x)
\qquad\left(x\ge\frac{41}{2}\right).\tag{3.8}
\]

The threshold printed as the mixed fraction \(20\tfrac12\) was checked
against the page image. It is not \(\sqrt{20}\). The count includes
primes in \((x,2x]\). This theorem has no RH premise and is used directly;
it is not rederived from a qualitative prime number theorem or replaced
by the weaker assertion that the interval contains one prime.

The [FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§393 applies this count to the actual coefficients at indices \(4p\).
The original prime-count theorem remains a literature input. Its use in
an actual coefficient subseries is a separate model derivation, and the
source statement is not a Lean proof of that derivation.

## Global prime counts and the classical PNT interface

On the same printed page 69, Corollary 1 states

\[
\frac{x}{\log x}<\pi(x)\qquad(x\ge17),\tag{3.5}
\]
\[
\pi(x)<1.25506\frac{x}{\log x}\qquad(x>1).\tag{3.6}
\]

Printed pages 65–67, Section 2, recall the classical prime number theorem
and its attribution to Hadamard and de la Vallée Poussin. Equation (2.26)
on printed page 67 gives the Stieltjes partial-summation interface for
sums over primes. The qualitative PNT is used as an existing theorem;
these page references do not claim an independent verification of its
proof or of the paper's numerical tables.

The FIB volume §394 uses PNT only with fixed integer cofactor \(m\) and
fixed cutoff \(D\). Equation (3.6) controls the tails of the rescaled
prime-count measure. It does not by itself supply an asymptotic estimate
uniform in an unbounded cofactor range, and the volume does not claim one.

## Quantitative PNT for a growing cofactor range

Printed page 66, equations (2.21)–(2.22), recall the classical bound,
attributed to Ingham's Theorem 23:

\[
|\pi(x)-\operatorname{li}(x)|
<b x\exp[-a\sqrt{\log x}]\qquad(x\ge X),
\]

for some positive absolute constants \(a,b,X\). The equation and exponent
were checked against the original page image. Consequently, for each fixed
\(A>0\), this already supplies
\(\pi(x)-\operatorname{li}(x)=O_A(x/(\log x)^A)\).
It is a classical literature input, not a newly derived prime number theorem
or a claim about the strongest available PNT error.

The FIB volume §396 combines this existing bound with Stieltjes partial
summation for its Gaussian prime kernel. The kernel's derivative
and endpoint budgets give errors uniform over its particular growing
cofactor range. That actual signed-source interface is separate from the
source theorem and remains a paper derivation.
