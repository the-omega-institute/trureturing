---
bibkey: bakerharmanpintz1997goldbach
authors: R. C. Baker, G. Harman and J. Pintz
year: 1997
title: The Exceptional Set for Goldbach's Problem in Short Intervals
doi: 10.1017/CBO9780511526091.004
url: https://doi.org/10.1017/CBO9780511526091.004
claim: Theorem 3(I), at q=1, independently supplies the adopted all-centre 0.99 and 1.01 counts above the strict eleven-twentieths threshold; the chapter also warns of errors in a Lou--Yao paper.
strata_touched: []
license: citation-only
triage: anchor
---

# Independent two-sided counts above eleven twentieths

The primary is Baker--Harman--Pintz, *The Exceptional Set for Goldbach's
Problem in Short Intervals*, in *Sieve Methods, Exponential Sums, and
their Applications in Number Theory*, London Mathematical Society
Lecture Note Series 237, pp.1--54,
[DOI 10.1017/CBO9780511526091.004](https://doi.org/10.1017/CBO9780511526091.004).
The publisher's chapter metadata gives publication year 1997; its
online-publication date is not the original publication year.
The [Cambridge excerpt](https://assets.cambridge.org/97805215/89574/excerpt/9780521589574_excerpt.pdf)
has SHA-256
`68995a7c6a0cf2971c5d350daa86c582d291ff31a95f23d779f2c239d02ba293`.
Its rendered printed pp.1--4 were read for the definitions, fixed
positive epsilon, theorem statement and source warning. The excerpt
contains printed pp.1--10, not the complete chapter.

Theorem 3(I), printed p.4, with $q=1$ and $\mathcal L=\log x$,
states, for a fixed sufficiently small positive $\varepsilon$ and
all sufficiently large centres,

$$
x^{11/20+\varepsilon}\le M\le x/\log x
\quad\Longrightarrow\quad
0.99\frac M{\log x}
<\pi(x)-\pi(x-M)
<1.01\frac M{\log x}.
$$

The project uses only this $q=1$ specialization. This is an
all-centre count; Theorem 3(II)'s exceptional-centre qualification
is a different statement. The fixed positive epsilon and length
upper bound remain. No value at exponent $11/20$, moving-epsilon
uniformity, interval asymptotic, numerical sufficient start or
best-known-constant assertion is inferred.
The paragraph following Theorem 3 explains its reduction to the
pointwise lower and upper sequences constructed in section 4.
That section's full sieve argument and numerical estimates have
not been independently audited or Lean-verified here.

## Source warning and the consumer's admissible inputs

The same printed p.4 says of Lou and Yao [19]:
"there are serious errors in this paper, including the use of the
bound" $\pi(x)-\pi(x-y)\ll y/\log x$ "with $y$ tending to zero."
The inspected excerpt does not contain the bibliography needed to
bind [19] to an exact title and year. This is evidence of a published
proof warning, not a proof that either recorded Lou--Yao theorem is
false or that their entire bibliography is invalid.

The [actual-source consumer](../Estimation/trureturing2026pricegapconvexity.md#independent-two-sided-counts-above-the-strict-eleven-twentieths-cut)
uses this independent BHP statement for the strict exponent region
above $11/20$. It does not rely on either recorded Lou--Yao proof.
The shorter region continues to use the existing Iwaniec upper
capacity and BHP 2001 terminal lower envelope. The original source,
fixed exponents, logarithmic prime weights, higher layers and strict
endpoints are retained in the existing blocking transfer and
competitor root. The resulting bounds are project applications of
published inputs, not new prime-distribution theorems. They do not
supply the original signed Robin upper estimate or prove RH.
