---
bibkey: "stone1967local"
authors: "Charles Stone"
year: 1967
title: "On local and ratio limit theorems"
doi: "10.1525/9780520325340-017"
url: "https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s5_v2_p2_article-15.pdf"
claim: "A normalized nondegenerate probability law with finite covariance satisfies a uniform local central limit theorem, in lattice, nonlattice and mixed cases; the nonlattice specialization concerns fixed-width interval probabilities and does not require a density."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# On local and ratio limit theorems

The primary source is Stone's eight-page paper in *Proceedings of the Fifth
Berkeley Symposium on Mathematical Statistics and Probability*, volume II,
part 2, *Contributions to Probability Theory*, University of California Press,
1967, pp. 217–224. Berkeley's scanned copy supplies the text. Crossref identifies
the chapter DOI above and the page range 217–224.

Theorem 1 and Corollary 1, printed p. 218, give the local limit theorem for a
normalized law. The definitions on p. 217 distinguish its lattice and
nonlattice coordinates through the set where the characteristic function has
modulus one. In the one-dimensional nonlattice case, the normalization imposes
no lattice rescaling. Corollary 1 specializes as follows: if independent,
identically distributed real variables have mean $`m`$, variance
$`v\in(0,\infty)`$ and a nonlattice law, then for every fixed $`h>0`$,

```math
\sup_{x\in\mathbb R}
\left|
\sqrt n\,\mathbb P\{Y_1+\cdots+Y_n\in[x,x+h)\}
-\frac{h}{\sqrt{2\pi v}}
 \exp\left(-\frac{(x-nm)^2}{2nv}\right)
\right|\longrightarrow0.
```

The original formulation uses centered cubes; translating the interval gives
the displayed version, with a uniformly negligible change in the Gaussian
term. Endpoint conventions have the same limit: place any endpoint atom in
an interval of fixed width, apply the uniform bound and then let that width
shrink. The same argument shows that the largest atom is $`o(n^{-1/2})`$.
Nonlattice does not mean absolutely continuous. A discrete law can satisfy
this theorem.

Corollary 1 requires finite covariance. The paper introduces its “Cramér's
condition” only afterward, in (2.9), as existence of an exponential moment.
Theorem 2 on p. 219 adds uniformity over compact sets of exponential tilts.
Neither the corollary used here nor that terminology means the stronger
condition that the characteristic function stay uniformly below one at
infinity. No such condition is assumed for the two-jump compound-Poisson law.
Stone attributes the nonlattice case of Theorem 1 to his 1965 paper,
*A local limit theorem for nonlattice multi-dimensional distribution
functions*, *Annals of Mathematical Statistics* 36, 546–551,
DOI `10.1214/aoms/1177700165`. The inspected primary text for the present use is
the 1967 paper.

For the sparse parity model, exponential tilting at the fixed critical
parameter gives a compound-Poisson process with fixed jump sizes
$`\log(1+r)`$ and $`\log(1-r)`$. Its unit-time increment has positive mass at
zero and at both jumps. Irrationality of their ratio makes its law
nonlattice, and its variance is positive and finite. Decomposing a real time
into its integer part and an independent remainder of length less than one
reduces its interval estimate to the corollary. Uniformity in the location
allows this bounded-time remainder to be integrated out.

The local limit theorem and exponential-tilt method are
`literature-attested`. The compensated parity model's actual-path transport,
mixed rare-row counts, logarithmic correction and exact minimax recovery
curve require the additional model-specific arguments in
[PARITY_HIDDEN_ARROW](../../docs/develop/theory/PARITY_HIDDEN_ARROW.md).
Stone's paper does not supply those statistical conclusions, a growing-row
comparison, or an equivalence of complete experiments. Its nonlattice
specialization does not justify using continuous tail prefactors at an
arithmetic jump ratio.
