---
bibkey: ozvatanpashaev2017binetcurves
authors: Merve Özvatan and Oktay K. Pashaev
year: 2017
title: Generalized Fibonacci Sequences and Binet-Fibonacci Curves
doi: null
url: https://arxiv.org/abs/1707.09151v1
claim: Section 5.1 extends the Binet formula to a real-parameter complex curve after selecting the +pi logarithm branch.
strata_touched: []
license: citation-only
triage: anchor
---

# Generalized Fibonacci sequences and Binet-Fibonacci curves

The primary source is the fixed [arXiv v1 PDF](https://arxiv.org/pdf/1707.09151v1),
§5.1, printed pages 13–14. It writes
$\log(-1)=i(2n+1)\pi$ and then selects $n=0$. Its real-parameter curve is

```math
B_+(t)=\frac{e^{at}-e^{-at}e^{i\pi t}}{\varphi+\varphi^{-1}},
\qquad a=\log\varphi.
```

The displayed real and imaginary components on printed page 14 are

```math
\Re B_+(t)=\frac{e^{at}-e^{-at}\cos(\pi t)}{\sqrt5},\qquad
\Im B_+(t)=-\frac{e^{-at}\sin(\pi t)}{\sqrt5}.
```

Thus the negative-frequency branch used in
[FIB hyperbolic geometry and phase boundary, §§一、六](../../docs/develop/theory/AURIC_FIB_HYPERBOLIC_GEOMETRY_AND_PHASE_BOUNDARY.md)
is $\overline{B_+(t)}$ for real $t$. All integer samples agree. The source
attests the complex Binet continuation and its branch choice. Its later
area, curvature, spiral and natural-form comparisons are not consumed.
The consumer's autonomous embedding, observation fibers and native
continuing-response comparison are not attributed to this paper.
