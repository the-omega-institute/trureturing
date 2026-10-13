---
bibkey: brouckevindas2024discretization
authors: Frederik Broucke; Jasson Vindas
year: 2024
title: A new generalized prime random approximation procedure and some of its applications
doi: 10.1007/s00209-024-03526-4
url: https://arxiv.org/abs/2102.08478v2
claim: Theorem 1.2 realizes any admissible continuous counting template by strictly increasing generalized primes with count discrepancy at most one and simultaneous exponential-sum control; it supplies no ordinary-prime or selected Robin-source sign estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Published generalized-prime realization supplier

The inspected primary is [arXiv:2102.08478v2](https://arxiv.org/abs/2102.08478v2),
revised 17 June 2024, [versioned PDF](https://arxiv.org/pdf/2102.08478v2)
and [HTML](https://arxiv.org/html/2102.08478v2).
The PDF has 15 pages and SHA-256
`66b727b7b5b151844558b88c1495e1eca902b1c0ea01840b5e783f4b2ff0c9c8`.
Theorem 1.2 and equation (1.3) were inspected on printed p.2;
the formula was also checked against the HTML mathematical text.
The arXiv record and Crossref identify the publication as
*Mathematische Zeitschrift* 307 (2024), Article 62,
[DOI 10.1007/s00209-024-03526-4](https://doi.org/10.1007/s00209-024-03526-4).
The publisher's full text and the complete source proof are not
independently audited here. No source text is vendored or Lean
verification claimed.

## Exact reusable statement

Theorem 1.2 assumes that $F:[1,\infty)\to\mathbb R$ is nondecreasing,
right-continuous, unbounded, $F(1)=0$, and
$F(x)\ll x/\log x$. It gives an unbounded nondecreasing sequence
$\mathcal P=(q_j)$ of real generalized primes, with $q_j>1$, such that

$$
|\pi_{\mathcal P}(x)-F(x)|\le2
\qquad(x\ge1),
$$

and, simultaneously for all real $t$ and all $x\ge1$,

$$
\left|\sum_{q_j\le x}q_j^{-it}
       -\int_1^x u^{-it}\,dF(u)\right|
\ll\sqrt x+
\sqrt{\frac{x\log(|t|+1)}{\log(x+1)}}.
\tag{BV1}
$$

If $F$ is continuous, the sequence may be chosen strictly increasing
with $|\pi_{\mathcal P}(x)-F(x)|\le1$, retaining (BV1).
The implicit constant in (BV1) belongs to the chosen template;
no uniform constant over every admissible $F$ is asserted.
The count bound at $t=0$ is the separate stronger conclusion,
not the weaker $O(\sqrt x)$ obtained by using (BV1) alone.

The source's introduction explicitly attributes the predecessor
random approximation method to Diamond–Montgomery–Vorhauer,
*Beurling primes with large oscillation*,
[DOI 10.1007/s00208-005-0638-2](https://doi.org/10.1007/s00208-005-0638-2),
and its refinement to Zhang. This attribution was read in the
Broucke–Vindas primary; those predecessor proofs are not
independently verified here. Reuse Theorem 1.2 for realization rather
than reproducing any of these discretization constructions.

## Parameter correspondence for the existing FIB pulse source

Use the already constructed differentiable cumulative function $B$
of [FIB §261](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#261-精确-fibonacci-采样的相位盲区与单调脉冲模型),
before its integer-part projection $M=\lfloor B\rfloor$.
The source gives $B'(u)=1+O(u^{-1/4})$ and eventual positivity.
Choose $X>1$ in that eventual range and set

$$
F_B(x)=\begin{cases}
0,&1\le x\le X,\\
\displaystyle\int_X^x\frac{B'(u)}{\log u}\,du,&x>X.
\end{cases}
\tag{BV2}
$$

This $F_B$ is continuous, nondecreasing and unbounded, with
$F_B(1)=0$ and $F_B(x)\ll x/\log x$.
Apply Theorem 1.2 directly. Its strictly increasing generalized-prime
sequence has unit count atoms and $|\pi_{\mathcal P}-F_B|\le1$.
The realization is supplied by the literature theorem; neither the
pulse construction nor the random discretization is reproduced here.

Write $e(x)=\pi_{\mathcal P}(x)-F_B(x)$ and
$\vartheta_{\mathcal P}(x)=\sum_{q_j\le x}\log q_j$.
Stieltjes integration by parts gives, for $x\ge X$,

$$
\begin{aligned}
\vartheta_{\mathcal P}(x)-[B(x)-B(X)]
&=\log x\,e(x)-\int_1^x\frac{e(u)}u\,du,\\
\left|\vartheta_{\mathcal P}(x)-[B(x)-B(X)]\right|
&\le2\log x.
\end{aligned}
\tag{BV3}
$$

The lower boundary has zero logarithm; the constant $B(X)$ remains.
Thus the same existing continuous source has a published discrete
realization with logarithmically weighted prime mass accurate to
$O(\log x)$. This is stronger source information than a count made
from fractional atoms of weight $1/\log u$. The primes remain real
generalized primes, with no assertion that they are ordinary primes.

## Transport of the already computed forward response

For the original positive decreasing kernel
$w(u)=(1+\log u)/(u^2\log^2u)$, let

$$
\mathcal T_Y(A,h)=\int_0^h
[Y(A+r)-Y(A)-r]\frac{w(A+r)}{w(A)}\,dr.
\tag{BV4}
$$

The [versioned forward application](https://github.com/the-omega-institute/trureturing/blob/894bfc768450f651bc0de4a0bc748f4d0c0c240f/Library/Analytic/guthmaynard2024largevalues.md#reuse-the-existing-pulse-model-for-the-forward-limitation),
(F7)–(F11), already computes this response for the same
$M=\lfloor B\rfloor$. Its source, Fibonacci phase calculation and
subsequence are reused. Equation (BV3) and $|M-B|<1$ give, uniformly
for $A\ge X$ and $0<h\le A$,

$$
\mathcal T_{\vartheta_{\mathcal P}}(A,h)
=\mathcal T_M(A,h)+O(h\log(2A)).
\tag{BV5}
$$

Indeed, subtract the two cumulative increments. The constant $B(X)$
cancels; their difference is $O(\log(2A))$ throughout the window,
and $0<w(A+r)/w(A)\le1$.
At the already used $h=A^{4/5}$ the normalized transport error is

$$
\frac{O(h\log(2A))}{A^{11/10}}
=O(A^{-3/10}\log(2A))\longrightarrow0.
\tag{BV6}
$$

Consequently the existing divergence to $-\infty$ along
$A_j=F_{2j}$ transfers to $\mathcal T_{\vartheta_{\mathcal P}}$.
This is a paper application of the published supplier and the
previously computed response, with no new phase calculation or
Lean-certified refutation. It concerns generalized prime mass
$\vartheta_{\mathcal P}$; it does not establish the same conclusion
for ordinary $\vartheta$, ordinary $\psi$, or even generalized
$\psi_{\mathcal P}$, whose higher-power increments were not included
in (BV5).

## Remaining arithmetic interfaces

Theorem 1.2 supplies count realization and (BV1). It does not supply
CA own-price self-matching, selection by global Robin maximality,
a signed estimate for the complete prime-power response, or the
full Euler-layer tail at those selected sources. Those would require
separate joint estimates on the same generalized source; they are
not conclusions of the quoted theorem or (BV5).

For the original Robin task, the required source is an actual ordinary
integer with the stated selection and price conditions. The theorem
gives no map from the generalized-prime system to such a source,
no ordinary zeta functional equation, no Euler–Mascheroni
normalization for its generalized Euler product, and no effective
finite cutoff for the original consumer in
[CW4–CW5](../ArithSums/nicolas2025comparison.md#the-exact-forward-successor-on-the-same-original-integer).
These source obligations remain intact. Neither the generalized
realization nor a FIB re-encoding is an RH or Robin counterexample.
