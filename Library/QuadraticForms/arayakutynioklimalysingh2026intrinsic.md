---
bibkey: arayakutynioklimalysingh2026intrinsic
authors: "Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh"
year: 2026
title: "Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension"
doi: 10.48550/arXiv.2610.39674
url: https://arxiv.org/abs/2610.39674v1
claim: "Section 4.1 predicts that the probability-one affine-intersection intrinsic dimension of a deep-linear solution fiber equals its input dimension independently of width and depth."
strata_touched:
  - D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2610.39674

Source: https://arxiv.org/abs/2610.39674v1

## Source statements

The following are verbatim source-TeX excerpts, with macros retained. Page numbers
refer to the numbered PDF pages. Definition and theorem numbering differs from the
TeX-label numbering used in the problem description; the equations and sentences
identify the mathematical statements.

Page 5, random affine planes:

```tex
Equivalently, $\calU$ is obtained by taking the column space of a $p\times d$ matrix with i.i.d. $\calN(0,1)$ entries or the kernel of a $(p-d)\times p$ matrix with i.i.d. $\calN(0,1)$ entries.
```

```tex
If $d = p$, we set $\calV = \R^p$ a.s.
```

Page 5, equation (3):

```tex
We define the \emph{intrinsic dimension}
```

```tex
\dint(\Theta) := \inf \Big\{ d \ge 0 \colon \Pr[ \calV \cap \Theta \neq \emptyset ] = 1, \text{ for $\calV \sim \nu_d \times \calN(\0,\id_{p-d})$} \Big\}.
```

Page 21, Section 4.1:

```tex
We say $h\colon \R^{M_0}\to \R$ is a function implemented by an $L$-layer \emph{deep linear network} with architecture $\bm=(M_0,\dots,M_L) \in \mathbb N^{L+1}$ if there are weight matrices $\bW_\ell \in \R^{M_\ell\times M_{\ell-1}}$ and an ouput projection $\ba \in \R^{M_L}$, for $\ell\in [L]$, such that $h(\bx)= \ba^T \bW_L \bW_{L-1} \cdots \bW_1\bx$.
```

Page 22, equation (20), the displayed polynomial fiber:

```tex
\Theta=\{(\bb{W}_1, \dots, \bb{W}_L, \ba) \colon \bb{W}_1^T\bb{W}_2^T\cdots \bb{W}_L^T \ba = \bu_\star\}.
```

Page 23, the exact-value prediction:

```tex
As we will see in Section \ref{sec:Numerics}, numerical experiments suggest that $\dint(\Theta)=D$ in the deep linear case independently of the width and depth of the network.
```

The PDF sentence on page 23 reads:

> As we will see in Section 7, numerical experiments suggest that $d_{\mathsf{int}}(\Theta)=D$ in the deep linear case independently of the width and depth of the network.

The mathematical notation in these excerpts is defined in the source. In ordinary
notation the last assertion is $d_{\mathsf{int}}(\Theta)=D$.

## Encoding and scope

The finite sum of all matrix-entry indices and output-coordinate indices encodes the
bias-free tuple in equation (20) and Theorem 17. The inconsistent bias coordinates
in the paragraph following equation (20) are not part of that displayed tuple.
The architecture function records widths through the positive depth. Ordered matrix
multiplication gives the transpose-product fiber. Independent standard Gaussian
columns and offset implement the paper's stated generator; translating by the offset
or its perpendicular projection gives the same affine set. The infimum is taken in
ENat over dimensions from zero through the ambient cardinality.

The repository result negates the universal exact-value assertion using the scalar
one-layer unit-target fiber $wa=1$. Nonempty open miss events for points and lines
have positive Gaussian measure. In the line event the intersection equation has
negative discriminant. The proof excludes intrinsic dimensions zero and one; it does
not formalize the general-width lower bounds or a separate Haar/Gaussian equivalence.

## Computational evidence

The preregistration is https://github.com/the-omega-institute/trureturing/issues/26399.
Its exact checker is `check.py` under
`docs/reports/araya-kutyniok-li-maly-singh-2026-deep-linear-intrinsic-dimension/`
in https://github.com/the-omega-institute/trureturing-experiments,
commit `5fb8908a2eb5c3ec8cde5ca7ce1ebb9dd54fdacf`, SHA-256
`d28c887336061a38b9074c014b1662f0933a6f33f14ee20b966bb2dda43925a4`.
The recorded command `python3 check.py` exited 0 with `ALL_CHECKS_OK`. It checked
36 population-MSE instances, 24 signatures, 216 translated-plane maxima, rational
margins and scalar dimension counts through M=29. These finite checks are supporting
computations, not the probability proof.

## Literature boundary

The literature screen recorded on issue #26399 found no resolution in its searched
scope. Worldwide completeness and priority are ASSUMED-UNVERIFIED: rate-limited
citation APIs and bounded query results do not establish absence of follow-up work.
