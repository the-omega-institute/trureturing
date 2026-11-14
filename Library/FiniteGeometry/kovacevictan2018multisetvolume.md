---
bibkey: kovacevictan2018multisetvolume
authors: M. Kovačević; D. Tan
year: 2018
title: "Codes in the Space of Multisets—Coding for Permutation Channels with Impairments"
doi: null
url: https://arxiv.org/html/1612.08837v5
claim: "Equation (4) uses the larger signed mass; Lemma 2, equation (17), gives the constrained simplex-difference volume r^m/m! times binomial(2m,m) by orthant products."
strata_touched:
  - D5/S3/Geometry/BooleanRotationCodebook
license: citation-only
triage: anchor
---

# Constrained multiset bodies and simplex differences

## Source and shape correspondence

M. Kovačević and D. Tan, *Codes in the Space of Multisets—Coding for
Permutation Channels with Impairments*, [arXiv:1612.08837v5](https://arxiv.org/html/1612.08837v5)
(21 June 2018), equation (4), uses the maximum of positive and negative
coordinate masses. Lemma 2, equation (17), states, for integers $r,m\ge 1$,

$$
\operatorname{Vol}(S_m^{\mathrm{con}}(r))
 = \frac{r^m}{m!}\binom{2m}{m}.
$$

Here $S_m^{\mathrm{con}}(r)$ is the convex hull of the integer ball for that
signed-mass distance. Its intersection with a chamber having $j$ positive
coordinates is a product of simplices of dimensions $j$ and $m-j$.
The source sums their volumes using $\sum_j\binom mj^2=\binom{2m}{m}$.
Thus both the volume formula and this orthant-product argument are established
precedents.

For $\Delta_m=\{u\in\mathbb R^m:u_i\ge0,\sum_i u_i\le1\}$, the real body
with positive and negative masses each at most $\epsilon>0$ is
$\epsilon(\Delta_m-\Delta_m)$. At integer radius it is the source's constrained
body; dilation extends the same volume formula to every positive real radius.
The theorem `D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume`
formalizes this calculation and includes dimension zero. The formula and
orthant decomposition are not new mathematical claims of the rotation model.

## Classical difference-body relation and limits

Andrea Colesanti, *Functional inequalities related to the Rogers–Shephard
inequality*, [arXiv:math/0512098v1](https://arxiv.org/html/math/0512098v1),
introduction, equation (5), states the classical inequality

$$
\operatorname{Vol}(K-K)\le\binom{2m}{m}\operatorname{Vol}(K)
$$

for convex bodies in dimension $m\ge2$, with equality if and only if $K$ is a
simplex. Applied to $\Delta_m$, this is the same volume formula. This citation
is to Colesanti's statement; it does not represent a reading of the original
Rogers–Shephard paper.

These references concern Euclidean shape families and their volumes. They do
not supply the circular no-wrap lemma, the common codeword for all Boolean
queries, or the fixed literal rotation decoder and its codebook bounds.
