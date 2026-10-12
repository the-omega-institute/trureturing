---
slug: faifman-polterovich-2026-centred-gaussian-dilation
bibkey: faifmanpolterovich2026faberkrahn
doi: 10.48550/arXiv.2607.21539
url: https://arxiv.org/abs/2607.21539v2
triage: theorem
motivation_gids:
  - D5/S3/Geometry/CentredGaussianDilationRefutation.result
---

# Centred convex bodies and Gaussian dilation

## Problem

D. Faifman and I. Polterovich, *The Faber–Krahn position of convex bodies and Gaussian measure inequalities*, arXiv:2607.21539v2, §5.2, p. 38, state verbatim:

> The B-theorem requires central symmetry. To prove Theorem 1.1, we circumvent this by proving a weaker concavity property of the Gaussian measure in a special case. However, we do not know a convex counterexample to the B-conjecture with its linear barycenter at the origin. Question 5.3. Let K ⊂ R^n be a convex body whose Lebesgue barycenter is at the origin. Is t ↦ γ_n(e^t K) log-concave? More generally, is t ↦ γ_n(e^{tS} K) log-concave for every symmetric matrix S?

## Motivation

Central symmetry implies zero Lebesgue barycenter, but zero barycenter does not imply central symmetry. The question asks whether this weaker centering condition still suffices for the Gaussian B-conjecture. A scalar counterexample also refutes the matrix clause because the identity matrix is symmetric.

## Gap

The passage distinguishes its weaker concavity theorem from the B-conjecture and asks for a centred convex counterexample. The source locator is arXiv:2607.21539v2, §5.2, p. 38. Independent verification of the author text and an exhaustive literature or priority claim remain ASSUMED-UNVERIFIED.

## Route

In $\mathbb R^{16}$, write $z=(x,y)$ with $y\in\mathbb R^{15}$ and put

$$
K=\{z:-1\le z_0\le16,\quad |z_i|\le10(16-z_0)\ \text{for }i\ne0\}.
$$

This is a compact convex pyramid with nonempty interior. Its transverse sections are symmetric boxes, so each transverse first moment vanishes. The remaining first moment is

$$
\int_K z_0\,dz=\int_{-1}^{16}x\,[20(16-x)]^{15}\,dx=0.
$$

An antiderivative is $20^{15}[-(16-x)^{16}+(16-x)^{17}/17]$, with equal endpoint values. Thus the Lebesgue barycenter is the origin.

Let $G(a,b)=\gamma_1([a,b])$. The boxes

$$
[-1/4,7/2]\times[-5,5]^{15}\subseteq K/4,
\qquad [-1,7/2]\times[-5,5]^{15}\subseteq K
$$

give product-measure lower bounds. Also $K/2\subseteq\{z:z_0\ge-1/2\}$ gives a one-dimensional upper bound.

For $c=(2\pi)^{-1/2}$, the certified bounds are $997/2500<c<2/5$. On $[0,1]$,

$$
e^{-u^2/2}\ge1-u^2/2+u^4/8-u^6/48-5u^8/1536.
$$

Integration gives lower bounds for the Gaussian mass between zero and $1/4$ or $1$. Symmetry gives half the mass on either side of zero. The exponential moment gives

$$
\gamma_1([a,\infty))\le e^{-a^2/2}\quad(a\ge0).
$$

Finite exponential sums certify tails less than $1/350$ at $7/2$ and less than $1/16000$ at $5$. Consequently,

$$
G(-1/4,7/2)>1191/2000,\quad
G(-1,7/2)>419/500,\quad
G(-5,5)>7999/8000,
$$

and $G(-5,5)^{15}>7985/8000$. These estimates suffice for the strict contradiction below.

## Falsifier

The exact certified margins are

$$
\gamma_{16}(K/4)>594/1000,\qquad
\gamma_{16}(K)>836/1000,\qquad
\gamma_{16}(K/2)<7/10.
$$

Thus

$$
\gamma_{16}(K/2)^2<49/100
<\frac{594}{1000}\frac{836}{1000}
=\frac{62073}{125000}
<\gamma_{16}(K/4)\gamma_{16}(K).
$$

Log-concavity at $t_1=-\log4$, $t_2=0$, with equal weights, would give the opposite inequality because their midpoint is $-\log2$. The matrix version fails for $S=I_{16}$.

## Evidence

The public declarations in `D5/S3/Geometry/CentredGaussianDilationRefutation.lean` are `gaussianMeasure`, `IsConvexBody`, `BarycenterZero`, `claim`, and `result`. All supporting declarations are private.

`gaussianMeasure n` is the product of $n$ copies of `gaussianReal 0 1` on `Fin n → ℝ`. `IsConvexBody` requires real convexity, compactness, and nonempty interior. `BarycenterZero` requires every coordinate's Lebesgue set integral to vanish. For a convex body these integrals exist, and its volume is positive and finite, so the condition is equivalent to zero normalized Lebesgue barycenter.

`claim` requires concavity on the entire real line of the logarithm of the real Gaussian mass of `Real.exp t • K`, for every dimension and every such centred convex body. The theorem `D5.S3.Geometry.CentredGaussianDilationRefutation.result` has type `¬ claim`.

The geometric lemmas establish compact convexity, interior, scaled membership and box inclusions. `barycenter` uses product Lebesgue measure and the exact polynomial integral. `gaussian_box_products` and `dilation_bounds` establish the rational Gaussian estimates. The final logarithmic comparison uses positive finite masses; positivity at half scale follows from inclusion of the quarter-scale pyramid.

The axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom.

## Triage

### What the settlement shows

1. **Proved (Lean) — the centred convex counterexample.** The 16-dimensional pyramid is a convex body with Lebesgue barycenter at the origin and violates log-concavity of $t\mapsto\gamma_{16}(e^tK)$. This answers both clauses of Question 5.3 negatively, with $S=I_{16}$, and supplies the convex counterexample with linear barycenter at the origin requested in §5.2.

2. **Mechanism (reasoning) — a far apex.** At Gaussian scales for which the apex and transverse faces remain far from the origin, a centred pyramid approximates the half-space $\{x\ge-1\}$. Its dilated Gaussian mass is then close to $\Phi(e^t)$, whose logarithm is convex for sufficiently negative $t$. For a pyramid of height $H$ in dimension $n$, the Lebesgue centroid lies $H/(n+1)$ from the base; keeping the base near the origin and the apex far away therefore favours large dimension. This half-space approximation concerns an intermediate scale regime, not the limit $t\to-\infty$ of a fixed bounded body.

3. **Computed (numerical, not formalized) — centred cones.** The supplied numerical observations give no violation for centred cones in dimension 2 and violations of size about $10^{-4}$ from dimension 3 upward. These observations concern the examined cone family; they neither exclude other two-dimensional bodies nor certify a three-dimensional example in Lean.

4. **Open — smallest dimension.** Whether a counterexample exists in dimension 2, and whether dimension 3 is minimal, remain unsettled here. The formal result supplies an upper bound of 16 on the smallest dimension.

5. **Open — Gaussian centering.** Whether zero Gaussian centroid, rather than zero Lebesgue barycenter, suffices for the B-conjecture remains unsettled. The two centering conditions are different; the pyramid's Lebesgue first moments do not establish zero Gaussian first moments.

## ASSUMED-UNVERIFIED

The author-text locator and quotation are supplied with the statement and have not been independently retrieved. An exhaustive literature or priority claim is unverified. The cone computations and the half-space mechanism are not formalized; no numerical experiment data or exhaustive two-dimensional conclusion is asserted by the Lean theorem.
