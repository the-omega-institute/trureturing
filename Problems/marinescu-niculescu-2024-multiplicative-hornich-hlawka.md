---
slug: marinescu-niculescu-2024-multiplicative-hornich-hlawka
bibkey: marinescuniculescu2024survey
doi: null
url: https://arxiv.org/abs/2407.03278v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/MultiplicativeHornichHlawka.result
---

# The multiplicative Hornich–Hlawka inequality in inner product spaces

## Problem

D.-Ş. Marinescu, C. P. Niculescu, *A survey of the Hornich-Hlawka inequality*, arXiv:2407.03278v1, §6, the paragraph applying Theorem 8 to the logarithm, states:

> Applying Theorem 8 to the function f (x) = ln(1 + x) one obtains the multiplicative analog of the inequality (2.1), (1 + |x|)(1 + |y|)(1 + |z|)(1 + |x + y + z|) ≥ (1 + |x + y|)(1 + |y + z|)(1 + |z + x|), for all x, y, z ∈ R. No extension of this remark to the case of inner product spaces is known.

The claim replaces absolute values by norms in every real or complex inner product space, with no finite-dimensionality or completeness assumption.

## Motivation

A Hornich–Hlawka inequality for the logarithmic transform would yield the product inequality by exponentiation. An inner-product extension requires simultaneous control of the linear, quadratic, and cubic norm terms in the product expansion.

## Gap

The additive Hornich–Hlawka bound controls only the linear term of the product expansion, so the product inequality does not follow from that bound alone. For example, the nonnegative numbers $a=b=1$, $c=d=0$, and $u=v=w=2/3$ have equal sums, but

$$
(1+a)(1+b)(1+c)(1+d)=4<125/27=(1+u)(1+v)(1+w).
$$

This is an algebraic illustration, not a vector configuration. Applying the increasing logarithm to a sum inequality does not give a sum-of-logarithms inequality.

The survey states that no inner-product-space extension of this multiplicative remark is known. Its scalar case follows from Theorem 8, whose derivative conditions are $f'\ge0$, $f''\le0$, and $f'''\ge0$. The logarithm satisfies these conditions, but the survey's power-function transfer does not apply to $\ln(1+t)$.

Ressel, *Journal of Mathematical Inequalities* **9** (2015), 883–888, proves the real-line Bernstein-function inequality and a Euclidean square-root case. This abstract-level comparison does not establish the logarithmic extension. El Idrissi–Zoubeir, arXiv:2601.18768, prove a Ptolemy-type strengthening, $\|x\|\|y\|+\|z\|\|x+y+z\|\ge\|x+z\|\|y+z\|$; the three cyclic instances provide the quadratic comparisons used here.

## Route

Set

$$
a=\|x\|,\quad b=\|y\|,\quad c=\|z\|,\quad d=\|x+y+z\|,
\qquad u=\|x+y\|,\quad v=\|y+z\|,\quad w=\|z+x\|.
$$

All seven numbers are nonnegative. The private lemma `ptolemy_sum` applies Mathlib's `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist` to the four points $0,x,x+y,x+y+z$. Cyclic permutations give

$$
uv\le ac+bd,\qquad vw\le ab+cd,\qquad wu\le bc+ad.
$$

Their sum is the second elementary symmetric function comparison (`hpair` in `scalar_inequality`). The private lemma `frechet_identity` proves

$$
a^2+b^2+c^2+d^2=u^2+v^2+w^2.
$$

Combining this identity with `hpair` bounds $(u+v+w)^2$ by $(a+b+c+d)^2`; nonnegativity yields $u+v+w\le a+b+c+d$ (`hsum`).

Write $S=a+b+c+d$ and $R=abc+abd+acd+bcd$. The private lemma `norm_triangle_four` and the ordinary triangle inequality give each of $a,b,c,d$ at most the sum of the other three. Multiplying these four inequalities by the corresponding nonnegative norm and adding gives

$$
S^2-2(a^2+b^2+c^2+d^2)\ge0
$$

(`hdefect`). The polynomial identity

$$
R^2-(ab+cd)(ac+bd)(bc+ad)
=abcd\bigl(S^2-2(a^2+b^2+c^2+d^2)\bigr)
$$

is proved by `ring` (`hfactor`). Multiplying the three Ptolemy bounds gives $(uvw)^2\le(ab+cd)(ac+bd)(bc+ad)$. The identity and `hdefect` then give $uvw\le R$ (`hcubic`). Comparing the three elementary symmetric functions and the nonnegative extra term $abcd$ proves

$$
(1+u)(1+v)(1+w)\le(1+a)(1+b)(1+c)(1+d).
$$

The theorem `result` equips the carrier with its underlying real inner product using `InnerProductSpace.rclikeToReal`, so the argument applies to both real and complex inner product spaces. Every inequality and identity in this route is a Lean step; elementary symmetric function terminology describes their organization and is not a separate Lean definition.

## Falsifier

A falsifier would be a real or complex inner product space and three vectors for which the product of the three pair-sum factors strictly exceeds the product of the four single-vector and total-sum factors. The theorem `result : claim` rules out this strict reverse inequality under exactly the carrier and typeclass assumptions in `claim`.

## Evidence

The public declarations in `D5/S3/Geometry/MultiplicativeHornichHlawka.lean` are `claim` and `result`; `scalar_inequality`, `ptolemy_sum`, `frechet_identity`, and `norm_triangle_four` are private. The theorem `D5.S3.Geometry.MultiplicativeHornichHlawka.result` has type `claim`.

The definition `claim : Prop` quantifies over a scalar type with `RCLike`, a carrier with `NormedAddCommGroup` and `InnerProductSpace`, and all three vectors. It asserts the multiplicative inequality with the pair-sum product on the left. The axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. The module contains no theorem about arbitrary Hornich–Hlawka normed spaces, arbitrary Bernstein functions, or equality classification.

## Triage

1. **Proved (Lean) — inner-product extension.** The multiplicative inequality holds in every real or complex inner product space, for all triples of vectors, without dimension or completeness restrictions.

2. **Proved (mechanism in Lean; symmetric-function interpretation by reasoning).** Ptolemy controls the second elementary symmetric function (`hpair`); Fréchet plus Ptolemy controls the first (`hsum_sq`, `hsum`); the cubic identity and triangle inequalities control the third (`hfactor`, `hdefect`, `hcubic`). All of these comparisons and the final product comparison are in `scalar_inequality`. Their description as three elementary symmetric function comparisons is explanatory reasoning, not an additional named theorem.

3. **Open — general Hornich–Hlawka normed spaces.** Whether the multiplicative inequality holds in every normed space satisfying the additive Hornich–Hlawka inequality, including the class of subspaces of $L^1$, is not settled by this module. The proof uses inner-product Ptolemy and Fréchet identities.

4. **Open — Bernstein-function extension.** Whether the Hornich–Hlawka inequality for $f(\|\cdot\|)$ holds in inner product spaces for every Bernstein function $f$ is not established by this module. The logarithmic case gives the proved $(1+\|\cdot\|)$ product inequality by exponentiation; the module does not formalize that logarithmic reformulation or a general function-transfer theorem.

5. **Open — equality cases.** A complete classification of triples giving equality is not proved in the module. The product inequality alone does not provide such a classification.

## ASSUMED-UNVERIFIED

The journal version of the survey and the full text of Ressel (2015) are unverified. The survey evidence binds to arXiv:2407.03278v1, §6; the Ressel evidence is limited to its abstract.
