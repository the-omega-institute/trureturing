---
slug: grunwald-pales-2024-gini-mean-comparison
bibkey: grunwaldpales2024gini
doi: null
url: https://arxiv.org/abs/2408.07658v1
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/GiniMeanEndpointComparison.result
---

# Endpoint comparison of Gini means on a bounded interval

## Problem

R. Grünwald and Zs. Páles, *Comparison of Gini means with fixed number of variables*, arXiv:2408.07658v1, §4, state verbatim:

> We conclude this paper by formulating two conjectures that we have not been able to verify. The first conjecture seems to be a natural extension of the formula for Γ2(I), if 0 < inf I < sup I < ∞.

Conjecture 1 states verbatim:

> Conjecture 1. Let n ≥ 3 and let I be a subinterval of R+ such that 0 < a := inf I < sup I =: b < ∞. Then Γn(I) = {((r, s), (p, q)) ∈ R² × R² | r + s ≤ p + q, G[n]r,s(a, …, a, b) ≤ G[n]p,q(a, …, a, b), and G[n]r,s(a, b, …, b) ≤ G[n]p,q(a, b, …, b)}.

Here $\Gamma_n(I)$ is the set of parameter pairs satisfying $G_{r,s}(x)\le G_{p,q}(x)$ for all $x\in I^n$. For $r\ne s$ and positive coordinates,

$$
G_{r,s}(x)=\left(\frac{\sum_{i=1}^n x_i^r}{\sum_{i=1}^n x_i^s}\right)^{1/(r-s)}.
$$

The journal bibliographic reference is *Results in Mathematics* 80 (2025), article 54; the quotations and locators refer to the arXiv version.

## Motivation

The conjecture would reduce a comparison on every tuple in a bounded positive interval to one parameter-sum inequality and two tests involving only the extreme endpoints. It extends the paper's two-variable description to $n\ge3$.

## Gap

The paper states both conjectures as unverified. Conjecture 1 proposes the bounded-interval description; Conjecture 2 concerns intervals with $\inf I=0$ or $\sup I=\infty$. The two endpoint tests do not certify comparisons at intermediate coordinate ratios.

## Route

Refute the $\supseteq$ inclusion of Conjecture 1 on the closed interval $I=[1,3]$ with distinct parameters. Choose

$$
n=3,\qquad (r,s)=(3,-1),\qquad (p,q)=(0,2),\qquad x=(1,1,5/3).
$$

Both parameter sums equal 2, and every coordinate of $x$ belongs to $[1,3]$. The means are nonnegative, so their order can be checked by taking fourth powers. The proof computes those powers exactly at the two extreme tuples and at $x$.

## Falsifier

The two endpoint tests hold strictly:

$$
G_{3,-1}(1,1,3)^4=\frac{87}{7}<\frac{121}{9}=G_{0,2}(1,1,3)^4,
$$

$$
G_{3,-1}(1,3,3)^4=33<\frac{361}{9}=G_{0,2}(1,3,3)^4.
$$

The comparison reverses inside the interval:

$$
G_{3,-1}(1,1,5/3)^4=\frac{895}{351}>\frac{1849}{729}=G_{0,2}(1,1,5/3)^4.
$$

The last inequality is the exact integer comparison $895\cdot729=652455>648999=1849\cdot351$. Thus the three proposed conditions hold but the pair is not in $\Gamma_3([1,3])$.

## Evidence

The public declarations in `D5/S3/ArithSums/GiniMeanEndpointComparison.lean` are `giniMean`, `lowTuple`, `highTuple`, `claim`, and `result`. The tuple `x` and every supporting lemma are private.

`giniMean r s x` is the real-power expression above for `x : Fin n → ℝ`. Its interpretation as the source's mean is restricted to positive coordinates and distinct parameters. `lowTuple n a b` places $b$ at the last index and $a$ elsewhere; `highTuple n a b` places $a$ at index zero and $b$ elsewhere.

`claim` quantifies over $n\ge3$, real endpoints $0<a<b$, and real parameters $r\ne s$, $p\ne q$. It asserts that the parameter-sum inequality and both endpoint comparisons imply the comparison for every `x : Fin n → ℝ` with coordinates in `Set.Icc a b`. This is the proposed $\supseteq$ inclusion on closed intervals, rather than an encoding of the full equality or of the equal-parameter formula.

`gini_low_rs`, `gini_low_pq`, `gini_high_rs`, `gini_high_pq`, `gini_x_rs`, and `gini_x_pq` establish the six fourth-power identities. `le_fourth` transfers fourth-power inequalities to nonnegative real numbers; the `nonneg_*` lemmas establish the nonnegativity used in the proof. The theorem `D5.S3.ArithSums.GiniMeanEndpointComparison.result` has type `¬ claim`. It instantiates the claim with the displayed witness, derives the false interior fourth-power inequality, and closes the contradiction by exact arithmetic. The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

1. **Proved (Lean) — Conjecture 1 fails.** The witness satisfies all three conditions of the conjectured description but violates comparison at $(1,1,5/3)$. Hence the proposed $\supseteq$ inclusion fails, and so does the equality asserted by Conjecture 1.

2. **Computed (numerical, not formalized) — further violations.** Further integer-parameter violations include $(r,s,p,q)=(-2,0,4,-6)$ on $[1,4]$ at $(1,13/8,13/8)$. These are computed observations, not additional Lean refutations.

3. **Computed (exact mathematical reasoning, not formalized) — ratio mechanism.** For positive coordinates, homogeneity gives $G_{r,s}(a y)=aG_{r,s}(y)$. Thus $(1,1,5/3)$ scales to $(a,a,5a/3)$, an endpoint configuration for a smaller interval. For the displayed three-variable parameters, comparison fails at ratio $5/3$ but holds at ratio 3. Passing the two tests at the extreme ratio $b/a$ therefore does not control all intermediate ratios; persistence of comparison as the ratio decreases is false.

4. **Open — candidate correction.** A candidate description replaces the two extreme-ratio tests by both tests at every $t\in(1,b/a]$, namely the configurations $(1,\ldots,1,t)$ and $(1,t,\ldots,t)$, together with $r+s\le p+q$. These tests are necessary for comparison on a closed bounded interval by homogeneity. Whether they are sufficient for all tuples and all $n\ge3$ is not proved.

5. **Open — Conjecture 2.** The conjecture for $\inf I=0$ or $\sup I=\infty$ is not settled by this result.

6. **Open — the bounded-interval comparison region.** The true description of $\Gamma_n(I)$ for bounded positive intervals is not settled by this result.

## ASSUMED-UNVERIFIED

The journal version's text is unverified. The quotations and their locators bind to arXiv:2408.07658v1, §4; no exhaustive literature or priority claim is established.

The additional numerical violations, general homogeneity argument, and sufficiency of the candidate all-ratios criterion are not formalized in the companion Lean module.
