---
slug: hieu-2026-weak-pareto-connectedness
bibkey: hieu2026connectedness
doi: null
url: https://arxiv.org/abs/2610.01029v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Convexity/WeakParetoDisconnected.result
---

# Connectedness of weak Pareto solutions for continuous convex data

## Problem

Vu Trung Hieu, *A connectedness result for convex polynomial multi-objective optimization without boundedness*, arXiv:2610.01029v1 (2026-10-01), §4.3 “Scope of the hypotheses”, asks:

> whether $\mathrm{Sol}^w(K,f)$ is still connected in the general convex case, with $K$ closed convex and the $f_i$ convex and continuous but not necessarily polynomial

The paper states:

> no explicit example of a disconnected weak Pareto solution set is known

and that Theorem 1

> shows that no such example can have convex polynomial data.

The theorem in the paper proves connectedness for convex polynomial data without boundedness or a constraint qualification. The question is whether the conclusion survives for general continuous convex objectives.

## Motivation

The formal counterexample addresses the stated general-convex gap while retaining a closed convex feasible set. It also tests whether smoothness or semi-algebraic data, by themselves, can replace the polynomial hypothesis.

## Gap

The paper states that no example of a disconnected weak Pareto solution set was known. Warburton's connectedness theorem for bounded $K$ does not apply because the feasible strip below is unbounded. Helbig's result for compact lower level sets does not apply either. The example therefore targets the hypotheses left open in §4.3.

## Route

Let

$$
K=[0,\infty)\times[0,2],\qquad h(x)=\sqrt{x^2+1}-x,
$$

and define

$$
f_1(x,y)=y^2,\qquad
f_2(x,y)=\bigl(\max(h(x)-y/2,0)\bigr)^2-y/2.
$$

The Lean instance is the set $K$ of points with $0\le x$, $0\le y$, and $y\le2$. The function $h$ is positive and convex, with $h(x)=\|(x,1)\|-x$; pinned Mathlib norm convexity, affine composition, even-power convexity, supremum, nonnegative powers, and subtraction of affine terms give convexity of $f_1$ and $f_2$. Both objectives are continuous on the whole Euclidean space.

For a point with $0<y<2h(x)$, the proof chooses $v=(\max(0,-2d)+y)/2$, where $d=f_2(x,y)$. It shows $0<v<y$, $(1/v,v)\in K$, and that this point is strictly smaller in both objectives. The reciprocal inequality $h(1/v)<v/2$ gives strict improvement in the second objective.

The remaining boundary pieces are

$$
A=\{(x,0):x\ge0\},\qquad
B=\{(x,y):x\ge0,\ 2h(x)\le y\le2\}.
$$

The Lean lemmas prove that every point of $A$ or $B$ is weak Pareto and that every weak Pareto point lies in $A\cup B$. The open sets $\{y<h(x)\}$ and $\{h(x)<y\}$ contain the two nonempty parts and cover the weak Pareto set, so it is not preconnected.

## Falsifier

The universal connectedness claim, with $n,m\ge1$, is falsified by $n=m=2$, the displayed strip, and the displayed objectives. The module proves that $K$ is nonempty, closed, and convex, and that both objectives are continuous and convex on the full Euclidean space. It then proves that the weak Pareto solution set is not preconnected. No boundedness or constraint qualification is assumed.

## Evidence

The public declarations in `D5/S3/Analytic/Convexity/WeakParetoDisconnected.lean` are `weakPareto`, `claim`, and `result`; the instance data and supporting lemmas are private.

The Lean proof establishes the instance properties, the two boundary characterization directions (`weak_of_boundary` and `weak_boundary`), strict domination in the open gap (`dominated_in_gap`), and non-preconnectedness (`not_preconnected`). The theorem `D5.S3.Analytic.Convexity.WeakParetoDisconnected.result` has type `¬ claim`.

The accepted axiom closure is
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. The module does not expose a separate equality theorem for $W=A\cup B$; the boundary directions and the gap-domination lemma provide the proved characterization pieces used in the refutation.

## Triage

### What the settlement shows

1. **Proved (Lean) — the instance and non-preconnectedness.** The strip is nonempty, closed, and convex; both objectives are continuous and convex; and the resulting weak Pareto set is not preconnected.

2. **Proved (Lean) — characterization pieces.** Every feasible point with $y=0$ or $y\ge2h(x)$ is weak Pareto, while every weak Pareto point satisfies one of those alternatives. Every feasible point with $0<y<2h(x)$ has an explicit strict dominator.

3. **Proved (analytic argument, not in Lean) — asymptotic separation and regularity.** Rationalization gives
   $h(x)=1/(\sqrt{x^2+1}+x)$ for $x\ge0$, hence $h(x)\to0$ as $x\to\infty$. The distance from $(x,2h(x))\in B$ to $(x,0)\in A$ is $2h(x)$, tending to zero, although the Lean open-set separation holds at every finite point. The function $h$ is smooth since $x^2+1>0$. The function $\phi(t)=\max(t,0)^2$ is $C^1$: its derivative is $2\max(t,0)$, including derivative zero at $t=0$. Thus $f_1$ and $f_2=\phi(h(x)-y/2)-y/2$ are $C^1$. The graph of $h$ is described by $t+x\ge0$ and $(t+x)^2=x^2+1$; the two cases defining $\phi$ are polynomial. Composition and polynomial operations preserve semi-algebraicity, so the objectives and strip are semi-algebraic. Neither $C^1$ regularity nor semi-algebraicity alone therefore guarantees connectedness in this setting.

4. **Proved (analytic argument, not in Lean) — every scalarization attains a minimum.** Let $\alpha,\beta\ge0$ be not both zero. For $\alpha,\beta>0$, set

   $$
   y_*=\min\left(2,\frac{\beta}{4\alpha}\right)>0.
   $$

   On $K$, the nonnegative square term gives

   $$
   \alpha f_1(x,y)+\beta f_2(x,y)
   \ge \alpha y^2-\frac{\beta y}{2}
   \ge \alpha y_*^2-\frac{\beta y_*}{2}.
   $$

   The second inequality follows by completing the square,
   $\alpha y^2-\beta y/2=\alpha(y-\beta/(4\alpha))^2-\beta^2/(16\alpha)$,
   and minimizing on $0\le y\le2$. Since
   $h'(x)=x/\sqrt{x^2+1}-1<0$ and $h(1/y_*)<y_*/2$ (`h_reciprocal`), the positive-part term vanishes on the whole ray $x\ge1/y_*,\ y=y_*$. Every feasible point on that ray attains the displayed bound. More precisely, equality requires $y=y_*$ and $h(x)\le y_*/2$; squaring the latter inequality (both sides of $\sqrt{x^2+1}\le x+y_*/2$ are nonnegative) gives the full minimizer ray $x\ge1/y_*-y_*/4,\ y=y_*$. Its endpoint is nonnegative since $y_*\le2$.

   For $\alpha>0,\beta=0$, the minimum is zero, attained at $(0,0)$ and on the whole ray $x\ge0,\ y=0$. For $\alpha=0,\beta>0$, the lower bound $f_2\ge-y/2\ge-1$ is attained at $(0,2)$ and on the whole ray $x\ge0,\ y=2$, because $h(x)\le h(0)=1$. Equality forces $y=2$, so this is the full minimizer set. All nonzero nonnegative scalarizations thus have unbounded minimizer rays. Attainment of every scalarization does not imply connectedness of the weak Pareto set.

5. **Open — neighboring question.** The Pareto (non-weak) half of Yen's Question 9.8 for convex polynomials is not settled by this delivery.

## ASSUMED-UNVERIFIED

Zhong–Fan, *Journal of Guangxi Normal University* 39(3) (2021), 62–68, is reported in its abstract to prove connectedness on unbounded sets via upper semicontinuity of the scalarized solution map. Only the abstract was read; applicability to this instance remains unresolved until the actual hypotheses are checked. Scalarization attainment is established above, so non-attainment cannot explain any applicability boundary.

The asymptotic limit, $C^1$ regularity, semi-algebraicity, and scalarization attainment above are analytic arguments, not Lean results. The literature's specific connectedness mechanisms are not verified by this delivery.
