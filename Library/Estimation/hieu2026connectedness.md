---
bibkey: hieu2026connectedness
authors: Vu Trung Hieu
year: 2026
title: "A connectedness result for convex polynomial multi-objective optimization without boundedness"
doi: null
url: https://arxiv.org/abs/2610.01029v1
claim: "Section 4.3 asks whether the weak Pareto solution set remains connected for general continuous convex data on a closed convex feasible set; Theorem 1 proves connectedness for convex polynomial data without boundedness or constraint qualification."
strata_touched:
  - D5/S3/Analytic/Convexity/WeakParetoDisconnected
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2610.01029v1>.
Vu Trung Hieu, *A connectedness result for convex polynomial multi-objective optimization without boundedness*, arXiv:2610.01029v1 (2026), §4.3 “Scope of the hypotheses”.

The paper asks whether $\mathrm{Sol}^w(K,f)$ is connected when $K$ is closed and convex and the objective functions are convex and continuous without the polynomial assumption. It states that no explicit example of a disconnected weak Pareto solution set is known, and that Theorem 1 rules out such an example for convex polynomial data.

## Connectedness question

For the weak Pareto solution set

$$
\mathrm{Sol}^w(K,f)=\{z\in K:\nexists u\in K\text{ with }f_i(u)<f_i(z)\text{ for every }i\},
$$

Theorem 1 gives connectedness for convex polynomial objectives on a closed convex feasible set without boundedness or a constraint qualification. The §4.3 question concerns continuous convex objectives in the general case.

**Repository-derived counterexample.** The companion Lean module uses
$K=[0,\infty)\times[0,2]$ and
$h(x)=\sqrt{x^2+1}-x$. Its objectives are
$f_1(x,y)=y^2$ and
$f_2(x,y)=\bigl(\max(h(x)-y/2,0)\bigr)^2-y/2$.

The weak Pareto set has the proved boundary pieces

$$
A=\{(x,0):x\ge 0\},\qquad
B=\{(x,y):x\ge0,\ 2h(x)\le y\le2\},
$$

in the sense established by the two boundary lemmas: every point on either boundary is weak Pareto, and every weak Pareto point lies on one of them. A point with $0<y<2h(x)$ is strictly dominated by $(1/v,v)$ for a suitable $v>0$. Since $h(x)>0$, the open sets $\{y<h(x)\}$ and $\{h(x)<y\}$ separate the two nonempty parts of the weak Pareto set.

## Motivation

The example answers the paper's §4.3 question in the continuous convex setting. The analytic arguments below show that the two pieces approach one another as $x\to\infty$ and that $C^1$ regularity, semi-algebraicity, and attainment of every nonnegative scalarization do not restore connectedness.

## Gap

The paper states that no explicit example of a disconnected weak Pareto solution set was known. Warburton's connectedness theorem for bounded $K$ does not apply because this $K$ is unbounded. Helbig's result for compact lower level sets does not apply either. The example therefore fills the stated general convex gap while retaining a closed convex feasible set and continuous convex objectives.

## Route

Use the closed convex strip

$$
K=\{(x,y)\in\mathbb R^2:0\le x,\ 0\le y\le2\}
$$

and the function $h(x)=\sqrt{x^2+1}-x$. The identity $h(x)>0$ separates the axes and upper boundary $y=2h(x)$. Convexity of $h$ follows from the Euclidean norm representation $h(x)=\|(x,1)\|-x$; convexity of $f_1$ follows from Mathlib's even-power convexity and affine composition, and convexity of $f_2$ follows from Mathlib's supremum, nonnegative-power, and affine-subtraction results. Both objectives are continuous.

For a point in the open gap, write the second objective as $d$. Choose
$v=(\max(0,-2d)+y)/2$; then $0<v<y$, and $(1/v,v)\in K$ strictly improves both objectives. The reciprocal estimate $h(1/v)<v/2$ makes the second objective strict. Thus only the two boundary pieces can be weak Pareto. The open-set separation then contradicts `IsPreconnected`.

## Falsifier

The universal assertion, with $n,m\ge1$, is falsified by $n=m=2$, the strip $K$ above, and the two displayed objectives. The module proves that $K$ is nonempty, closed, and convex, and that each objective is continuous and convex on the full Euclidean space. It proves non-preconnectedness of the resulting weak Pareto set, so no boundedness or constraint qualification is used in the counterexample.

## Evidence

The public declarations are `weakPareto`, `claim`, and `result`; the instance data and supporting lemmas are private to
`D5/S3/Analytic/Convexity/WeakParetoDisconnected.lean`.

The Lean proof establishes the instance properties, the two boundary inclusions (`weak_of_boundary` and `weak_boundary`), strict domination throughout the open gap (`dominated_in_gap`), and non-preconnectedness (`not_preconnected`). The theorem
`D5.S3.Analytic.Convexity.WeakParetoDisconnected.result` proves `¬ claim`.

The accepted axiom closure is
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$; there is no `sorry` or additional axiom. The proof uses the square-root identities, Euclidean norm convexity, and exact real inequalities in Mathlib.

The module does not separately name an equality theorem for $W=A\cup B$; the two boundary lemmas together with the gap-domination lemma provide the corresponding characterization pieces used by the refutation.

## Triage

### What the settlement shows

1. **Proved (Lean) — disconnected weak Pareto set.** The displayed closed convex strip and continuous convex objectives satisfy the universal hypotheses, while their weak Pareto set is not preconnected.

2. **Proved (Lean) — boundary characterization pieces.** Every feasible point with $y=0$ or $y\ge2h(x)$ is weak Pareto, and every weak Pareto point satisfies $y=0$ or $y\ge2h(x)$. Every feasible point in the remaining positive gap has a strict dominator.

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
