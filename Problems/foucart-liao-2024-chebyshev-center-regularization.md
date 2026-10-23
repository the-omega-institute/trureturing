---
slug: foucart-liao-2024-chebyshev-center-regularization
bibkey: foucartliao2024sprocedure
doi: 10.1007/978-3-031-66497-7_1
url: https://arxiv.org/abs/2310.09677v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.result
---

# Foucart–Liao's Chebyshev-center regularization question

## Problem

S. Foucart and C. Liao, *S-Procedure Relaxation: a Case of Exactness
Involving Chebyshev Centers*, arXiv:2310.09677v1, in *Explorations in
the Mathematics of Data Science* (Springer, 2024),
DOI 10.1007/978-3-031-66497-7_1, §5 “Some Open Questions”, Question 2:

> Is the Chebyshev center always obtained via regularization?

The authors' gloss is:

> From [10], we know that the answer is affirmative under the specific conditions mentioned above, since the Chebyshev center equals the regularizer $f_{\tau_\sharp}$ with parameter $\tau_\sharp\in(0,1)$ satisfying the implicit equation (9). Without the specific conditions, we also know from [8] that the answer is affirmative if one considered the complex setting rather than the real setting.

The section takes $Q=\mathrm{Id}_H$ and, in (25),
$\mathcal K=\{f\in H:\|Pf\|_H\leq\varepsilon\}$ and
$\mathcal E=\{e\in\mathbb R^m:\|e\|_2\leq\varepsilon\}$.
The “specific conditions” are that $P$ is an orthogonal projector
and $\Lambda\Lambda^*=\mathrm{Id}_m$.
Equation (8) defines

$$
f_\tau=\operatorname{argmin}_f
\bigl((1-\tau)\|Pf\|^2+\tau\|y-\Lambda f\|^2\bigr).
$$

The Lean `claim` quantifies over finite-dimensional real Euclidean
spaces, linear $P$ and $\Lambda$, data $y$, and positive bounds
$\varepsilon,\eta$. For every nonempty bounded feasible set
$C=\{f:\|Pf\|\leq\varepsilon,\ \|y-\Lambda f\|\leq\eta\}$,
it asks whether every Chebyshev center minimizes this objective for
some $\tau\in(0,1)$. The counterexample uses $\varepsilon=\eta=1$,
so it also addresses the equal-bound setting of (25).

## Motivation

The section describes questions “to which we do not know the
answers—we cannot even foretell if any of them are likely to be
easily solved”. The positive result under the specific conditions
does not settle the unrestricted real case. The declaration
`D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.result`
proves `¬ claim` while retaining an orthogonal-projector $P$.

## Gap

Preregistration [#15463](https://github.com/the-omega-institute/trureturing/issues/15463)
identifies the tier-1 question. Foucart–Liao, arXiv:2401.11112,
concerns the global setting only. Foucart–Hengartner,
arXiv:2406.14418, and Lin–Du, arXiv:2506.00704, do not answer this
local-center question. These references do not establish exhaustive
priority. The source note is `Library/Estimation/foucartliao2024sprocedure.md`.

**ASSUMED-UNVERIFIED:** classical work on Chebyshev centers of
intersections of two ellipsoids, including Beck–Eldar (2007) and
follow-ups, has not been checked for an earlier real instance whose
center lies on no regularization path.

## Route

Take $H=\mathbb R^2$,

$$
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
\Lambda=\begin{pmatrix}1/2&-1/2\\0&1\end{pmatrix},\qquad
y=(1,0),\qquad \varepsilon=\eta=1.
$$

Here $P$ is an orthogonal projector, $\Lambda$ is invertible, and
$\Lambda\Lambda^*=\left(\begin{smallmatrix}1/2&-1/2\\-1/2&1\end{smallmatrix}\right)
\ne\mathrm{Id}_2$. In coordinates $f=(x,z)$, feasibility is
$x^2\leq1$ and $g(x,z)\leq0$, where

$$
g=(x-z-2)^2+4z^2-4,\qquad
q=(x-3/5)^2+(z+1/5)^2-4/5.
$$

The containment certificate is

$$
10(4-x+z)q=(x-1)(4-x+7z)^2+(17-11x+2z)g.
$$

Feasibility implies $x\leq1$, $z\geq-1$, $4-x+z>0$, and
$17-11x+2z\geq0$, hence $q\leq0$.
The feasible contact points

$$
A=(1,3/5),\qquad B=(-1/5,-3/5),\qquad D=(1,-1)
$$

all have squared distance $4/5$ from $c_*=(3/5,-1/5)$.
Their positive weights $5/12,1/3,1/4$ sum to one and give, for any $c$,

$$
\frac5{12}\|A-c\|^2+\frac13\|B-c\|^2+\frac14\|D-c\|^2
=\frac45+\|c-c_*\|^2.
$$

Thus every enclosing ball has squared radius at least $4/5$,
and $c_*$ is the unique center with radius $\sqrt{4/5}$.
Finally, $v=(3/5,-7/25)$ satisfies

$$
\|Pv\|^2=\|Pc_*\|^2=\frac9{25},\qquad
\|y-\Lambda v\|^2=\frac{49}{125}
<\frac{50}{125}=\|y-\Lambda c_*\|^2.
$$

For every $\tau>0$ the objective at $v$ is smaller by $\tau/125$.
More generally the gap is $b/125$ for
$a\|Pf\|^2+b\|y-\Lambda f\|^2$ with $b>0$.

## Falsifier

The single nonempty bounded real feasible set and its center falsify
the universal assertion. Equal positive bounds, an orthogonal
projector, and an invertible measurement map are retained.
The row-isometry condition fails. Strict domination excludes every
$\tau\in(0,1)$; a failure for only one parameter would not suffice.
The comparator $v$ improves the objective without changing the
model penalty, so no positive residual weight can recover the center.

## Evidence

The module's public definitions are `feasible`, `IsChebyshevCenter`,
`IsRegularizer` and `claim`; its only public theorem is
`result : ¬ claim`. Private `projection`, `measurement`, `datum`
and `center` encode the instance. The private lemmas `norm_square`
and `feasible_coordinates` give the coordinate reduction; `contacts`
and `bounded` establish admissibility. The lemma `containment`
proves the polynomial certificate bound, and `center_certificate`
uses the weighted contact identity to compare every enclosing bound.
The lemma `not_regularizer` uses the strict comparator for every
$\tau>0$. The proof uses exact rational arithmetic and Mathlib.
Its accepted axiom closure is
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$;
there is no `sorry` or additional axiom.

The radius is identified by containment together with attained
contact distances. The weighted identity also gives uniqueness;
neither radius nor uniqueness is a separate public Lean theorem.
The path formula and reflection observation in Triage are not Lean
theorems in this module.

## Triage

### What the settlement shows

1. **Proved (Lean) — real counterexample.** The instance above has
   center $c_*=(3/5,-1/5)$ and radius $\sqrt{4/5}$, with strict
   domination by $v=(3/5,-7/25)$ in the squared residual and equality
   in the squared model norm. No parameter $\tau\in(0,1)$ recovers it.

2. **Proved (elementary consequence; not a separate Lean theorem) —
   mechanism.** A minimizer of a positively weighted sum of two
   penalties is Pareto-optimal for that pair: any point with both
   penalties no larger and one strictly smaller would lower the sum.
   A real Chebyshev center can instead be Pareto-dominated in
   $(\|Pf\|^2,\|y-\Lambda f\|^2)$, as this instance shows.
   **Proved in the cited literature (not in this Lean module) —
   complex distinction.** The source's affirmative complex result
   relies on exactness of the complex S-procedure; the real
   counterexample does not contradict that result or the affirmative
   real result with both specific conditions.

3. **Computed (exact algebra; not in Lean) — regularization path.**
   For $0<\tau<1$ the normal equations give the unique minimizer

   $$
   f_\tau=\left(\frac{2\tau}{5-4\tau},
   -\frac{2(1-\tau)}{5-4\tau}\right).
   $$

   Its first coordinate equals $3/5$ only at $\tau=15/22$, where
   its second coordinate is $-7/25$, rather than $-1/5$.

4. **Proved (paper argument; not in Lean) — projector reflection.**
   Let $V=\ker P$ and $S=V+\operatorname{ran}(\Lambda^*)$, with
   $P$ an orthogonal projector and $\Lambda:H\to\mathbb R^m$
   bounded linear. The subspace $S$ is closed since $V$ is closed
   and $\operatorname{ran}(\Lambda^*)$ is finite-dimensional.
   Write $f=s+w$ with $s\in S$, $w\in S^\perp$. Then $Pw=w$,
   $\Lambda w=0$ and $\langle Ps,w\rangle=0$. Reflection
   $s+w\mapsto s-w$ therefore preserves both feasibility norms.
   For a nonempty bounded feasible set, its unique Hilbert-space
   Chebyshev center is fixed by this reflection and lies in $S$.
   Hence Question 1, asking for membership in
   $V+\operatorname{ran}(\Lambda^*)$, can only fail for non-projector
   $P$ in this setting. This observation is separate from the
   regularization assertion refuted by `result`.

5. **Open — surviving hypotheses and neighboring questions.** Is
   the center always a regularizer when $\Lambda\Lambda^*=\mathrm{Id}_m$
   but $P$ is not a projector? Is it always a regularizer when $P$
   is a projector and $\Lambda\Lambda^*=\alpha\mathrm{Id}_m$ for
   $\alpha>0$, allowing orthonormal rows up to scaling? The example
   does not settle either restriction. Question 3, with
   $Q\ne\mathrm{Id}_H$, and Question 4, concerning near-optimality of
   the relaxation regularizer, also remain open here. Failure to
   recover the exact center alone gives no quantitative bound on
   that regularizer's near-optimality.

## ASSUMED-UNVERIFIED

Classical work on Chebyshev centers of intersections of two
ellipsoids, including Beck–Eldar (2007) and follow-ups, has not been
checked for an earlier real instance whose center lies on no
regularization path. Exhaustive priority is not established.
The reflection argument, explicit path formula and general
Pareto-optimality observation have no Lean theorem in this module.
