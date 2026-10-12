---
slug: marinescu-niculescu-2024-variable-exponent-hornich-hlawka
bibkey: marinescuniculescu2024survey
doi: null
url: https://arxiv.org/abs/2407.03278v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/VariableExponentHornichHlawka.result
---

# Variable-exponent Lebesgue spaces and the Hornich–Hlawka inequality

## Problem

D.-Ş. Marinescu and C. P. Niculescu, *A survey of the Hornich-Hlawka inequality*, arXiv:2407.03278v1, §3, the paragraph introducing Problem 3 and Problem 3 itself, state verbatim:

> A natural generalization of Lp spaces is provided by the class of Lp(·) spaces with variable exponent. They differ from the classical Lp spaces in that the exponent p is not constant but a function from the measure space under attention to [1, ∞]. See the monograph of L. Diening, P. Harjulehto, P. Hästö and M. Ruzicka [6] for a thorough presentation. Problem 3. Is every Lp(·)(0, 1) space with a variable exponent p(·) : (0, 1) → [1, 2] a Hornich-Hlawka space?

A Hornich–Hlawka space satisfies

$$
\|f+g\|+\|g+h\|+\|h+f\|
\le \|f\|+\|g\|+\|h\|+\|f+g+h\|
$$

for every triple. The norm considered here is the Luxemburg norm. The journal version is *A New Look at the Hornich-Hlawka Inequality*, Results Math. (2025), doi:10.1007/s00025-025-02464-9; the quotation and locator refer to the arXiv version.

## Motivation

For constant $p\in[1,2]$, the survey gives a positive answer: $L^p(0,1)$ embeds isometrically in $L^1$, which satisfies the Hornich–Hlawka inequality. Variable exponents permit different power laws on different parts of the measure space. The question asks whether the same range restriction on those powers suffices for the inequality.

## Gap

The survey poses Problem 3 with no answer. Its positive argument for constant exponents does not establish the assertion for variable exponents. The source evidence is arXiv:2407.03278v1; the journal full text and an exhaustive literature or priority claim remain ASSUMED-UNVERIFIED.

## Route

Use Lebesgue measure on $(0,1)$ and put

$$
p(t)=\begin{cases}1,&0<t<1/2,\\2,&1/2\le t<1.\end{cases}
$$

The Lean definition extends $p$ to all of $\mathbb R$ by the same test $t<1/2$. For $u=(u_1,u_2,u_3)$, define the step function

$$
J(u)(t)=\begin{cases}
4u_1,&0<t<1/4,\\
4u_2,&1/4\le t<1/2,\\
\sqrt2\,u_3,&1/2\le t<1,\\
0,&\text{otherwise}.
\end{cases}
$$

For $\lambda>0$, its modular is

$$
\rho_p(J(u)/\lambda)=\int_0^1|J(u)(t)/\lambda|^{p(t)}\,dt
=\frac{|u_1|+|u_2|}{\lambda}+\frac{u_3^2}{\lambda^2}.
$$

Writing $a=|u_1|+|u_2|$, the positive scales at which this is at most one are exactly those with

$$
\lambda\ge N(u):=\frac{a+\sqrt{a^2+4u_3^2}}2.
$$

Thus the Luxemburg norm $\inf\{\lambda>0:\rho_p(J(u)/\lambda)\le1\}$ equals $N(u)$. The Lean lemma `luxNorm_J` proves this equality under $N(u)>0$, which holds for every vector used below. The zero vector has norm zero by the defining infimum; that case is mathematical reasoning rather than a separate theorem in the module.

## Falsifier

Take

$$
x=J(0,1,1/2),\qquad y=J(0,-1,1/2),\qquad z=J(-1,0,-1/2).
$$

The four norms $\|x\|,\|y\|,\|z\|,\|x+y+z\|$ all equal $(1+\sqrt2)/2$. Additivity of $J$ gives

$$
x+y=J(0,0,1),\quad y+z=J(-1,-1,0),\quad z+x=J(-1,1,0),
$$

whose norms are $1,2,2$, respectively. The proposed inequality would require

$$
5\le2+2\sqrt2,
$$

but $\sqrt2<3/2$, so $2+2\sqrt2<5$. All three functions belong to $L^{p(\cdot)}(0,1)$ and $p$ is measurable with values in $[1,2]$.

## Evidence

The public declarations in `D5/S3/Geometry/VariableExponentHornichHlawka.lean` are `modular`, `luxNorm`, `InLp`, `claim`, and `result`; the exponent, step functions, finite-dimensional formula and supporting lemmas are private.

`modular p f lam` is the Lebesgue lower integral over `Set.Ioo (0 : ℝ) 1` of `ENNReal.ofReal (|f t / lam| ^ p t)`. `luxNorm p f` is the real `sInf` of the positive scales with modular at most one. `InLp p f` requires global measurability of the representative and such a scale. For finite exponents bounded between one and two, this is the scaled-modular membership condition. The counterexample representatives are measurable on all of $\mathbb R$, so they also define measurable functions on $(0,1)$ and equivalence classes modulo equality almost everywhere.

`claim` quantifies over measurable real functions $p$ with $1\le p(t)\le2$ on $(0,1)$, and over triples of real functions satisfying `InLp p`. It requires the Hornich–Hlawka inequality for their Luxemburg norms. These definitions use representatives rather than a separately constructed normed quotient space; the exhibited strict inequality depends only on their almost-everywhere classes.

`exponent_measurable` and `exponent_range` establish the exponent hypotheses. `J_measurable` and `J_InLp` establish membership for the vectors with positive `N`. `modular_J` evaluates the three interval integrals; `scale_iff` solves the scale inequality; `luxNorm_J` identifies its infimum. `J_add`, `N_special`, `base_positive`, and `pair_norms` give the seven norms used by `result`. The theorem `D5.S3.Geometry.VariableExponentHornichHlawka.result` has type `¬ claim`; its final square-root comparison proves the strict violation.

The module's axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom.

## Triage

### What the settlement shows

1. **Proved (Lean) — the exponent hypotheses.** The two-valued exponent is measurable and lies in $[1,2]$, including at the midpoint.

2. **Proved (Lean) — membership.** Each of the three step functions is measurable and has modular at most one at a positive scale, hence satisfies `InLp`.

3. **Proved (Lean) — the Luxemburg norms.** The modular and positive-scale formula yield the four norms $(1+\sqrt2)/2$ and the three pair-sum norms $1,2,2$.

4. **Proved (Lean) — the strict violation.** The inequality $2+2\sqrt2<5$ contradicts `claim`, giving a negative answer to Problem 3.

5. **Computed (exact mathematical reasoning) — the mechanism.** The linear map $J$ is injective modulo equality almost everywhere because its three constant values occur on disjoint sets of positive measure. Its norm formula identifies $J(\mathbb R^3)$ isometrically with $(\mathbb R^3,N)$, the Luxemburg norm associated with the modular $|u_1|+|u_2|+u_3^2$. The square-root expression mixes an $\ell^1$ part and an $\ell^2$ part nonlinearly. Each part separately embeds isometrically in $L^1$, but this mixed norm fails Hornich–Hlawka. The module proves the modular, additivity and norm identities for positive `N`; it does not separately construct the linear isometry or prove the norm axioms.

6. **Open — variable-exponent Sobolev spaces.** Problem 4 of the same survey, concerning $W^{k,p(\cdot)}$, is not settled for positive derivative order by this module. The observation $W^{0,p(\cdot)}=L^{p(\cdot)}$ transfers the counterexample only to order zero.

7. **Open — continuous or nearly constant exponents.** Whether the inequality holds when $p$ is continuous, or sufficiently close to a constant, is not settled by this discontinuous two-valued example. Perturbing its two values towards the interior of $[1,2]$ does not make the exponent continuous or close to constant.

8. **Open — classification.** Which variable exponents yield Hornich–Hlawka spaces remains unsettled; the range restriction $1\le p\le2$ alone is insufficient.

## ASSUMED-UNVERIFIED

The journal version's full text is unverified. The quoted Problem 3 and its status in the survey refer to arXiv:2407.03278v1; an exhaustive literature or priority claim is unverified.

Preservation of the strict violation under sufficiently small perturbations of the two exponent values into $(1,2)$ is mathematical reasoning, not formalized. For each of the seven nonzero step functions, the modular is a finite sum of continuous functions of the two powers and the positive scale. It decreases strictly from infinity to zero with the scale, so its unique unit level, the Luxemburg norm, varies continuously with the powers. The positive gap $5-(2+2\sqrt2)$ therefore persists in a sufficiently small neighbourhood of $(1,2)$. No quantitative perturbation radius is certified by the module.
