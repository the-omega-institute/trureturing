---
slug: dedania-patel-2024-spatial-numerical-range-convexity
bibkey: dedaniapatel2024spatial
doi: null
url: https://arxiv.org/abs/2306.16172v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.result
---

# Convexity of the spatial numerical range in non-unital normed algebras

## Problem

H. V. Dedania and A. B. Patel, *Spatial numerical range in non-unital, normed algebras and their unitizations*, arXiv:2306.16172v1, *Sarajevo Journal of Mathematics* 20(2) (2024), §1, p. 2, write:

> Let $S(A)=\{x\in A:\|x\|=1\}$ be the unit sphere in $A$. Let $A^*$ be the Banach space dual of $A$. Let $D_A(x)=\{\varphi\in A^*:\|\varphi\|=1=\varphi(x)\}$ for each $x\in S(A)$. Further, let $V_A(a;x)=\{\varphi(ax):\varphi\in D_A(x)\}$ for $a\in A$ and $x\in S(A)$. Then $V_A(a)=\cup\{V_A(a;x):x\in S(A)\}$ is the spatial numerical range (SNR) … It is still open problem wether $V_A(a)$ is always convex? This problem is discussed in [5].

The question is whether $V_A(a)$ is convex as a subset of the real vector space underlying $\mathbb C$, for every element of every complex non-unital normed algebra.

## Motivation

Convexity would allow norming functionals at different unit vectors to contribute a common convex range. Classical convexity of the algebra numerical range in unital normed algebras, as treated by Bonsall–Duncan, does not directly settle the spatial definition above without a unit. An explicit counterexample separates the universal assertion from the specific convexity results in the companion paper.

## Gap

The authors state that the question is open. The abstract of their companion paper, *On the convexity of the spatial numerical range in non-unital normed algebras*, likewise says that they believe it is still open and that the answer seems to be negative, while establishing convexity in several specific non-unital Banach algebras. Their account presents no known non-convex example. This is the gap stated by the authors; whether older books or the general Banach-space-operator literature already contain a transferable counterexample remains ASSUMED-UNVERIFIED.

## Route

On $X=\mathbb C^2$ with its supremum norm, define

$$
P=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix}.
$$

Give $A=\mathbb C\oplus X$ the product and norm

$$
(\alpha,x)(\beta,y)=(\alpha\beta,\alpha Py+\beta x),\qquad
\|(\alpha,x)\|=\max(3|\alpha|,\|x\|_\infty).
$$

The Lean carrier `Alg` is `ℂ × (Fin 2 → ℂ)`, with rescaled scalar coordinate $u_0=3\alpha$ and the ordinary product supremum norm. Its multiplication `mulDef` is

$$
(u_0,x)(v_0,y)=\left(\frac{u_0v_0}{3},\frac{u_0}{3}Py+\frac{v_0}{3}x\right).
$$

The lemma `P_sq` proves idempotence. The algebra instances use the associativity, distributivity, scalar compatibility and submultiplicative norm lemmas. The norm proof uses the sufficient bound $\|Py\|_\infty\le2\|y\|_\infty$; it does not assert the exact operator norm of $P$.

Let $e=(1,0)$, represented by `e = (3, 0)` in Lean. The lemma `e_mul` gives $e(u_0,x)=(u_0,Px)$. The unit vectors

$$
x_1=(0,(1,i)),\qquad x_2=(0,(i,1))
$$

and the coordinate functionals `phi0` and `phi1` are norming pairs. The lemma `z_points` proves

$$
z_1=\frac15+\frac25i\in V_A(e),\qquad
z_2=\frac45+\frac25i\in V_A(e).
$$

For a hypothetical norming pair $(u,\varphi)$ producing their midpoint, write

$$
\varphi(u_0,x)=c_0u_0+c_1x_0+c_2x_1.
$$

Testing $\varphi$ on the coefficient phases gives $|c_0|+|c_1|+|c_2|\le1$ (`coeff_sum_le_one`). The norming equation and the coordinate bounds make the three diagonal products $c_0u_0,c_1x_0,c_2x_1$ real (`support_im_zero`). Consequently

$$
\operatorname{Im}\varphi(eu)
=\frac25\bigl(\operatorname{Im}(c_1x_1)+\operatorname{Im}(c_2x_0)\bigr)
\le\frac25(|c_1|+|c_2|)\le\frac25.
$$

At height $2/5$, equality forces $c_0=0$, $|c_1|+|c_2|=1$, diagonal products $c_1x_0=|c_1|$, $c_2x_1=|c_2|$, and cross products $c_1x_1=i|c_1|$, $c_2x_0=i|c_2|$. The identity

$$
(c_1x_0)(c_2x_1)=(c_1x_1)(c_2x_0)
$$

then gives $|c_1||c_2|=-|c_1||c_2|$. For the proposed midpoint, its real part additionally forces $|c_1|=|c_2|=1/2$, a contradiction. This is the argument in `midpoint_not_mem`; `nonconvex` applies the convexity midpoint condition, and `result` refutes `claim`.

## Falsifier

The displayed normed algebra and element $e$ falsify the universal convexity assertion. Both $z_1$ and $z_2$ belong to $V_A(e)$, whereas

$$
\frac{z_1+z_2}{2}=\frac12+\frac25i\notin V_A(e).
$$

The structure uses a non-unital normed ring with complex normed-space structure and both scalar compatibility instances. No completeness or commutativity premise is used in `claim`.

## Evidence

The public declarations in `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.lean` are `spatialNumericalRange`, `claim`, and `result`; the construction and supporting lemmas are private.

The definition `spatialNumericalRange` quantifies over a unit vector and a continuous complex-linear functional of norm one taking value one on that vector. The definition `claim` quantifies over `A : Type` with instances `NonUnitalNormedRing A`, `NormedSpace ℂ A`, `IsScalarTower ℂ A A`, and `SMulCommClass ℂ A A`, and over every `a : A`; its conclusion is `Convex ℝ (spatialNumericalRange a)`.

The algebra instances establish the required normed-algebra structure. The private lemmas `z_points`, `coeff_sum_le_one`, `support_im_zero`, `midpoint_not_mem`, and `nonconvex` establish the membership and exclusion argument. The theorem `D5.S3.Analytic.NumericalRange.SpatialNumericalRangeNonconvex.result` has type `¬ claim`.

The accepted axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. `NonUnitalNormedRing` does not itself assert that no identity exists; absence of a left identity is justified separately below. The module has no separate theorem classifying the entire spatial range or proving an abstract transfer principle.

## Triage

### What the settlement shows

1. **Proved (Lean) — the normed-algebra instance and refutation.** The explicit algebra has the required non-unital normed-algebra structure, $z_1,z_2\in V_A(e)$, and their midpoint is absent. Hence `claim` fails. The conclusion concerns spatial numerical ranges defined by norming pairs, not the classical Hilbert-space numerical range.

2. **Computed (exact hand calculation) — one-sided identity and projection norm.** The product gives $(\alpha,x)e=(\alpha,x)$, so $e$ is a right identity. The nonzero vector $k=(2,-1)$ satisfies $Pk=0$; every $b\in A$ therefore satisfies $b(0,k)=0$, which excludes a left identity. Left multiplication by $e$ is $\operatorname{diag}(1,P)$, as also expressed by `e_mul`, and $P^2=P$ is proved by `P_sq`. The absolute row sums of $P$ are $3/5$ and $6/5$, and $P(1,1)=(3/5,6/5)$, giving $\|P\|_\infty=6/5$. The right-identity, no-left-identity and exact-norm assertions have no separate Lean theorem.

3. **Open — explanatory mechanism beyond the instance.** In the classical normalized unital setting, evaluating an element on the convex set of states makes its algebra numerical range convex. The candidate explanation for failure here is that the spatial range of $L_e$ is a union over norming vectors of convex pieces $\{\varphi(L_eu):\varphi\in D_A(u)\}$ that need not glue into a convex set. This is mathematical reasoning about the example; the comparison with states and a general criterion for gluing are not proved in the Lean module.

4. **Open — generalization and transfer.** For a complex Banach space $X$ and a bounded linear idempotent $P$, consider

   $$
   A_c=\mathbb C\oplus X,\qquad
   (\alpha,x)(\beta,y)=(\alpha\beta,\alpha Py+\beta x),\qquad
   \|(\alpha,x)\|=\max(c|\alpha|,\|x\|).
   $$

   The hand derivation for $c\ge\|P\|+1$ gives associativity from $P^2=P$ and, with $M=\|(\alpha,x)\|$, $N=\|(\beta,y)\|$,

   $$
   c|\alpha\beta|\le MN/c,\qquad
   \|\alpha Py+\beta x\|\le (\|P\|+1)MN/c\le MN.
   $$

   A norming pair $(x,f)$ for $X$ extends to $((0,x),F)$ with $F(\alpha,y)=f(y)$ and $\|F\|=1$, yielding $F((1,0)(0,x))=f(Px)$. Thus the proposed construction contains the spatial numerical range of $P$ in $V_{A_c}((1,0))$. These general statements are not formalized. The stronger proposed conclusion that every nonconvex spatial range of an idempotent transfers to a nonconvex algebra spatial range remains open: inclusion alone is insufficient, because other norming pairs can add points. A transfer theorem must also preserve an excluded point, as the explicit equality-case argument does here.

5. **Open — bounded approximate identities.** Is $V_A(a)$ convex for every element of a non-unital Banach algebra with a bounded approximate identity? The example and its Lean statement do not settle this question.

6. **Open — commutative algebras.** Does convexity hold for every element of every commutative non-unital normed algebra? The universal refutation does not settle this restricted assertion.

7. **Open — unitization comparison.** Does the closed convex hull of $V_A(a)$ always equal the numerical range of $a$ in the unitization? This is only a question; no equality is asserted.

## ASSUMED-UNVERIFIED

Whether Bonsall–Duncan, *Numerical Ranges I/II*, contain an element of a non-unital normed algebra with nonconvex spatial numerical range is unverified: the books have not been read for this question. The source authors cite them and still call the problem open. Their description does not replace a check of the books' actual results and hypotheses.

The general Banach-space-operator literature on nonconvex spatial numerical ranges has not been read. Its relation to the idempotent construction and any earlier non-unital-algebra counterexample remains unverified. The exact hand calculations and proposed generalization in Triage are distinguished from the Lean results; no literature priority or general transfer theorem is claimed.
