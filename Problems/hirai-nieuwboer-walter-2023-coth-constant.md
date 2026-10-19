---
slug: hirai-nieuwboer-walter-2023-coth-constant
bibkey: hirai2023interiorpoint
doi: 10.48550/arXiv.2303.04771
url: https://arxiv.org/abs/2303.04771
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.result
---

# Optimal hyperbolic cotangent constant

## Problem

Hirai–Nieuwboer–Walter, arXiv:2303.04771v2, §5, Lemma 5.13 and Remark 5.14:

> "Lemma 5.13. The constant C = √2 is such that for all a, b ∈ ℝ, one has |coth((a − b)/2) (a coth(a/2) − b coth(b/2))| ≤ C √(ab(a − b) coth(a/2) coth(b/2) coth((a − b)/2))."

> "Remark 5.14. We conjecture, based on numerical evidence, that the optimal constant in the above inequality is C = 1/√2."

The source proves the coefficient $\sqrt2$ and conjectures the optimal
coefficient $1/\sqrt2$. The repository resolves that conjecture: the optimal
constant in

$$
\left|\coth\frac{a-b}{2}
\left(a\coth\frac a2-b\coth\frac b2\right)\right|
\le C\sqrt{ab(a-b)\coth\frac a2\coth\frac b2\coth\frac{a-b}{2}}
$$

is $C=1/\sqrt2$. The quantifiers range over all real $a,b$ with
$a\ne0$, $b\ne0$, and $a\ne b$. Optimality means that for every real
$C<1/\sqrt2$, some such pair violates the estimate strictly.
Here $\coth x=\cosh x/\sinh x$ and square roots are nonnegative real roots.

## Motivation

The scalar inequality controls third derivatives of squared Riemannian
distance on positive definite matrices. Through the paper's Theorem 5.15,
the sharp constant gives the consequence “squared distance on PD(n) is
8-self-concordant.” The geometric consequence is not formalized here.

## Gap

Both the uniform bound and its sharpness require analytic arguments over
unbounded real inputs, including the removable singularity as one input tends
to zero. Finite sampling does not prove either quantified assertion.

## Route

Extend $u(x)=x\coth x$ by $u(0)=1$, and put $\psi(x)=x\tanh x$.
On the nonnegative half-line, $u\ge1$, $u$ is nondecreasing and
$0\le u'\le1$ away from zero; continuity supplies the endpoint. Also
$\psi$ is nondecreasing and $u(x)\psi(x)=x^2$.

For $A=\max(|x|,|y|)$, $B=\min(|x|,|y|)$ and $\delta=A-B$,
the Lipschitz estimate and monotonicity give

$$
(u(x)-u(y))^2\le\delta^2
=\psi(\delta)u(\delta)
\le\psi(\delta)u(A)u(B)
\le\psi(|x-y|)u(A)u(B).
$$

Evenness and $\delta\le|x-y|$ therefore yield

$$
(u(x)-u(y))^2\le(x-y)\tanh(x-y)u(x)u(y).
$$

Substitute $a=2x$, $b=2y$ and $h(s)=2u(s/2)$.
The radicand equals $h(a)h(b)h(a-b)>0$ on the permitted domain, and the
squared ratio of the left side to its square root is at most $1/2$.

For sharpness, let $C<1/\sqrt2$ and choose
$t=2/(1-C\sqrt2)>0$. Since $u(t)\ge t$,

$$
u(t)-1-Ct\sqrt2\ge t(1-C\sqrt2)-1=1>0.
$$

The function

$$
F(y)=u(t-y)(u(t)-u(y))
-C(t-y)\sqrt{2u(t)u(y)u(t-y)}
$$

is continuous at zero. Using $u(0)=1$ and $u(t)>0$ gives
$F(0)=u(t)(u(t)-1-Ct\sqrt2)>0$. Therefore some $y$ with $0<y<t$
still satisfies $F(y)>0$. The distinct nonzero pair $a=2t$, $b=2y$
then strictly violates the estimate with coefficient $C$.

| Needed interface | Reused source | Use |
| --- | --- | --- |
| Cotangent product lower bound | `ThermalCoefficientFloor.one_le_self_mul_coth` | Establish $u(x)\ge1$ for positive inputs |
| Scaled cotangent function and derivative | `ArimotoHyperbolic.f`, `f_hasDerivAt` | Differentiate $u$ away from zero |
| Positive derivative numerator | `ArimotoHyperbolic.sinh_cosh_sub_pos` | Show monotonicity of $u$ |
| Real hyperbolic tangent derivative | `LinearCayleyScaleFlow.real_tanh_hasDerivAt` | Differentiate $\psi(x)=x\tanh x$ |

## Falsifier

A pair of distinct nonzero real inputs violating the estimate at
$C=1/\sqrt2$ refutes the upper bound. A strictly smaller real coefficient
satisfying the estimate at every permitted pair refutes optimality.

## Evidence

The exact formal statement is `claim`, with the settling declaration
`result : claim` in
`D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.lean`.
The first conjunct is the uniform estimate; the second supplies a strict
counterexample for every smaller real coefficient.

## Triage

(i) The uniform estimate at $C=1/\sqrt2$ is **PROVED** by `result : claim`.

(ii) The failure of every $C<1/\sqrt2$ is **PROVED** by the second conjunct
of `result : claim`.

The consequence “squared distance on PD(n) is 8-self-concordant” follows
via the paper's Theorem 5.15; it is not formalized here.

## ASSUMED-UNVERIFIED

Bibliographic priority and the absence of a subsequent proof have not been
independently established. The source attribution uses arXiv:2303.04771v2,
§5, Lemma 5.13 and Remark 5.14; the geometric implication uses Theorem 5.15.
