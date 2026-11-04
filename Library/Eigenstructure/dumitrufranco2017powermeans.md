---
bibkey: dumitrufranco2017powermeans
authors: Raluca Dumitru; Jose Franco
year: 2017
title: On the monotonicity of weighted power means of matrices
doi: null
url: https://arxiv.org/abs/1701.07023v1
claim: The withdrawn first version conjectures decreasing distance to A for weighted power means with every unitarily invariant norm and every exponent 0 < p <= 2; an exact positive definite pair refutes its p=2 Euclidean operator-norm specialization.
strata_touched:
  - D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation
license: citation-only
triage: anchor
---

# Weighted power means and a version-specific counterexample

## Verified locator

Raluca Dumitru and Jose Franco, *On the monotonicity of weighted power means
of matrices*, arXiv:1701.07023v1, submitted 24 January 2017:
https://arxiv.org/abs/1701.07023v1.
The official source is https://arxiv.org/src/1701.07023v1.
The final conjecture is numbered Conjecture 9 in the first-version PDF.

## Source assertion and version boundary

Conjecture 9 reads:

> Let $A,B\geq 0$ and let $\lVert\cdot\rVert$ be a unitarily invariant norm.
> Let $0<p\leq 2$. Then,
> $t\mapsto\lVert A-\mu_p(A,B,t)\rVert$
> is monotonically decreasing for $t\in[0,1]$.

Here $\mu_p(A,B,t)=(tA^p+(1-t)B^p)^{1/p}$, with positive spectral powers.
Version 2, dated 30 January 2017, withdraws the preprint because Proposition 4
is false and major revisions are necessary. Withdrawal alone does not prove
Conjecture 9 false. The counterexample below is
attributed only to the displayed assertion of version 1.

The published successor is Trung Hoa Dinh, Raluca Dumitru, and Jose A. Franco,
*On the monotonicity of weighted power means for matrices*, Linear Algebra
and its Applications **527** (2017), 128–140,
https://doi.org/10.1016/j.laa.2017.04.003. Its author manuscript is
https://trunghoamath.wordpress.com/wp-content/uploads/2017/03/main-v-31.pdf.
It proves the $p=2$ Frobenius branch and the $p=1/2$ branch for every unitarily
invariant norm; those conclusions are compatible with this counterexample.
This comparison uses the public three-author author manuscript. Publisher full
version-of-record text was not obtained, so no complete comparison with it is
claimed.

No exact prior refutation was found in the bounded later primary literature
inspected through 2026-11-01. The directly relevant *The matrix power means and
interpolations* (2018), https://doi.org/10.15352/aot.1801-1288, remained
text-inaccessible; other candidates were metadata-only. Current-open status,
novelty, priority, and uniqueness remain unverified. No comprehensive
later-resolution claim is made, and this component earns zero
verified-original or unique credit.

## Exact formal scope

The closed Lean proposition `claim` quantifies over all natural dimensions,
complex positive semidefinite matrices $A,B$, and real $0\leq s\leq t\leq1$.
It asserts

$$
\lVert A-\mu_2(A,B,t)\rVert_{2\to2}
\leq\lVert A-\mu_2(A,B,s)\rVert_{2\to2}.
$$

The norm is the operator norm induced by the Euclidean norm on complex
vectors (`Matrix.Norms.L2Operator`). The power mean uses the positive spectral
square root through continuous functional calculus. The theorem `result`
has the literal closed type `Not claim`. This specialization follows from
the full version-1 assertion, so its negation refutes that universal assertion.
The formal proposition does not quantify over all norms, and the result
does not refute every norm separately.

## Exact matrices and the strict inequality

Take $A=Y$, $B=X$, $s=0$, and $t=1/100$, where

$$
X=\begin{pmatrix}1/10&0\\0&4\end{pmatrix},\qquad
Y=\begin{pmatrix}19/50&-24/25\\-24/25&93/25\end{pmatrix}.
$$

Both matrices are positive definite. Their determinants are $2/5$ and
$123/250$, respectively. The difference $D=X-Y$ satisfies $D^*D=I$, giving
the endpoint distance $1$. At the positive parameter put

$$
S=\frac{99X^2+Y^2}{100}
=\begin{pmatrix}257/12500&-123/3125\\-123/3125&39969/2500\end{pmatrix},
\quad d=\frac{51118101}{156250000},\quad T=\frac{100051}{6250}.
$$

For $r=\sqrt d$ and $w=\sqrt{T+2r}$, the matrix $Q=(S+rI)/w$ is positive
semidefinite and satisfies $Q^2=S$, hence is the positive spectral root.
The Euclidean unit vector $v=(3/5,4/5)$ has

$$
a=v^*Sv=\frac{127521}{12500},\qquad
c=v^*Xv=\frac{649}{250},\qquad v^*Yv=\frac{399}{250}=c-1.
$$

The exact certificates

$$
d-(57/100)^2=\frac{88119}{39062500}>0,
$$

$$
(a+r)^2-c^2w^2
=-\frac{339943099}{97656250}+\frac{108202}{15625}r
>\frac{22763263}{48828125}>0
$$

give $(a+r)/w>c$, and therefore $v^*(Q-Y)v>1$.
Cauchy–Schwarz and the Euclidean operator-norm bound yield
$\lVert Y-Q\rVert_{2\to2}>1$. No floating approximation is a premise.
