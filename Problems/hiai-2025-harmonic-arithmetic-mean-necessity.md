---
slug: hiai-2025-harmonic-arithmetic-mean-necessity
bibkey: hiai2025quasiarithmetic
doi: null
url: https://arxiv.org/abs/2508.20309
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.result
---

# Necessity in Hiai's harmonic arithmetic comparison

## Problem

Fumio Hiai, *Various inequalities between quasi-arithmetic mean and
quasi-geometric type means for matrices*, arXiv:2508.20309v2
(2025-09-25), Section 5, item (4), asks for the parameter range in the Loewner comparison
$\mathcal H_{\alpha,p}\le\mathcal A_{\alpha,q}$.
The source definitions in Section 2.1 allow $0\le\alpha\le1$,
$p,q>0$, and positive semidefinite matrices in every finite dimension:

$$
\mathcal A_{\alpha,q}(A,B)=((1-\alpha)A^q+\alpha B^q)^{1/q},\qquad
\mathcal H_{\alpha,p}(A,B)=(A^p!_\alpha B^p)^{1/p}.
$$

For positive definite $X,Y$, the weighted harmonic mean is
$X!_\alpha Y=((1-\alpha)X^{-1}+\alpha Y^{-1})^{-1}$.
For positive semidefinite $X,Y$, it is defined by

$$
X!_\alpha Y=\lim_{\varepsilon\downarrow0}
 (X+\varepsilon I)!_\alpha(Y+\varepsilon I).
$$

The source convention is $A^0=s(A)$, the support projection.
For $0<\alpha<1$ and positive definite complex matrices, write

$$
M_t(A,B)=((1-\alpha)A^t+\alpha B^t)^{1/t},\qquad t\ne0,
$$

$$
\mathcal A_{\alpha,q}=M_q,\qquad
\mathcal H_{\alpha,p}=(A^p!_\alpha B^p)^{1/p},\qquad
X!_\alpha Y=((1-\alpha)X^{-1}+\alpha Y^{-1})^{-1}.
$$

The Lean conclusion is restricted to $0<\alpha<1$: if the comparison
holds for every pair of positive definite complex $2\times2$ matrices,
then $p\ge1$ and $q\ge1$. The harmonic expression agrees with $M_{-p}$
on this domain. The endpoints are degenerate: for $\alpha=0$ both means
equal $A$, and for $\alpha=1$ both equal $B$, for every $p,q>0$.
Thus the necessity question only has content for $\alpha\in(0,1)$.

## Motivation

In dimension one the scalar comparison holds for every $p,q>0$,
including nonnegative inputs under the source's limiting definition.
Noncommuting two dimensional matrices distinguish the sharp exponent
thresholds. The source supplies sufficiency for $p,q\ge1$; necessity
and its direct sum consequences therefore complete the parameter
characterization for $0<\alpha<1$ on positive semidefinite matrices in
each dimension at least two. Only the two dimensional positive definite
necessity is a Lean conclusion here.

## Gap

Commuting pairs cannot detect either threshold. A noncommuting positive
definite family must expose a negative principal determinant when
$p<1$, for every positive comparison exponent $q$. An inverse order
argument must transfer the same obstruction to $q<1$.

## Route

Let $0<x<1$, let $A=\operatorname{diag}(1,x)$, and rotate
$\operatorname{diag}(1,x^2)$ to obtain $B$. Write $z=\sin^2\theta$.
For an exponent $t\ne0$, put

$$
d_t=(1-\alpha)x^t+\alpha x^{2t},\quad m_t=d_t^{1/t},\quad
k_t=\frac{\alpha(1+x^t)}{1+\alpha x^t},\quad
h_t=\frac{\alpha(1-\alpha)(1-x^{2t})}{t(1+\alpha x^t)}.
$$

The weighted power sum has diagonal entries $1-g_tz,d_t+g_tz$ and
off-diagonal entry $g_t\sqrt{z(1-z)}$, where
$g_t=\alpha(1-x^{2t})$. Its two eigenvalues and two-point functional
calculus give a differentiable diagonal formula in $z$ near zero.
For $r=-p$, $s=q$, the determinant divided by $z$ tends to

$$
C_x=(m_s-m_r)(h_r-h_s)
 -(k_s-k_r)^2(1-m_s)(1-m_r).
$$

For $-1<r<0<s$, factoring powers of $x$ gives
$m_s=x((1-\alpha)+\alpha x^s)^{1/s}$ and
$m_r=x^2(\alpha+(1-\alpha)x^{-r})^{1/r}$.
The scaled quantity $x^{-r}h_r$ has a finite limit. Thus the diagonal
contribution in the displayed formula vanishes using $x^{1+r}\to0$,
whereas $(k_s-k_r)^2(1-m_s)(1-m_r)\to(1-\alpha)^2$.
Consequently $C_x\to-(1-\alpha)^2$.

The assumed matrix order would imply a nonnegative determinant for
all small positive $z$, hence $C_x\ge0$ for every $x\in(0,1)$.
Passing to $x\downarrow0$ contradicts the strictly negative limit.
This proves $p\ge1$. Inverting the inputs, identifying
$M_t(A^{-1},B^{-1})=M_{-t}(A,B)^{-1}$, and reversing the inverse order
reduces $q\ge1$ to the same argument with the parameters exchanged.

## Falsifier

A conclusion restricted to real matrices, commuting pairs, a single
weight, a fixed positive gap below one, or a restricted set of positive
comparison exponents would not answer the stated target. Neither the
spectral expansion nor the scalar limit may be supplied as a hypothesis.
The matrix order is the Loewner order, not entrywise order.

## Evidence

The source identity and parameter conventions are recorded in
`Library/Divergence/hiai2025quasiarithmetic.md`. The exact target is
`D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic.result`, quantified over
all positive definite complex two by two matrices. Its harmonic mean
uses the inverse of the weighted sum of inverses after taking the
positive input powers. The proof reduces that definition to the negative
parameter power mean. Its auxiliary proofs establish the actual
spectral formula, determinant limit, scalar limit and inversion identities.

## Triage

**Proved in Lean:** The target necessity for positive definite complex
two by two matrices, for each weight strictly between zero and one
and all positive parameters. The obstruction has two vanishing spectral
scales $x,x^2$ and a small rotation. The adverse off-diagonal square
and the diagonal correction combine into the negative term in $C_x$,
whose magnitude approaches $(1-\alpha)^2$ while the other term
vanishes at a rate controlled by $x^{1-p}$ when $p<1$.

**Proved in the source, not formalized:** For $p,q\ge1$, the harmonic arithmetic
comparison holds for all positive semidefinite matrices in every finite
dimension, with the harmonic mean defined by the source's $\varepsilon$
limit. Section 5 (4) obtains this from Theorem 4.16 via
$\mathcal H_{\alpha,p}\le\mathcal G_{\alpha,1}\le\mathcal A_{\alpha,q}$.
The sufficiency is not a second Lean theorem here.

**Derived on paper, not formalized:** For every integer $n\ge2$, the two dimensional
counterexample extends by $A\oplus I_{n-2}$ and $B\oplus I_{n-2}$
(with no added block when $n=2$). Both means respect these direct sums,
and their difference is the original difference direct summed with zero.
Its negative two by two principal determinant still obstructs the Loewner
comparison. This extension is not formalized.

**Derived on paper, not formalized:** The positive definite counterexamples already belong
to the source's positive semidefinite domain. Hence, for each
$0<\alpha<1$ and each dimension $n\ge2$, comparison for all positive
semidefinite pairs forces $p,q\ge1$. Together with the source
sufficiency this gives the complete characterization on that domain.

**Derived on paper, not formalized:** At $\alpha=0$ or $\alpha=1$, both means equal the
same input, so the comparison holds for all $p,q>0$ in every dimension.
These endpoint identities are not formalized here.

**Derived on paper, not formalized:** For $n=1$ and positive inputs, monotonicity of scalar
power means gives $\mathcal H_{\alpha,p}=M_{-p}\le M_q
=\mathcal A_{\alpha,q}$ for all $p,q>0$. Nonnegative inputs follow
by the source's limiting definition and continuity of positive powers.
This scalar statement is not formalized here.

**Open:** Formalization of the source's singular-input limiting
definition, its sufficient comparison, the endpoint and scalar identities,
and the higher dimensional direct sum argument is outside this module.
Their mathematical status is given separately above; this is a
formalization boundary, not an unresolved source conjecture.

## ASSUMED-UNVERIFIED

Later-literature completeness and worldwide priority are unverified;
neither is claimed here. The source statements above refer to the checked
arXiv v2 (2025-09-25), Sections 2.1 and 5 (4).
The direct sum and singular-domain consequences above are paper deductions,
not additional compiled conclusions.
