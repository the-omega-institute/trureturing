---
slug: hiai-2026-problem-3-5-spectral-geometric-renyi
bibkey: hiai2026quasigeometric
doi: null
url: https://arxiv.org/abs/2510.04691v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.result
---

# Hiai's spectral geometric Renyi comparison beyond its sharp boundary

## Problem

Section 2 of the source defines, for positive definite complex matrices,

$$
A\#_\alpha B=A^{1/2}(A^{-1/2}BA^{-1/2})^\alpha A^{1/2},
\qquad \#=\#_{1/2},
$$
$$
F_\alpha(A,B)=(A^{-1}\#B)^\alpha A(A^{-1}\#B)^\alpha,
\qquad SG_{\alpha,p}(A,B)=F_\alpha(A^p,B^p)^{1/p},
$$
$$
R_{\alpha,q}(A,B)=
\left(A^{(1-\alpha)q/2}B^{\alpha q}A^{(1-\alpha)q/2}\right)^{1/q}.
$$

All powers are spectral real powers. Problem 3.5 states, verbatim:

> When α>1, no necessary condition on p,q>0 for SG_{α,p} ≺log R_{α,q} to hold is known.

> This suggests us that SG_{α,p} ≺log R_{α,q} might hold for any p,q>0.

The asserted comparison includes its first inequality
$\lambda_{\max}(SG_{\alpha,p}(A,B))\le
\lambda_{\max}(R_{\alpha,q}(A,B))$ for every positive definite complex
two by two pair. The target is its negation, together with a counterexample
for every $\alpha>1$, $q>0$, and $p>\alpha q$.

## Motivation

Theorem 3.4(1) proves the comparison for $p\le\alpha q$. Determining whether
this boundary is necessary distinguishes a genuine parameter restriction
from a sufficient condition of the source proof. Commuting pairs cannot
expose the distinction at the normalized pair used below: both means are
the identity at the common diagonal point.

## Gap

For each fixed $\alpha>1$ and $p>\alpha q>0$, a positive definite pair
must violate the largest eigenvalue inequality. The inputs must be complex
positive definite matrices, even though the witnesses have real entries.
No spectral expansion or strict coefficient separation may be assumed as
an additional hypothesis. The named target is preregistered in issue #31215.

## Route

Write $k=\alpha q/p$, so $0<k<1$. Choose $u>0$ such that

$$
p\sinh(k(\alpha-1)u)<q\sinh((\alpha-1)u).
$$

Such a choice exists because, for $z\ge1$,
$\sinh z\ge e^z/4$ while $\sinh(kz)<e^{kz}/2$, and $1-k>0$.
For example, take

$$
z=\max\{1,\log(4p/q)/(1-k)\}+1,\qquad u=z/(\alpha-1).
$$

Let

$$
D(w)=\operatorname{diag}(e^w,e^{-w}),\qquad
J_\theta=\begin{pmatrix}
-\cos(2\theta)&\sin(2\theta)\\
\sin(2\theta)&\cos(2\theta)
\end{pmatrix},
$$
$$
T_\theta=\cosh(u/2)I+\sinh(u/2)J_\theta,\qquad
X=D(\alpha u),\qquad Y_\theta=T_\theta X T_\theta,
$$
$$
A=D(\alpha u/p),\qquad B_\theta=Y_\theta^{1/p}.
$$

The real symmetric involution $J_\theta^2=I$ gives the two spectral
values $e^{u/2}$ and $e^{-u/2}$ of $T_\theta$. Thus $T_\theta$ is positive
definite with determinant one. So are $X$, $Y_\theta$, $A$, and $B_\theta$.
Since $T_\theta X T_\theta=Y_\theta$, uniqueness of the positive Riccati
solution identifies $X^{-1}\#Y_\theta=T_\theta$. Two-point functional
calculus also gives

$$
T_\theta^\alpha=\cosh(\alpha u/2)I+
 \sinh(\alpha u/2)J_\theta.
$$

The unrooted spectral geometric core is therefore
$F_\theta=T_\theta^\alpha X T_\theta^\alpha$. At zero angle,

$$
T_0=D(-u/2),\qquad Y_0=D((\alpha-1)u),\qquad F_0=I,
$$
$$
F'_0=d_SK,\qquad d_S=2\sinh(\alpha u),\qquad
K=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

The input core has derivative

$$
Y'_0=2\bigl(\sinh(\alpha u)-\sinh((\alpha-1)u)\bigr)K.
$$

The Renyi core is

$$
C_\theta=D(-k(\alpha-1)u/2)Y_\theta^kD(-k(\alpha-1)u/2).
$$

The diagonal values of $Y_0$ are distinct and positive. Two-point
functional calculus differentiates the off-diagonal power term by its
divided difference. It yields $C_0=I$ and

$$
C'_0=d_RK,\qquad
d_R=2\bigl(\sinh(\alpha u)-\sinh((\alpha-1)u)\bigr)
 \frac{\sinh(k(\alpha-1)u)}{\sinh((\alpha-1)u)}.
$$

For a real symmetric two by two matrix with entries $a,b,c$, the largest
eigenvalue is

$$
\frac{a+c+\sqrt{(a-c)^2+4b^2}}2.
$$

If its value at zero is the identity and its derivative is $dK$ with
$d\ge0$, this formula gives right-hand largest eigenvalue derivative $d$.
The positive real output powers therefore give the slopes $d_S/p$ and
$d_R/q$. The chosen inequality in $u$, together with
$0<\sinh(\alpha u)-\sinh((\alpha-1)u)<\sinh(\alpha u)$, implies

$$
\frac{d_R}{q}<\frac{d_S}{p}.
$$

The difference of the largest eigenvalues, divided by the positive angle,
tends to this strictly positive slope difference. A sufficiently small
positive angle therefore gives the strict largest eigenvalue violation.
The determinant-one facts for the inputs and outputs are paper calculations
(`det A = det B = 1`), not formalized. The failure of log-majorization comes
directly from the first largest-eigenvalue product inequality, so it does not
need determinant equalities in the Lean proof.

## Falsifier

A result only at one weight, with a fixed gap above $\alpha q$, only for
real input matrices, or conditional on the matrix expansion would not
establish the requested family. A comparison of entries alone is not a
comparison of the largest eigenvalues. Numerical evaluation is not a
substitute for the strict inequality proof. Replacing the spectral geometric
mean with a differently weighted mean changes the question.

## Evidence

The source definitions, Theorem 3.4(1), and the two exact Problem 3.5
quotations are recorded in `Library/QuantumBounds/hiai2026quasigeometric.md`.
The spectral geometric mean, weighted geometric mean, and real matrix powers
are reused from their existing declarations rather than redefined. The Renyi
mean is the existing `SharpWeightedLin.hiaiRMean`; its `CFC.rpow` powers
agree with the spectral powers on positive definite inputs.
The intended closed target is
`D5.S3.Quantum.Matrix.HiaiSpectralGeometricRenyi.result : ¬ claim`.

**Proved in Lean:** The module establishes
`D5.S3.Quantum.Matrix.HiaiSpectralGeometricRenyi.result : ¬ claim`.
Its private counterexample construction supplies, for every $\alpha>1$,
$q>0$, and $p>\alpha q$, positive definite complex two by two inputs with
a strict largest-eigenvalue violation. The determinant-one facts are paper
calculations (`det A = det B = 1`), not formalized; the failure of
log-majorization follows directly from the first largest-eigenvalue product
inequality. The result's axiom closure is `Classical.choice`, `Quot.sound`,
and `propext`.

## Triage

**Proved in Lean:** The obstruction is
first-order splitting at a commuting pair where both means are the identity.
The positive Riccati construction in Route chooses the geometric transition
directly. Exponential estimates with $k=\alpha q/p<1$ choose a finite $u$
such that $p\sinh(k(\alpha-1)u)<q\sinh((\alpha-1)u)$.
This makes the Renyi slope strictly smaller than the spectral geometric slope.

**Derived on paper, not formalized:** The same local mechanism can be seen
with the fixed-spectrum family

$$
A=\operatorname{diag}(e^{\alpha L},e^{-\alpha L}),\qquad
B_\theta=U_\theta\operatorname{diag}
 (e^{(\alpha-1)L},e^{-(\alpha-1)L})U_\theta^{\mathsf T}.
$$

Its right-hand spectral geometric coefficient is

$$
\frac{\sinh(\alpha pL)\sinh((\alpha-1)pL)}
 {p\sinh(pL/2)\cosh((\alpha-1/2)pL)},
$$

which grows at rate $e^{(\alpha-1)pL}$. Its Renyi coefficient is
$2\sinh(\alpha(\alpha-1)qL)/q$, which grows at rate
$e^{\alpha(\alpha-1)qL}$. The condition $p>\alpha q$ separates these
rates. The implemented family in Route uses a positive Riccati transition
rather than this fixed-spectrum rotation. The two descriptions give the
same first-order input direction up to a positive scale; the explicit
fixed-spectrum family and its displayed coefficients are not separate Lean
conclusions here.

**Proved in the source, not formalized:** Theorem 3.4(1) gives
$SG_{\alpha,p}\prec_{\log}R_{\alpha,q}$ for all positive definite pairs
in every finite dimension when $\alpha>1$, $p,q>0$, and $p\le\alpha q$.
The sufficient direction is attributed to the source, not to this module.

**Derived on paper, not formalized:** Combining the source sufficiency with
the two dimensional necessity and its direct sum extension gives the complete
characterization: for each $\alpha>1$, $p,q>0$, and fixed dimension $n\ge2$,
the comparison holds for every positive definite pair if and only if
$p\le\alpha q$.

**Derived on paper, not formalized:** A two dimensional counterexample
extends to every $n\ge2$ by $A\oplus I_{n-2}$ and $B\oplus I_{n-2}$.
Both means preserve these direct sums. For a positive determinant-one
two by two matrix, its largest eigenvalue is at least one, so adjoining
unit eigenvalues preserves the strict largest eigenvalue comparison.
Both enlarged determinants remain one.

**Proved in the source, not formalized:** The corresponding parameter
comparison for $0<\alpha<1$ is the source's Theorem 3.3. It is separate
from Problem 3.5 and is not a new conclusion of this refutation.

**Proved in Lean:** The counterexample family and closed refutation are
complete in the module named above. The source sufficient comparison and the
higher dimensional direct sum deduction are not additional Lean theorems here.

## ASSUMED-UNVERIFIED

The supplied arXiv v3 statement and preregistration identify the source
question. No fresh online literature search is asserted. Later-literature
completeness and worldwide priority are unverified and are not claimed.
The paper deductions above are separate from the compiled
Lean conclusions, and the source sufficient direction remains separately
attributed.
