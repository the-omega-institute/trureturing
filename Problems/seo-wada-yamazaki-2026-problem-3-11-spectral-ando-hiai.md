---
slug: seo-wada-yamazaki-2026-problem-3-11-spectral-ando-hiai
bibkey: seowadayamazaki2026andohiai
doi: 10.1016/j.laa.2026.05.013
url: https://arxiv.org/abs/2512.22807
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation.result
---

# Failure of the spectral geometric Ando-Hiai implication near an endpoint

## Problem

For strictly positive operators, set

$$
A\# B=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2},
\qquad
F_t(A,B)=A\natural_tB=(A^{-1}\#B)^tA(A^{-1}\#B)^t.
$$

The order is the Loewner order, and every power is a spectral real power.
Seo-Wada-Yamazaki, Problem 3.11, asks whether, for
$t\in(0,1)\setminus\{1/2\}$ and every $0<q\le1$,

$$
F_t(A,B)\le I\quad\Longrightarrow\quad F_t(A^q,B^q)\le I
$$

holds for all strictly positive operators. The closed finite dimensional
assertion quantifies over every such $t,q$, every dimension $m$, and every
positive definite complex $m\times m$ pair. A complex two by two
counterexample therefore refutes that assertion and the operator assertion.

## Motivation

Theorem 3.9 proves the implication when
$q\le\min\{t/(1-t),(1-t)/t\}$. At a fixed $q\in(0,1)$ this leaves
both endpoint regions outside the source sufficient range. The target family
requires a two dimensional counterexample for each such $q$, with a single
pair valid at every sufficiently small positive $t$.

## Gap

The original mean and original powers must be used, and the matrices must
be proved positive definite. A positive limiting coefficient alone is
insufficient: one must obtain a finite parameter, choose a scalar scaling,
and prove the Loewner inequalities throughout a positive interval in $t$.
No matrix expansion, derivative, or coefficient inequality may be added as
an unproved premise. The target is preregistered in issue #31242.

## Route

**Proved in Lean:** Fix $q\in(0,1)$. For $u>0$ and a real scaling parameter $b$, use

$$
A_u=\operatorname{diag}(1,e^{-u/2}),\qquad
B_{u,b}=\frac{e^b}{4}
\begin{pmatrix}
3e^u+e^{-u}&\sqrt3(e^u-e^{-u})\\
\sqrt3(e^u-e^{-u})&e^u+3e^{-u}
\end{pmatrix}.
$$

**Paper description:** The second matrix is
$e^bR_{\pi/6}\operatorname{diag}(e^u,e^{-u})R_{\pi/6}^{\mathsf T}$.

**Proved in Lean:** Both matrices are positive definite, and the existing
spectral power has the exact identities

$$
A_u^q=A_{qu},\qquad B_{u,b}^q=B_{qu,qb}.
$$

For $B_{u,b}$, these follow from two-point functional calculus for the
self-adjoint involution

$$
J=\begin{pmatrix}1/2&\sqrt3/2\\\sqrt3/2&-1/2\end{pmatrix},
\qquad J^2=I,
$$

whose affine spectral values are $e^{b+u}$ and $e^{b-u}$.

The scalar proof uses the normalization $h=e^{-u/4}\in(0,1)$ and the
polynomials and radicals

$$
p(h)=h^3-h^5,\qquad r(h)=1-h^8,\qquad
T(h)=1+h^3+h^5+h^8,
$$
$$
W(h)=\sqrt{p(h)^2+r(h)^2-p(h)r(h)},\qquad
Z(h)=\sqrt{3+h^2+8h^5+h^8+3h^{10}}.
$$

Here $W,Z>0$, $W<T$, and direct polynomial algebra gives

$$
T^2-W^2=h^3Z^2.
$$

Set

$$
\alpha(h)=\frac{r(h)/2-p(h)}{W(h)},\qquad
K(h)=\log\frac{T(h)+W(h)}{Z(h)},
$$
$$
H(u)=\alpha(e^{-u/4})
 \left(\frac{3u}{8}+K(e^{-u/4})\right).
$$

Rationalizing the coefficient gives the exact identity

$$
\alpha(h)-\frac12=h^3E(h),\qquad
E(h)=\frac{3(1-h^2)(p(h)-r(h))}
 {2W(h)(r(h)-2p(h)+W(h))}.
$$

The identity holds wherever its denominators are nonzero. They are
nonzero in a neighborhood of zero, since $W(0)=1$ and
$r(0)-2p(0)+W(0)=2$. The functions $E$, $\alpha$, and $K$ are
continuous at zero, with values $-3/4$, $1/2$, and
$\log(2/\sqrt3)$, respectively. Since $u e^{-3u/4}\to0$,

$$
H(u)-\frac{3u}{16}
=\frac{3u}{8}\left(\alpha(e^{-u/4})-\frac12\right)
 +\alpha(e^{-u/4})K(e^{-u/4})
\longrightarrow\frac12\log\frac2{\sqrt3}.
$$

The linear terms cancel in $D_q(u)=H(qu)-qH(u)$. Hence

$$
D_q(u)\longrightarrow
\frac{1-q}{2}\log\frac2{\sqrt3}
=\frac{1-q}{4}\log\frac43>0.
$$

This proves the existence of a finite $u>0$ with $D_q(u)>0$.

The matrix bridge is an explicit positive Riccati solution. Define

$$
X=T+r/2-p,\qquad Y=\sqrt3r/2,\qquad V=T-r/2+p,
$$
$$
P_{u,b}=\frac{e^{b/2}}{h^2Z}
\begin{pmatrix}X&Y\\Y&V\end{pmatrix}.
$$

Its first diagonal entry is positive, and
$\det P_{u,b}=e^b/h>0$. Direct multiplication proves

$$
P_{u,b}A_uP_{u,b}=B_{u,b}.
$$

Uniqueness of the positive Riccati solution, applied to the existing
geometric mean, therefore identifies
$A_u^{-1}\#B_{u,b}=P_{u,b}$. Its two positive eigenvalues are

$$
\lambda_\pm=\frac{e^{b/2}(T\pm W)}{h^2Z}.
$$

Their product is $e^b/h$, and the normalized difference of the two diagonal
entries of $P_{u,b}$ is $\alpha(h)$. Thus

$$
\log\lambda_+=\frac b2-2\log h+K(h),\qquad
\log\lambda_++\log\lambda_-=b-\log h.
$$

Two-point functional calculus for $P_{u,b}^t$ gives the derivative of its
first diagonal entry at zero:

$$
\left.\frac{d}{dt}(P_{u,b}^t)_{11}\right|_{t=0}
=\frac{\log\lambda_++\log\lambda_-}{2}
 +\alpha(h)\frac{\log\lambda_+-\log\lambda_-}{2}
=\frac b2+\frac u8+H(u).
$$

Consequently, for $F_t=F_t(A_u,B_{u,b})=P_{u,b}^tA_uP_{u,b}^t$,

$$
F_0=A_u,\qquad
\left.\frac{d}{dt}(F_t)_{11}\right|_{t=0}
=b+\frac u4+2H(u).
$$

The remaining real symmetric entries also have derivatives at zero.
Choose finite $u$ as above, write $D=D_q(u)>0$, and set

$$
b=-\frac u4-2H(u)-\frac Dq.
$$

The first entry slopes of $F_t(A_u,B_{u,b})$ and
$F_t(A_u^q,B_{u,b}^q)=F_t(A_{qu},B_{qu,qb})$ are then
$-D/q<0$ and $D>0$, respectively.

The order step uses the diagonal and determinant criteria directly.
Write the unpowered-input mean as
$\begin{pmatrix}a(t)&c(t)\\c(t)&d(t)\end{pmatrix}$, where
$a(0)=1$, $c(0)=0$, $d(0)=e^{-u/2}<1$, and $a'(0)<0$.
The first principal minor and determinant of $I-F_t$ vanish at zero and
have positive derivatives

$$
\left.\frac{d}{dt}(1-a(t))\right|_{t=0}=-a'(0)>0,
$$
$$
\left.\frac{d}{dt}\bigl((1-a(t))(1-d(t))-c(t)^2\bigr)
\right|_{t=0}=-a'(0)(1-e^{-u/2})>0.
$$

They are therefore positive for all sufficiently small positive $t$.
The two by two positive definiteness criterion gives $I-F_t>0$, hence
$F_t\le I$. For the powered-input mean, its first diagonal entry starts
at one and has positive derivative, so it exceeds one throughout a
sufficiently small positive interval. The corresponding diagonal entry of
$I-F_t(A_u^q,B_{u,b}^q)$ is negative, which excludes positive
semidefiniteness and proves $F_t(A_u^q,B_{u,b}^q)\nleq I$.

Intersecting the two intervals gives one pair and $t_0>0$ valid for every
$0<t<t_0$. Taking $q=1/2$ and
$t=\min\{t_0/2,1/4\}$ refutes the closed assertion. The order conclusions follow from the entry and determinant signs above.

## Falsifier

A result for one $q$ does not establish the full family. Allowing the pair
to depend on $t$ does not establish a single pair valid on an interval.
A conditional derivative or asymptotic expansion does not close the
construction. Entrywise comparisons cannot replace the Loewner order,
and a numerical largest eigenvalue calculation is not a proof of either
matrix inequality. The source definitions must not be replaced by a
related mean with a different weight.

## Evidence

The source locator, definitions, Problem 3.11, Theorem 3.9, and
Remark 3.10 are recorded in
`Library/Divergence/seowadayamazaki2026andohiai.md`.
The closed target is
`D5.S3.Quantum.Matrix.SeoWadaYamazakiAndoHiaiRefutation.result : ¬ claim`.
The existing `specMean` and `SpectralPower.mpow` are the required mean
and powers, rather than new definitions.

**Proved in Lean:** The module establishes
`D5.S3.Quantum.Matrix.SeoWadaYamazakiAndoHiaiRefutation.result : ¬ claim`.
Its private counterexample theorem supplies, for every $q\in(0,1)$,
a single positive definite complex two by two pair and $t_0>0$ such that
$F_t(A,B)\le I$ and $F_t(A^q,B^q)\nleq I$ for every $0<t<t_0$.
The proof includes the scalar limit, finite parameter choice, positive
Riccati bridge, exact powers, and entry and determinant order arguments.
The result's axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.

**Literature check as of 2026-11-17** (preregistration
[#31242](https://github.com/the-omega-institute/trureturing/issues/31242)):
**Tier 1**, an end-of-paper problem in a December 2025 preprint and a 2026
journal article. The checked sources and their relation to Problem 3.11 are:

- Yuki Seo, Shuhei Wada, and Takeaki Yamazaki, *On the Ando-Hiai property
  for spectral geometric means*, arXiv:2512.22807, has only version v1.
  Problem 3.11 is the target; Theorem 3.9 provides the central sufficient
  parameter region.
- L. Gan and T.-Y. Tam, *Inequalities and limits of weighted spectral
  geometric mean*, arXiv:2109.00351v2, Theorem 3.3: no erratum was found
  in the checked scope. The proof's final step treats
  $\lambda_{\max}(P^{-1})$ as $1/\lambda_{\max}(P)$; the correct identity
  is $1/\lambda_{\min}(P)$. The diagnosis is a paper statement, not an
  additional Lean conclusion.
- Hiai, arXiv:2510.04691v3, Problem 3.12 and Proposition 3.10, cites SWY
  without resolving Problem 3.11.
- Vuong and Dinh, *Quantum divergence and barycenter induced by the
  (k,t)-spectral geometric mean*, Linear Algebra and its Applications 753,
  DOI 10.1016/j.laa.2026.08.033, cites SWY without resolving this problem.
- Dinh, Tam, and Vuong, *A new weighted spectral geometric mean and
  properties*, Electronic Journal of Linear Algebra 40 (2024), 333-342,
  studies the different parameter line $F_{k,1/2}$.

No resolution was found in this checked scope. This is a bounded literature
check; it does not certify worldwide priority or originality.

## Triage

**Proved in Lean:** The mechanism is first-order splitting in $t$ at the
first diagonal equality point at $t=0$. The coefficient tends to
$D_\infty=(1-q)\log(2/\sqrt3)/2>0$.

**Paper interpretation:** With $\theta=\pi/6$, the same constant is

$$
D_\infty=(1-q)\cos(2\theta)\log\sec\theta>0.
$$

**Computed, not certified:** At moderate spectral separation the coefficient $D_q(u)$ can instead be
nonpositive. For example, direct binary64 evaluation of the displayed scalar
formulas gives a negative value at $q=1/2,u=4$. This finite numerical check
is not used as a proof. It explains why searches confined to moderate
parameters can miss the endpoint obstruction.

**Paper consequence:** The symmetry
$A\natural_tB=B\natural_{1-t}A$ transfers a counterexample near zero
to one near one by interchanging the inputs. This symmetry and the
transferred family are not additional Lean conclusions here.

**Derived on paper, not formalized:** The universal implication asserted
in L. Gan and T.-Y. Tam, *Inequalities and limits of weighted spectral
geometric mean*, arXiv:2109.00351v2, Theorem 3.3, is incompatible with the
family above. At the end of its proof, replacing
$\lambda_{\max}(P^{-1})$ by $1/\lambda_{\max}(P)$ reverses the
spectral endpoint. The correct identity for positive definite $P$ is

$$
\lambda_{\max}(P^{-1})=\frac1{\lambda_{\min}(P)}.
$$

This identifies the specific proof error.

**Proved in the source, not formalized:** Theorem 3.9 gives the safe region

$$
\frac{q}{1+q}\le t\le\frac1{1+q}.
$$

The parameter region outside this safe region and outside the constructed
endpoint intervals remains open here, including middle values of $t$ for
$q$ close to one. The case $q=1$ is equality and is not a counterexample.

**Derived on paper, not formalized:** Fix $0<t<1$ and $0<q<1$, and compare
log largest eigenvalues in the unscaled-input family:

$$
E_{q,t}(u)=\log\lambda_{\max}F_t(A_{qu},B_{qu,0})
 -q\log\lambda_{\max}F_t(A_u,B_{u,0}).
$$

As the spectral parameter tends to infinity,

$$
E_{q,t}(u)\longrightarrow(1-q)(1-t)\log(3/4)<0.
$$

Thus increasing the spectral separation at fixed $t$ does not extend this
mechanism to the whole remaining parameter region. The construction covers
endpoint intervals whose size may depend on $q$ and the chosen pair.

## ASSUMED-UNVERIFIED

Later-literature completeness and worldwide priority are unverified and are
not claimed. The source sufficient theorem, Gan-Tam proof diagnosis,
endpoint symmetry, and fixed-$t$ asymptotic are separate paper statements;
they are not additional compiled conclusions.
