---
slug: li-poon-sze-2011-p2-realignment-gap
bibkey: lipoonsze2011realignment
doi: 10.1088/1751-8113/44/31/315304
url: https://arxiv.org/abs/1103.2499v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.result
---

# Strict rectangular realignment gap

## Problem

C.-K. Li, Y.-T. Poon and N.-S. Sze, *A note on the realignment criterion*,
Journal of Physics A 44 (2011), 315304, arXiv:1103.2499v2, ask:

> (P2) To determine if $\widetilde B_\ell(m,n)>B_\ell(m,n)$.

Their elementary symmetric function is
$f_\ell(s)=\sum_{i_1<\cdots<i_\ell}s_{i_1}\cdots s_{i_\ell}$,
with $m^2$ realignment singular values. $B_\ell$ ranges over separable
density matrices. $\widetilde B_\ell$ ranges over density matrices obeying
$\sum_i s_i\le1$. The target is strict inequality for every
$2\le m<n$ and $2\le\ell\le m^2$.

## Motivation

A strict gap distinguishes separability from the scalar CCNR constraint
at every nontrivial elementary symmetric order in rectangular dimensions.
The paper gives equality when $m=n$. Its numerical evidence at unequal
dimensions does not establish the quantified rectangular claim.

## Gap

Issue #30506 supplies the preregistered statement, quoted source and
construction formulas. No fresh external literature search is asserted.
The proof combines the general separable covariance tail bound with a
sharp symmetric-function estimate and actual positive normalized matrices
realizing a strictly larger profile.

## Route

Write $k=m^2$, $b(a)=(1-a)/(k-1)$ and

$$
g_\ell(a)={k-1\choose\ell}b(a)^\ell+
 {k-1\choose\ell-1}a b(a)^{\ell-1}.
$$

For a separable state, CCNR gives $\sum_i s_i\le1$ and the covariance
estimate gives

$$
\sum_{i\ge2}s_i\le c=\sqrt{\frac{(m-1)(n-1)}{mn}}.
$$

Set $\delta=1-c$. Increase the first coordinate to
$x_1=1-\sum_{i\ge2}s_i$. Coordinatewise monotonicity increases
$f_\ell$. Maclaurin's inequality applied to the nonnegative tail gives
$f_\ell(x)\le g_\ell(x_1)$. Since $x_1\ge\delta$ and
$\delta>1/(2m)\ge1/k$, this is at most $g_\ell(\delta)$.
This argument supplies the needed Schur-concavity comparison without
requiring a general theory of majorization.

The derivative is

$$
g_\ell'(a)=\frac{\ell-1}{k-1}{k-1\choose\ell-1}
 b(a)^{\ell-2}(b(a)-a).
$$

It is negative in $(1/k,1)$; hence $g_\ell$ is strictly decreasing on
$[1/k,1]$.

The common matrix construction has Bob space
$(\mathbb C^m\otimes\mathbb C^q)\oplus\mathbb C^r$. It is the sum
of $t$ times a Gram matrix of maximally entangled vectors, an identity
weight $u$ on the occupied block and $v$ on the remainder. Its trace is
$tmq+um^2q+vmr$. If $d=\operatorname{vec}I_m$, its realignment row Gram is

$$
q t^2 I+\bigl(q(2tu+mu^2)+rv^2\bigr)dd^\dagger.
$$

Its repeated eigenvalue is $qt^2$ and its distinguished eigenvalue is
$q(t+mu)^2+mr v^2$. The explicit density conditions and characteristic
polynomial retain all unused Bob coordinates.

The dimension ranges used in the proof are $m<n<m^3-m$ for the main
family, $m^3-m\le n<m^3$ for the supported family, and $m^3\le n$
for the uniform family. The supported family starts before the cubic
transition, so these ranges cover every rectangular dimension pair.

For the main LPS spectrum take $\alpha=1/\sqrt{mn}$,
$\beta=(1-\alpha)/(m^2-1)$,
$t=\beta/\sqrt q$, $u=\alpha^2-\beta/(m\sqrt q)$ and
$v=\alpha^2$. The eigenvalues are $\alpha^2,\beta^2,\ldots,\beta^2$.
The scalar gap follows from

$$
(1-\alpha)^2-c^2=
\frac{(\sqrt n-\sqrt m)^2}{mn}>0.
$$

For $n\ge m^3$, set $q=m^2$, $t=1/m^3$, $u=v=0$ and retain
the unused Bob coordinates. Every singular value is $1/m^2$.

In the supported band set $q=m^2-1$, $v=0$,
$\alpha_0=1/(m\sqrt q)$, $\beta_0=(1-\alpha_0)/q$,
$t=\beta_0/\sqrt q$ and $u=(m-\sqrt q)/(mq^2)$. Then
$t+mu=1/(mq)$, so the trace is one and the singular values are
$\alpha_0,\beta_0,\ldots,\beta_0$.
For $m\ge3$, $1/k<\alpha_0<1/(2m)<\delta$.
For $m=2$, the stronger exact comparison is
$\alpha_0<7/24<\delta$.
Zero extension and reindexing give the stated Bob dimension.

## Falsifier

The terminal statement must quantify over all natural $m,n,\ell$ in the
stated range and produce an actual complex matrix on
`Fin m × Fin n`. Its density predicate must mean positive semidefinite
with trace one. Its realignment must have entries
$R(\rho)_{(i,j),(a,b)}=\rho_{(i,a),(j,b)}$, and its trace norm must be
the existing CFC nuclear norm. The separating constant must bound every
actual finite convex combination of product density matrices.
A theorem assuming the required spectra or scalar constraints would not
settle this target.

## Evidence

The implementation uses the existing `IsDensity` and `IsSeparable`
predicates, the existing CFC trace norm, and native descending singular
values. The retained singular vector is taken from the row Gram and has
exactly $m^2$ coordinates, rather than Bob's larger $n^2$ coordinates.
The real Hermitian-coordinate correlation matrix is related to complex
realignment by explicit Hilbert--Schmidt isometries. A characteristic
polynomial identity transports its full singular spectrum, including
zeros. The published covariance estimate is reused from the existing
correlation-minor modules.

The terminal declaration
`D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2.result`
proves the complete rectangular statement. It constructs one density
matrix satisfying CCNR and a common real bound for every separable state,
with a strict elementary-symmetric gap. The three construction theorems
provide actual matrices and exact singular-value multiplicities; no
spectrum-realizability premise occurs in the terminal statement.

The separating constant $c'=g_\ell(\delta)$ gives
$B_\ell(m,n)\le c'<f_\ell(s(R(\rho)))\le\widetilde B_\ell(m,n)$.
The maxima exist: the finite-dimensional density set is compact, the
separable set is the convex hull of the compact product-density set,
and the CCNR feasible set is a closed subset of the density set.
Continuity of singular values and their elementary symmetric functions
then gives attainment on both sets.

The terminal `result` and `separable_esymm_bound` have `proof_shape: content`.
The terminal result retains `admission_basis: open-problem-resolution`.
Both contain the
new Newton--Maclaurin tail-budget induction on their live proof paths.
The three explicit matrix-existence lemmas have `proof_shape: bind-only`,
with the terminal `result` as their live consumer. They are constructions
obtained from the cited Gram, characteristic-polynomial and Hermitian
spectral identities; they do not supply an independent new proof mechanism.

## Triage

The proof mechanism is the covariance tail budget, its sharp
equal-tail elementary-symmetric upper bound, and positive normalized
witnesses whose leading singular value is strictly below $\delta$.
Together with Li--Poon--Sze's equal-dimensional equality, the rectangular
result answers (P2) for all dimension pairs. It does not determine the
exact maxima in (P1).

Peled, Te'eni, Carmi and Cohen's filter-normal-form bounds concern
correlation minor norms under additional assumptions. The present
argument uses a general covariance tail bound and does not assert that
all their bounds survive removal of filter normal form. The covariance
inequality and the main and uniform matrix constructions are attributed
to the literature; the supported interpolation and gap synthesis are
repository deductions.

## ASSUMED-UNVERIFIED

The supplied source quotations and bibliographic locations have not been
independently retrieved in this task. No exhaustive priority or recent
literature claim follows from the formal proof. The equal-dimensional equality is cited from the supplied
Li--Poon--Sze source and is not re-proved by this declaration.
