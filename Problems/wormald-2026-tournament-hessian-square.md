---
slug: wormald-2026-tournament-hessian-square
bibkey: wormald2026tournaments
doi: null
triage: open
motivation_gids:
  - D5/S3/Combinatorics/WormaldTournamentHessian/Result.claim
url: https://arxiv.org/abs/2610.16245
---

# The rational-square conjecture for the tournament Hessian

## Problem

N. C. Wormald, *Tournaments with many Hamilton cycles*,
arXiv:2610.16245, section 1:

> Conjecture 6. For every regular tournament $T^*$ on at least three vertices,
> ${\cal H}\neq 0$ and $d/{\cal H}$ is the square of a rational.

The source defines $B=I_d-(\tfrac12 I_d+A)D_y$,
$K(\mathbf y)=\det B$, $z=2/d$ and $\mathbf z=(z,\ldots,z)$, and states:

> one may solve $K(\mathbf y)=0$ in the neighbourhood of $\mathbf z$ and obtain
> $y_d=h(y_1,\dots,y_{d-1})$

It defines $\tilde f(\theta)=\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}})$,
and lets

> ${\cal H}$ denote the determinant of the Hessian … of $\tilde f$ at $\theta_j=0$.

The formal namespace is `D5.S3.Combinatorics.WormaldTournamentHessian.Result`.
`claim` includes existence of a complex $C^2$ local solution and nonvanishing
and rational squareness for every such solution. `hessian` uses two real
Fréchet derivatives of the complex-valued `phase`, evaluated on `Pi.single`
coordinate vectors. `appendLast` uses `Fin.snoc` and retains vertex order.

## Motivation

The exact computations suggest a rational square without explaining its
structure. The proposed identity uses the integral skew adjacency
$S=A-A^{\mathsf T}$:

$$\frac d{\mathcal H}=
\left(\frac{\det(dI+S)}{\det(S+idI)/i}\right)^2.$$

The corresponding source note is `D5/L/GraphInvariants/wormald2026tournaments`.
A proof of rationality of the expression on the right does not by itself
identify it with the analytic expression on the left.

## Gap

**OPEN.** A kernel-checked proof relating the actual real angular Hessian to
the proposed determinant quotient is required. The general local existence
statement still requires a nonzero final-coordinate derivative of $K$ at
$\mathbf z$. `localSolutionOfInvertible` applies Mathlib's complex implicit
function theorem with this invertibility hypothesis; `determinantAtBase`
and `polynomialSmooth` discharge its zero-value and smoothness conditions.
No replacement of the Hessian by a prescribed algebraic expression is made.

## Route

An alternative to a general corank-one second-derivative formula is the
rank-one determinant identity. Tournament completeness gives
$2C=J+S$, where $J=\mathbf1\mathbf1^{\mathsf T}$. Set
$x_j=2/y_j=d e^{-u_j}$ and $Q(u)=\operatorname{diag}(x)-S$.
Near zero, $Q(u)$ is invertible and

$$K(y)=\det Q(u)\prod_j(y_j/2)
 \left(1-\mathbf1^{\mathsf T}Q(u)^{-1}\mathbf1\right).$$

Regularity implies $S\mathbf1=0$ and
$\mathbf1^{\mathsf T}S=0$. At zero, $Q=dI-S$ and both the row and column
sums of $Q^{-1}$ are $1/d$. For
$\alpha(u)=\mathbf1^{\mathsf T}Q(u)^{-1}\mathbf1$, differentiation gives

$$\alpha_j(0)=1/d,\qquad
\alpha_{jk}(0)=(Q^{-1})_{jk}+(Q^{-1})_{kj}-\delta_{jk}/d.$$

The implicit relation $\alpha(u',\varphi(u'))=1$ then gives
$\varphi_j=-1$. Let $R$ have columns $e_j-e_d$ and put
$T=I-d(Q^{-1}+Q^{-\mathsf T})$. Its second derivative matrix is
$R^{\mathsf T}TR$. On $W=\mathbf1^\perp$, the Gram determinant of these
columns is $d$, so

$$\mathcal H=d\det_W T
=d\frac{\det_W(d^2I+S^2)}{\det_W(d^2I-S^2)}.$$

A full-space version avoids choosing a basis of $W$. Let $U=[R\ \mathbf1]$.
Row addition gives $\det U=d$. Since $T\mathbf1=-\mathbf1$ and
$\mathbf1^{\mathsf T}T=-\mathbf1^{\mathsf T}$, the off-diagonal blocks of
$U^{\mathsf T}TU$ vanish and its final diagonal entry is $-d$.
Taking determinants gives $\det(R^{\mathsf T}TR)=-d\det T$.
Also, with $Q=dI-S$,

$$T=I-d(Q^{-1}+Q^{-\mathsf T})
=-(d^2I+S^2)(d^2I-S^2)^{-1}.$$

Oddness of $d$ then gives the same Hessian formula using full-space
determinants. This is a proposed replacement for the subspace determinant
bridge, not an additional Lean theorem.

Here $\dim W=d-1$ is even. The angular substitution $u=i\theta$
negates the Hessian and leaves its determinant unchanged.
The full-space determinants in the last quotient each acquire the same
factor $d^2$ from the constant direction. Transposition yields
$\det(dI-S)=\det(dI+S)$. Also
$\det(S-idI)=\overline{\det(S+idI)}=-\det(S+idI)$ for odd $d$.
Factoring $d^2I\pm S^2$ therefore yields the proposed square.
This is a proposed mathematical derivation; the analytic and subspace
identities in this paragraph are not asserted as Lean theorems.

## Falsifier

An incorrect sign in the second implicit derivative, an incorrect factor $d$
in the Gram determinant, or a missing constant-direction factor would
invalidate the proposed closed form. The faithful claim requires all local
solutions, not a single selected function or a formal power series.

## Evidence

The scripts and their exact bytes are present at the immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/0397e825286f7112ddd8052d8f8e22380a609021/experiments/wormald-tournament-hessian).

- **COMPUTED.** `python3 wormald-hessian.py`, exit 0; SHA-256
  `6c01f9f8405e71ccbfb32f9b930383250954e7e85d3c84368866d7dadd44428e`.
  For the rotational tournaments at $d=3,5,7$, the determinant at
  $\mathbf z$ is zero and the respective values of $d/\mathcal H$ are
  $4$, $1936/361$ and $9193024/1515361$, with positive rational square
  roots $2$, $44/19$ and $3032/1231$.
- **COMPUTED.** `python3 wormald-closed-form.py`, exit 0; SHA-256
  `d83f689a4b96551efca96fda60dcc6b4d495ebd08851a4e699fa6f11b81656f9`.
  With random seed 11, three successive regular tournaments obtained by
  directed-triangle reversals at each $d\in\{3,5,7,9,11\}$ satisfy the
  closed-form comparison. All 15 comparisons return true. The signed
  quotient at $d=5$ is $44/19$; the sign is removed by squaring.

These scripts use exact rational arithmetic for their determinant and
implicit-derivative formulas. They do not certify the analytic bridge
between these formulas and Mathlib's derivatives.

## Triage

### What the settlement shows

**OPEN.** The conjecture is not claimed settled by this implementation.

**PROVED.** `D5.S3.Combinatorics.WormaldTournamentHessian.Result.regularOdd`
shows that a regular tournament with at least three vertices has odd order.
`shiftedDetNeZero` proves nonvanishing of $S+cI$ whenever $|c|=d$.
`imaginaryShiftIntegral` shows that $\det(S+idI)=bi$ with $b\in\mathbb Z$.
`algebraicRatioRational` constructs a nonzero rational equal to
$\det(dI+S)/(\det(S+idI)/i)$ in odd dimension, without requiring regularity.
`algebraicSquareIdentity` proves

$$\frac{\det(d^2I-S^2)}{\det(d^2I+S^2)}
=q^2\quad(q\in\mathbb Q,\ q\ne0).$$

`regularAlgebraicSquare` supplies this nonzero rational square for every
regular tournament of order at least three. These are private algebraic
lemmas; none states the equality of this quotient with $d/\mathcal H$.

**PROVED.** `D5.S3.Combinatorics.WormaldTournamentHessian.Result.regularDegree`
gives $d=2r+1$ and the integral row sum $r$.
`determinantAtBase` proves $K(\mathbf z)=0$, and `polynomialSmooth` proves
that $K$ is complex $C^2$ everywhere. `localSolutionOfInvertible` proves
existence of a local solution conditional on invertibility of the
final-coordinate derivative. It does not discharge that hypothesis.

Its candidate mechanism is a rank-one determinant identity followed by
skew-symmetric spectral pairing, as detailed in Route.

- **OPEN.** The closed form for the analytic Hessian requires the missing
  derivative and subspace determinant bridges. Evidence contains the exact
  finite comparisons, including the rotational $d=5$ test.
- **OPEN.** Conditional on the closed form, the proposed positive spectral
  square root is
  $\prod_k(d^2+\mu_k^2)/(d^2-\mu_k^2)$, taking one $\mu_k\ge0$ from each
  pair $\pm i\mu_k$ of eigenvalues on $W$. Zero pairs contribute one.
  Each factor follows from the two eigenvalues of a skew-symmetric block;
  the bound $\mu_k<d$ makes it positive. This is a prose consequence of
  the proposed closed form, not a kernel-checked theorem.
- **OPEN.** The matrix-tree expression proposed for the numerator is
  $\det(dI+S)=d^2 2^{d-1}\tau$, where $\tau$ is the number of directed
  spanning arborescences toward a fixed root. For the out-Laplacian
  $L=((d-1)/2)I-A$, one has $dI-S=2L+J$; regularity makes the rooted
  counts equal. The matrix-tree relation $\det_W L=d\tau$ then gives
  the stated factor. This is a prose consequence of the directed
  matrix-tree theorem, not a Lean theorem here.
- **OPEN.** Wormald's Conjecture 1, that the rotational tournament maximises
  the expected number of Hamilton cycles, is not settled. Substituting a
  proved formula for the Hessian into the source's asymptotic expression
  would express its Hessian contribution spectrally. Establishing the
  resulting extremal inequality remains a separate problem.

## ASSUMED-UNVERIFIED

The complete source text, printed page numbers, exhaustive literature
coverage and priority were not independently checked. The supplied source
and bibliographic excerpts are used without a new network search.
The proposed analytic, spectral and matrix-tree derivations have not been
fully compiled in Lean. No `result : claim` or problem-resolution annotation
is asserted without that proof.
