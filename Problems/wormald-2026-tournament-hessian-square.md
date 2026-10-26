---
slug: wormald-2026-tournament-hessian-square
bibkey: wormald2026tournaments
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/WormaldTournamentHessian/Result.result
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

The rational-square structure is expressed through the integral skew adjacency
$S=A-A^{\mathsf T}$:

$$\frac d{\mathcal H}=
\left(\frac{\det(dI+S)}{\det(S+idI)/i}\right)^2.$$

The corresponding source note is `D5/L/GraphInvariants/wormald2026tournaments`.
The theorem `calH_closedForm` computes the actual analytic Hessian determinant;
`result` proves nonvanishing and rational squareness for every local solution.

## Gap

**PROVED.** `D5.S3.Combinatorics.WormaldTournamentHessian.Result.result`
proves `claim`, including existence by the complex implicit function theorem
and the conclusion for every complex $C^2$ local solution. The consumed theorem
`calH_closedForm` proves

$$\mathcal H(h)=d\frac{\det(d^2I+S^2)}{\det(d^2I-S^2)}.$$

The determinant, logarithmic phase and two real Fréchet derivatives are the
original analytic definitions. No algebraic expression replaces them.

## Route

Tournament completeness gives $2C=J+S$, where $C=\frac12I+A$ and every
entry of $J$ is one. For $Q(y)=\operatorname{diag}(2/y)-S$, the matrix
determinant lemma gives, near the constant point $z=2/d$,

$$K(y)=\det Q(y)\prod_j(y_j/2)
 \left(1-\mathbf1^{\mathsf T}Q(y)^{-1}\mathbf1\right).$$

The shifted determinant is nonzero by strict diagonal dominance. Regularity
makes the row and column sums of $S$ zero. Thus at the constant point,
$Q=dI-S$ and $V=Q^{-1}$ has every row and column sum equal to $1/d$.
Writing $\alpha(y)=\mathbf1^{\mathsf T}Q(y)^{-1}\mathbf1$, the derivative
formulas in the original $y$ coordinates are

$$\alpha_j=\frac12,\qquad
\alpha_{jk}=z^{-2}(V_{jk}+V_{kj})-z^{-1}\delta_{jk}.$$

Every local solution satisfies $\alpha(y',h(y'))=1$ on a neighbourhood.
First and second Fréchet differentiation of this germ gives $h_j=-1$ and
the four-term difference of the second derivatives of $\alpha$.
The exponential chart, principal logarithm at the positive value $z$, and
restriction from complex to real scalars identify the actual angular Hessian
with $-R^{\mathsf T}TR$, where $R$ has columns $e_j-e_d$ and

$$T=I-d(V+V^{\mathsf T}).$$

Both row and column sums of $T$ are $-1$. Put $U=[R\ \mathbf1]$.
Then $\det U=d$ and $U^{\mathsf T}TU$ has diagonal blocks
$R^{\mathsf T}TR$ and $-d$, with zero off-diagonal blocks. Hence

$$\det(R^{\mathsf T}TR)=-d\det T.$$

The resolvent calculation yields

$$T(d^2I-S^2)=-(d^2I+S^2).$$

The quadratic denominator is nonsingular because it factors as
$(dI-S)(dI+S)$. Regular tournaments have odd order, so $d-1$ is even;
the overall minus sign of the angular Hessian leaves its determinant
unchanged. Taking determinants gives `calH_closedForm`.

Transposition identifies $\det(dI-S)$ and $\det(dI+S)$. The imaginary shift
$S+idI$ is a Gaussian-integer matrix with purely imaginary determinant in odd
dimension. Its determinant divided by $i$ is a nonzero integer. Factoring
$d^2I-S^2$ and $d^2I+S^2$ therefore expresses their determinant quotient as
the square of the rational in Motivation.

Finally, every first coordinate derivative of $K$ at the constant point is
$-\det(dI-S)/(2d^d)$, which is nonzero. The complex implicit function theorem
supplies existence; the Hessian calculation applies to every local solution.

## Falsifier

The source-faithfulness checks retain the final coordinate order, the
principal logarithm at the positive base value, complex $C^2$ regularity,
the local equation germ, and two real angular derivatives. An assertion for
only one chosen solution would not imply `claim`; `result` quantifies over
every function satisfying `IsLocalSolution`.

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

**PROVED.** `D5.S3.Combinatorics.WormaldTournamentHessian.Result.result`
settles Conjecture 6 in the stated formal model. The consumed public theorem
`calH_closedForm` computes $\mathcal H$ as the full-space quadratic determinant
quotient. Consequently the result is independent of which local solution
satisfying the specified germ is chosen.

**PROVED.** The private theorem `regularLocalSolution` derives existence
from Mathlib's complex implicit function theorem, using the exact nonzero
coordinate derivative computed by `regularColumnSlopeValue` and
`K_coordinate_deriv`. The private algebraic stage `regularAlgebraicSquare`
provides the nonzero rational square used by `result`.

- **OPEN.** A separate spectral formalization is not provided. The positive spectral
  square root is
  $\prod_k(d^2+\mu_k^2)/(d^2-\mu_k^2)$, taking one $\mu_k\ge0$ from each
  pair $\pm i\mu_k$ of eigenvalues on $W$. Zero pairs contribute one.
  Each factor follows from the two eigenvalues of a skew-symmetric block;
  the bound $\mu_k<d$ makes it positive. This is a prose consequence of
  the proved closed form, not a separately kernel-checked spectral theorem.
- **OPEN.** The matrix-tree expression for the numerator is
  $\det(dI+S)=d^2 2^{d-1}\tau$, where $\tau$ is the number of directed
  spanning arborescences toward a fixed root. For the out-Laplacian
  $L=((d-1)/2)I-A$, one has $dI-S=2L+J$; regularity makes the rooted
  counts equal. The matrix-tree relation $\det_W L=d\tau$ then gives
  the stated factor. This is a prose consequence of the directed
  matrix-tree theorem, not a Lean theorem here.
- **OPEN.** Wormald's Conjecture 1, that the rotational tournament maximises
  the expected number of Hamilton cycles, is not settled. Substituting the
  proved formula for the Hessian into the source's asymptotic expression
  would express its Hessian contribution spectrally. Establishing the
  resulting extremal inequality remains a separate problem.

## ASSUMED-UNVERIFIED

The complete source text, printed page numbers, exhaustive literature
coverage and priority were not independently checked. The supplied source
and bibliographic excerpts are used without a new network search.
The spectral product and directed matrix-tree consequences are mathematical
expositions, not separate Lean theorems in this module. Wormald's Conjecture 1
remains open here.
