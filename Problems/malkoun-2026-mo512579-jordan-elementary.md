---
slug: malkoun-2026-mo512579-jordan-elementary
bibkey: malkoun2026mo512579
doi: null
url: https://mathoverflow.net/questions/512579
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/MalkounJordanElementary.result
---

# Malkoun's two-matrix elementary symmetric inequality

## Problem

This dossier anchors only the explicit first question of Malkoun's
*Promoting polynomial equalities for nonnegative variables to elementary symmetric
polynomial inequalities*, [MathOverflow 512579](https://mathoverflow.net/questions/512579),
revision 1, GUID DFD20136-D37A-462C-8A59-FD828AEEFF9A. The source first promotes
real nonnegative variables to Hermitian positive semidefinite matrices and sets
$L=XY+YX$ and $R=X^2+Y^2$. Its question reads (HTML formatting adapted):

> Given an $n$ by $n$ matrix $A$, denote by $\lambda(A)$ its "set" of eigenvalues,
> taking multiplicity into account. Moreover, denote by $e_k$ the $k$-th elementary
> symmetric polynomial. Note that both $L$ and $R$ are hermitian, so that their
> eigenvalues are all real. Is it true that
> $$e_k(\lambda(L)) \leq e_k(\lambda(R)),$$
> for any $n$ by $n$ hermitian positive semidefinite matrices $X$ and $Y$ and for
> any $k \in \{1, \dots, n\}$?

The precise assertion is: for every positive integer $n$, every pair of complex
Hermitian positive semidefinite $n\times n$ matrices $X,Y$, and every integer
$1\leq k\leq n$, the displayed inequality holds. Repeated eigenvalues retain
their algebraic multiplicity. No positivity of $XY+YX$, commutation,
invertibility, rank, simple-spectrum or dimension restriction is imposed.
The source's later unspecified question about promoting arbitrary symmetric
polynomial inequalities is not this dossier's assertion.

The source text is by [Malkoun (user 81645)](https://mathoverflow.net/users/81645)
and is licensed under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
See the [literature note](../Library/Eigenstructure/malkoun2026mo512579.md).

## Motivation

The scalar inequality $2xy\leq x^2+y^2$ motivates a comparison of the Hermitian
matrix polynomials through all elementary symmetric functions, including the
determinant at $k=n$. Eigenvalue-by-eigenvalue monotonicity cannot simply be
assumed for elementary symmetric functions when the Jordan product can have
negative eigenvalues. The source proposes Kronecker-product and immanant methods
and cites a separate determinant question as motivation. The argument here
instead compares every principal minor through one common Gram construction.

## Gap

The preregistered target and finite literature check are supplied by forward unit
[#24963](https://github.com/the-omega-institute/trureturing/issues/24963).
The source-page response observed at 2026-10-31T23:02:47Z has answer_count = 0,
is_answered = false and no accepted answer. This observation does not establish
worldwide novelty. The recorded broader literature search is
`not-found-in-searched-scope`, with its unreproduced portion disclosed below.

The reusable suppliers are the existing public `cauchyBinet` in
`D5/S3/Quantum/Schatten/CompoundMatrices.lean` and pinned Mathlib identities for
characteristic-polynomial coefficients, principal minors and Hermitian spectra.
The source assertion is resolved by applying those identities to the stacked
column construction; the proof is classified as bind-only throughout.

## Route

For a principal index set $S$ of cardinality $k$, let $X_S,Y_S$ be the selected
columns and stack $U=[X_S;Y_S]$, $V=[Y_S;X_S]$. Hermiticity gives

$$U^*U=V^*V=(X^2+Y^2)[S,S],\qquad U^*V=(XY+YX)[S,S].$$

For each common $k$-row selection $T$, write $u_T=\det U[T,:]$ and
$v_T=\det V[T,:]$. The real scalar inequality

$$\operatorname{Re}(\overline{u_T}v_T)
\leq \frac{|u_T|^2+|v_T|^2}{2}$$

follows by adding the nonnegative squares of the real and imaginary parts of
$u_T-v_T$. Cauchy–Binet uses the same row selections for all three determinants.
Their sums and the equality of the Gram matrices therefore give

$$\operatorname{Re}\det((XY+YX)[S,S])
\leq \operatorname{Re}\det((X^2+Y^2)[S,S]).$$

For every Hermitian matrix $M$, the characteristic-polynomial principal-minor
identity and Vieta's formula identify $e_k(\lambda(M))$ with the sum of the real
principal determinants over all $k$-element $S$. Summing the preceding inequality
proves the exact source assertion. No division by a determinant or eigenvalue
is used, so singular and zero matrices are included.

## Falsifier

A proof restricted to commuting matrices, to positive Jordan products, to one
dimension, to $k=1$ or $k=n$, or to distinct eigenvalues would miss this question.
The compiled `claim` instead quantifies all positive $n$, all source matrices and
every $1\leq k\leq n$. Its statistic is a sum over $k$-element subsets of the
indexed eigenvalue list, so equal eigenvalues at different indices are counted
separately. Mathlib's `roots_charpoly_eq_eigenvalues` supplies the multiplicity
correspondence. The retained Reg source checks an inhabited instance at
$n=k=1$, $X=Y=0$; the assertion is not vacuous.

## Evidence

The mathematical source is
`D5/S3/Quantum/Matrix/MalkounJordanElementary.lean`; its public theorem
`D5/S3/Quantum/Matrix/MalkounJordanElementary.result` has type `claim`.
The two public definitions express the original statistic and source proposition.
Its four private authored helpers are `jordan_hermitian`, `gram_det_le`,
`principal_det_le` and `spectral_minors`. The consumer edges are
`claim → jordan_hermitian`, `principal_det_le → gram_det_le`, and
`result → principal_det_le, spectral_minors, claim`. The helpers and result
are all bind-only; no escape witness is claimed. Compiler-generated declarations
are not additional authored companion claims.

The existing public Cauchy–Binet supplier is used directly over $\mathbb C$.
Its owner already attributes the physlib source to Alex Meiburg under Apache-2.0;
no supplier is transplanted or reproved. Mathlib supplies
`Matrix.charpoly_coeff_eq_sum_minors`,
`Polynomial.coeff_eq_esymm_roots_of_splits` and
`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`.
The accepted axiom closure is `propext`, `Classical.choice`, `Quot.sound`,
without `sorryAx` or an added axiom.

The retained audit source is
`Reg/D5/S3/Quantum/Matrix/MalkounJordanElementary.lean`.
Its source-family reconstruction, positive law, nonvacuity, sensitivity and
dependence proofs compile. The binding audit remains `declared_unresolved`:
`source.residual_requires_open`, IE-C050 `ClosedTruthReadout`, with no binding
certificate, under [#24980](https://github.com/the-omega-institute/trureturing/issues/24980).
In particular, the faithful `escapeFrom := some ℝ` does not meet the current
source validator's `fromObject.isNone` condition. The linked-issue exception in
CLAUDE.md §3.9 permits delivery of the mathematics with this unfinished audit;
it supplies neither `declared_validated` nor a missing certificate.

## Triage

Tier 1: an explicit recent question published in 2026, with a complete symbolic
proof from existing algebraic and spectral identities. The admission basis is
`open-problem-resolution`, independently of its bind-only proof shape.
The utility kind is `none`: no declaration delivers bounded enumeration, a
checker, a numerical reduction or a finite certified instance. There is no
corresponding theory volume or digestion atom.

### What the settlement shows

**Proved** by `D5/S3/Quantum/Matrix/MalkounJordanElementary.result`: the complete
first two-matrix assertion holds for all source dimensions, matrices and degrees.
The decisive mechanism is the equal-Gram stacked-column construction and the
nonnegative squared gap between the corresponding minors, followed by the
spectral principal-minor identity. This proves the trace and determinant cases
as members of the same full range; it does not assume the Jordan product is
positive semidefinite.

**Proved helper scope** in
`D5/S3/Quantum/Matrix/MalkounJordanElementary.principal_det_le` and
`D5/S3/Quantum/Matrix/MalkounJordanElementary.spectral_minors`:
the principal-minor comparison needs only Hermiticity of $X,Y$, and the spectral
identity needs only Hermiticity of its matrix and $k\leq n$. In `result`, positive
semidefiniteness is used only to obtain Hermiticity. The public assertion retains
the exact original hypotheses; no generalized companion theorem is delivered.

**Algebraic sharpness observation, not an additional frozen theorem:** setting
$X=Y$ makes $L=R=2X^2$, so every displayed symmetric-function comparison is an
equality. Thus a uniformly strict conclusion would fail on this source family.
**Open here:** a complete classification of equality, and a separately retained
generalization of the public assertion beyond its positive-semidefinite source
domain. These are not claimed as new formal results of this unit.

**Open and excluded:** the later general promotion question lacks a specified
promotion rule and is not answered by the proof of this one polynomial pair.
The source's motivating determinant problem is also not settled here. The first
question now has an affirmative formal answer; no other source theorem or
conditional implication is asserted to change, and the proposed
Kronecker/immanant route is not validated by this different argument.

## ASSUMED-UNVERIFIED

The source revision and finite source-page status were read directly. The wider
literature checks supplied by issue #24963 and the approved input were not
independently reproduced. No exhaustive novelty, worldwide priority or absence
of a proof elsewhere is claimed. The source's linked motivating determinant
problem and general promotion question were not investigated for settlement.

The equality observation is an explicit algebraic argument, not an added Lean
statement; equality classification and a new public generalization are outside
this formal result. The Reg binding certificate remains absent under #24980.
No successful kernel or axiom check is represented as a completed binding audit.
