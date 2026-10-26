---
slug: lin-2017-majorization-conjecture-4-3
bibkey: lin2017dtimajorization
doi: 10.1142/S0219199716500449
url: https://arxiv.org/abs/1604.04141v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.result
---

# Lin's matrix majorization conjecture fails at exponent four

## Problem

Lin, *On a determinantal inequality arising from diffusion tensor imaging*,
Communications in Contemporary Mathematics 19 (2017), Conjecture 4.3, asks
whether for positive semidefinite matrices $A,B$ and every real $p>0$,

$$
\lambda(A^2+|BA|^p) \succ \lambda(A^2+|AB|^p).
$$

Here $|X|=(X^*X)^{1/2}$ and the eigenvalue lists are in descending order.
The Lean claim uses the literal carrier `Matrix (Fin n) (Fin n) ℂ`, the
continuous functional calculus expression for $|X|^p$, and the source's
prefix-sum definition of majorization.

### Statement echo

The source clause is “Let A and B be n × n positive semidefinite matrices.
Then λ(A² + |BA|^p) ≻ λ(A² + |AB|^p) for all p > 0.” The declaration
`D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.claim` binds $n,A,B,p$,
the two positive-semidefinite hypotheses, and the two ordered eigenvalue lists
with exactly those operations.

## Motivation

The source presents the majorization statement as a strengthening of the
determinantal question and cites an integer-power comparison. A certified
counterexample separates the majorization claim from those surviving
determinant results.

## Gap

The source leaves Conjecture 4.3 as a universal statement. The settlement
supplies one exact positive-semidefinite pair in dimension three and one exact
positive exponent, enough to refute that universal quantification.

## Route

Take

$$
A=\operatorname{diag}(3,1,1/2),\qquad
B=\begin{pmatrix}1/2&1/4&3/4\\1/4&3/4&0\\3/4&0&5/2\end{pmatrix},
\qquad p=4.
$$

The Lean result proves $B\succeq0$ by an exact triangular factorization and
proves $L-(7/5)I\succeq0$ for $L=A^2+|BA|^4$. The exact vector
$(0,-1,19/64)$ has negative quadratic form for $R-(7/5)I$, where
$R=A^2+|AB|^4$. Thus the smallest eigenvalue of $L$ is at least $7/5$ while
one eigenvalue of $R$ is below $7/5$. Equal traces and the two-entry prefix
condition contradict majorization.

## Falsifier

The refutation depends on the source's positive-semidefinite hypotheses,
complex-matrix absolute value, descending eigenvalue lists, and $p=4$. A
different norm, ordering convention, or matrix carrier is a different claim.

## Evidence

The kernel-checked declaration is
`D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.result`, with the axiom
closure of every public declaration contained in
`{propext, Classical.choice, Quot.sound}`. The Scribe result node carries an
`OpenProblemResolutionClaim` with resolution `Refuted`.

The numerical check is recorded in the experiments repository at
`https://github.com/the-omega-institute/trureturing-experiments/tree/57862c24fae9058c2deba3b5b3272b0a7c5611d0/docs/reports/lin-2017-conjecture-4-3`.
The pinned `check.py` exists at that commit, has SHA-256
`5d3d2268b13a1e04f409852514c48ed52b4de19f9dae519c9f44415a00e5890a`, and
returned exit 0 with `RESULT PASS`. Its exact certificate checks positivity,
the trace equality, the two threshold sign certificates, and the resulting
two-prefix violation; its floating-point exponent scan tests
$p\in\{1/4,1/2,\ldots,12\}$.

## Triage

The settlement is `Refuted` for issue #18700. The public result is the
designated refutation result (`basis=refutes`) and is exempt from four-slot
escape registration (CLAUDE.md §3.9).

### What the settlement shows

- **Proved in the module:** the exact dimension-three, exponent-four witness
  satisfies the positive-semidefinite hypotheses and violates majorization at
  the two-entry prefix. The failure mechanism is the opposite ordering of the
  smallest eigenvalues at threshold $7/5$.
- **Proved in the source's neighbouring result:** the determinant inequalities
  survive. Ghabries–Abbas–Mourad, Corollary 3.1, proves the determinant form
  for Hermitian matrices and $p\ge0$; this settlement refutes only the
  majorization strengthening.
- **Computed:** for this pair, the pinned experiment checks the grid
  $p\in\{1/4,1/2,\ldots,12\}$ and finds violation exactly for
  $3\le p\le33/4$; it also finds the claim satisfied at $p=2$. This is a
  finite floating-point computation, not a uniform theorem.
- **Computed:** on this pair the largest-eigenvalue comparison at $p=4$ has
  the expected direction; the failure is at the two-largest-eigenvalue sum.
- **Open:** whether the conjecture holds for $0<p<2$.
- **Open:** whether it fails for every $p>2$.
- **Open:** whether it holds in dimension $n=2$.
- **Proved in the cited mechanism:** the Lin–Wolkowicz integer-power result
  gives the comparison at $p=2$ for Hermitian $A,B$; its expression uses
  $(AB)^k(BA)^k$, which is different from $|BA|^{2k}$ for $k\ge2$.
- **Open:** no determinant inequality is refuted by this result; extending
  the exact majorization refutation beyond the displayed witness is outside
  the module's statement.

## ASSUMED-UNVERIFIED

The literature screen and its completeness are `ASSUMED-UNVERIFIED`.
The source, the Lin–Wolkowicz preprint, the determinant follow-ups, and the
listed citing-work titles were screened; the remaining citing works,
including Lemos–Soares (DOI 10.1016/j.laa.2018.02.015), were not independently
read for this formalization.
