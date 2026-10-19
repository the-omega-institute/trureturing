---
slug: han-wang-yu-gluing-spectrum
bibkey: hanwangyu2025gluing
doi: 10.3390/math13132080
url: https://www.mdpi.com/2227-7390/13/13/2080
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.result
---

# The Han–Wang–Yu gluing spectral hull conjecture is false

## Problem

X. B. Han, S. Wang and C. Yu, *PageRank of Gluing Networks and Corresponding
Markov Chains*, Mathematics 13 (2025), 2080, Conjecture 1, §4.3, page 17:

> Glue Markov chains M_i = (S_i, A_i) to a Markov chain M = (S, A), then all the eigenvalues of A lie in the convex hull of the eigenvalues of all A_i on the complex plane.

The gluing is Definition 8, page 10. The
[Library note](../Library/Eigenstructure/hanwangyu2025gluing.md) records its four
entrywise cases. Preregistration: [#19143](https://github.com/the-omega-institute/trureturing/issues/19143).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finitely many Markov chains with selected states | `RootedChain`; families indexed by `Fin k` | States are `Fin (n + 1)`, selected state 0; the stochastic field is `Matrix.colStochastic` |
| Transition probability from $w$ to $v$ | Matrix entry `A v w` | Column convention of Definition 8 |
| Common root and otherwise disjoint states | `Option (Σ i, Fin (M i).n)` | `none` is the common root, `some ⟨i,v⟩` corresponds to `v.succ` |
| Definition 8's four transition cases | `glue` | Root-root weighted sum, private-root weighted entry, root-private unchanged entry, same-chain unchanged entry and cross-chain zero |
| $0<\theta_i<1$, $\sum_i\theta_i=1$ | Both antecedents of `claim` | No weight hypothesis is dropped |
| All eigenvalues lie in the input spectral convex hull on the complex plane | `claim` | Complex `spectrum` after entrywise `algebraMap ℝ ℂ`, with `convexHull ℝ` in $\mathbb C$ |
| Refutation | `result : ¬ claim` | Two identical 3-state chains give an admissible 5-state counterexample |

The state and spectrum expressions are expanded directly rather than introduced
as forwarding definitions. Using labelled finite state sets loses no
counterexample: these labelled matrices are themselves instances of the source's
finite chains. The finite cardinality encoding and column convention introduce
no additional hypothesis into the displayed conjecture.

## Motivation

Identifying the roots leaves private-block modes whose eigenvalues need not be
input eigenvalues. Opposite private components can cancel at the root while
retaining a root-deleted block eigenvalue.

## Gap

The literature screen in #19143 reports the source, its citing works and fifteen
later works of its authors, classical coalescence and lumpability references,
MathDB, `google-deepmind/formal-conjectures`, QIQC, repository issues and the
published problem register. No settlement was found in that searched scope.
Completeness is `ASSUMED-UNVERIFIED`. The source and literature checks are
orchestrator-reported; they are distinct from the kernel proof below.

## Route

Take two identical copies, rooted at 0, of

$$
B=\frac1{54}\begin{pmatrix}43&9&2\\2&36&16\\9&9&36\end{pmatrix},
\qquad \theta=(1/2,1/2).
$$

The private helper `B_stochastic` certifies nonnegative entries and unit column
sums. The helper `glued_eigenvalue` certifies the nonzero vector
$(0,-4,3,4,-3)$ with glued eigenvalue $4/9$. The helper `input_halfplane` uses

$$
\det(\mu I-B)=(\mu-1)(\mu-17/27)(\mu-1/2)
$$

to put the input spectrum in $\{z\in\mathbb C:1/2\leq\operatorname{Re}z\}$.
The proof of `result` uses `convexHull_min` and `convex_halfSpace_re_ge` to put
the input spectral hull in the same half-plane, excluding $4/9$.
All imports are pinned Mathlib; there is no D5 proof prerequisite.

## Falsifier

A discrepancy in Definition 8's root-column weights or column convention, a
nonstochastic input, an incorrect eigenpair, or failure of the input half-plane
bound would defeat this witness. The Lean declaration retains all strict weight
bounds and their unit sum, and proves the literal negation of `claim`.

## Evidence

The module is `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.lean`,
under the namespace `D5.S3.Quantum.Matrix.HanWangYuGluingSpectrumRefutation`.
Its only public theorem is `result`; its three theorem helpers are private and
consumed. Every theorem has `proof_shape: bind-only`, with
`admission_basis: open-problem-resolution (#19143; Refuted)` and certified-instance
utility refuting `claim`. No strict escape witness is asserted.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/10affd8b6d1c88d5f55af61de92721df944c2ecd/docs/reports/han-wang-yu-2025-gluing-spectral-hull).
Command, from that directory: `python3 check.py`; exit code $0$, result PASS.
The script's SHA-256 is
`909c9d85d9a165992829444f84a0c8818f58f6757476bb83accbb66747d9bdf6`.
The command uses the pinned script bytes.

The six seed cases have $k\in\{2,3,4\}$, each with uniform weights, and with
nonuniform weights $(1/3,2/3)$, $(1/2,1/4,1/4)$ and
$(1/2,1/6,1/6,1/6)$ respectively. Exact rational arithmetic checks column
stochasticity and the eigenvector $(0,-4,3,4,-3,0,\ldots)$ at $4/9$;
floating point checks corroborate the seed input eigenvalues and that glued
eigenvalue. The script also checks the three stated seed determinant roots in
exact rational arithmetic. It does not compute a symbolic characteristic
polynomial for arbitrary $k$.

The nine family samples use
$r\in\{1/9,1/20,1/100\}$ and $\delta\in\{1/2,3/4,9/10\}$,
$h=2r+3r^2$, and

$$
B_{r,\delta}=\delta I+(1-\delta)
\begin{pmatrix}
1/3+h&1/3&1/3-h\\
1/3-h&1/3&1/3+h\\
1/3&1/3&1/3
\end{pmatrix}.
$$

For these samples, exact arithmetic checks strict positivity and column
stochasticity; the two-copy, equal-weight glued eigenvalue
$\delta-(1-\delta)r$ is checked numerically to tolerance $10^{-9}$, with
its strict inequality below $\delta$ checked exactly. The script does not
verify the general input spectral formula or a similarity decomposition.

## Triage

Tier 1: an explicit published conjecture. Settlement: **Refuted**. Settlement
kind: small case with family mechanism. Literature completeness:
`ASSUMED-UNVERIFIED`.

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| Conjecture 1 | Proved false, kernel-checked `result` | Two identical 3-state inputs, root 0 and weights $(1/2,1/2)$ |
| Failure mechanism | Kernel-checked `glued_eigenvalue` and `input_halfplane`, used by `result` | Zero root coordinate and opposite private blocks yield $4/9$; all input spectral real parts are at least $1/2$ |
| Six seed gluings | Computed by the pinned experiment above, exit 0 | Exactly the six stated $k$/weight choices; rational stochasticity and eigenpair checks |
| Nine family samples | Computed by the same experiment, exit 0 | Exactly the nine $(r,\delta)$ pairs and two equal-weight copies; glued eigenvalue check is numerical |
| General identical-copy similarity $G\sim B\oplus D^{\oplus(k-1)}$ and invariant-subspace description | Open; unformalized search-seat assertion in #19143 | All admissible weights and arbitrary $k\geq2$; no uniform theorem is claimed |
| General positive doubly stochastic family, input spectrum and hull separation | Open; unformalized beyond the tested properties above | $0<r\leq1/9$, $1/2\leq\delta<1$ and arbitrary $k\geq2$ |
| Reversible input chains as a sufficient condition for containment | Open; unformalized search-seat assertion in #19143 | A separate candidate, with irreducibility and reversible symmetrization to be checked |

The refutation isolates cancellation of private-block modes as the obstruction
to universal spectral-hull containment. The exact six seed checks extend the
observed obstruction to the stated finite choices; they do not prove the
uniform family or similarity assertions. Reversibility is the nearest proposed
surviving restriction, with no positive theorem claimed here.

The conclusion negates Conjecture 1. It does not negate the source's Theorem 2,
peripheral-eigenvalue statements, or Examples 1 and 2. An argument using
Conjecture 1 as a universal premise cannot retain that premise; determining
which additional hypotheses recover such arguments remains open.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`.
Rymkhanova et al. (2026), Schwenk (1974), Laffey–Šmigoc and
Belardo–Li Marzi–Simić (2010) were not accessed in the recorded literature screen.
General families, identical-copy similarity, invariant-subspace classification
and the reversible-chain containment assertion are not formalized here.
Numerical family eigenvalue checks are not kernel certificates.
