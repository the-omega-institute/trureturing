---
slug: guo-2023-partial-negativity-concavity
bibkey: guo2023partialnorm
doi: 10.1088/1367-2630/acf152
url: https://arxiv.org/abs/2212.06521v6
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.result
---

# The reduced function of the partial negativity is not concave

## Problem

Y. Guo, *Partial-Norm of Entanglement: Entanglement Monotones That are not
Monogamous*, New J. Phys. 25 (2023) 083047, arXiv:2212.06521v6, states:

> We conjecture that $\hat{h}$ is concave [Suppl].

For decreasing Schmidt coefficients $\lambda_1\ge\lambda_2\ge\cdots$,
the paper defines $\hat N(|\psi\rangle)=\lambda_1\lambda_2$ and the reduced
function $\hat h(\rho)=\sqrt{\delta_1\delta_2}$, where
$\delta_j=\lambda_j^2$. Its definition of concavity is

$$
h(t\rho+(1-t)\sigma)\ge t h(\rho)+(1-t)h(\sigma),\qquad 0\le t\le1.
$$

Issue [#14495](https://github.com/the-omega-institute/trureturing/issues/14495)
preregisters the reading over every finite dimension $d\ge2$ and all
positive semidefinite complex $d\times d$ matrices of trace one. The
later paper *Complete Genuine Multipartite Entanglement Monotone*,
arXiv:2301.00334v3, explicitly identifies $\delta_1,\delta_2$ as the two
largest eigenvalues of $\rho$ and repeats the conjecture in its table
footnote. Eigenvalues are counted with multiplicity; their positions are
chosen separately for each state, rather than tied to fixed eigenvectors.

## Motivation

The source's Proposition 1 states that an entanglement monotone's reduced
function is concave. The partial-negativity section assumes monotonicity
before deriving further statements. A failure of concavity therefore
removes a premise used for that interpretation in general dimension.
It does not, by itself, settle every separate statement about partial
negativity, its convex-roof extension, or monogamy.

## Gap

The primary TeX sources of arXiv:2212.06521v6 and arXiv:2301.00334v3 retain
the conjecture. The former's phrase "but it is not true for the higher
dimensional case" concerns strict concavity: its displayed pair attains
equality at the midpoint. It does not supply a violation of concavity.
Reference [Suppl] additionally asserts the midpoint inequality for
commuting states; the counterexample below has commuting diagonal states.

The arXiv metadata queries `all:"partial negativity" AND all:concave` and
`all:"partial-norm" AND all:entanglement` each return only 2212.06521v6.
Repository and pinned Mathlib searches do not identify a theorem settling
this conjecture. These are bounded search results, not worldwide priority
or absence claims. The standalone erratum with DOI
10.1016/j.rinp.2025.108408 remains unread; the read v3 of the later paper
still contains the conjecture. The later paper asserts concavity in its
prose, labels it a conjecture in the table, and explicitly assumes it
later; those passages supply no proof of the conjecture.

## Route

Set $d=3$, $t=1/2$ and

$$
\rho=\operatorname{diag}(1/2,1/3,1/6),\qquad
\sigma=\operatorname{diag}(1/2,1/6,1/3).
$$

Both matrices are positive semidefinite and have trace one. Their
characteristic polynomials are the products of their three diagonal
linear factors. Their decreasing eigenvalue lists are both
$(1/2,1/3,1/6)$, so $\hat h(\rho)=\hat h(\sigma)=\sqrt{1/6}$.
Their midpoint is $\operatorname{diag}(1/2,1/4,1/4)$ and has reduced
function $\sqrt{1/8}<\sqrt{1/6}$. This reverses the required inequality.

## Falsifier

The meaning "two largest eigenvalues" is essential. Fixing the same two
eigenvectors for both states changes the claim. The definition `hhat`
uses the real parts of characteristic roots sorted in decreasing order.
For Hermitian matrices these are the real eigenvalues with their
multiplicities, as identified by Mathlib's
`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`.
The default zero entries for lists shorter than two are irrelevant on
the claim's domain $d\ge2$.

## Evidence

The Lean source is
`D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.lean`.
Its sole public theorem `result : ¬ claim` is an unconditional negation
of the universal density-matrix concavity claim. Its four private helper
theorems identify the sorted diagonal spectrum, positivity, trace and
mixture, and each occurs on the proof path of `result`. The definitions
`hhat` and `claim` introduce no additional theorem or audit target.
The direct import is `Mathlib.Analysis.Matrix.Order`; there is no project
formal prerequisite, new axiom, `sorry` or `native_decide`.

The Blueprint describes the same definitions and negation. Statements
about publications, physical realizability or other entanglement
properties are source readings or manuscript arguments, not consequences
certified by the Lean theorem.

## Triage

Tier 1 external named conjecture, preregistered in #14495.
`proof_shape: bind-only` for `result` and all four consumed helpers;
`escape_witness: none`; `admission_basis: open-problem-resolution`.
The result's utility is `certified-instance` with basis `refutes` the
closed definition `claim`. The designated literal `result : ¬ claim`
is exempt from four-slot registration under CLAUDE.md §3.9; there are no
other public theorems or lemmas in the module.

### What the settlement shows

- **Proved by `result`:** concavity fails in the universal finite-dimensional
  claim. The proof supplies positive semidefinite trace-one qutrit states
  and the legal mixing parameter $1/2$, so failure does not depend on a
  non-Hermitian extension or an inadmissible matrix.
- **Proved inside `result` for the displayed states:** the two original
  sorted spectra give $\sqrt{1/6}$, while the midpoint gives $\sqrt{1/8}$.
  The second-largest value belongs to different basis vectors in the
  two states; mixing reduces it while preserving the largest value.
- **Manuscript argument, not a separate Lean theorem:** the states commute,
  so commutativity alone cannot repair the conjecture or [Suppl]'s
  assertion. This observation does not characterize the state families
  on which concavity survives.
- **Source-attested, not formalized here:** concavity for qubit states.
  The qutrit refutation does not contradict that restricted assertion.
- **Open here:** a complete characterization of state families on which
  $\hat h$ is concave, including a proposed restriction to diagonal
  states with a common decreasing order, and the exact consequences for
  the source's monotonicity and monogamy results. The source's conditional results
  require their actual hypotheses; this refutation does not certify or
  refute their remaining arguments.

## ASSUMED-UNVERIFIED

The literature search is not exhaustive. The standalone Results in
Physics erratum is not read: its publisher landing page supplies only a
redirect and the Firecrawl proxy is unavailable without authentication.
The full text of *Monogamy of k-entanglement*, Phys. Rev. A 110, 012405
(DOI 10.1103/PhysRevA.110.012405), is also unread: its PDF requires
authorization and the same proxy is unavailable.
The preregistration's other literature readings are attributed reports,
not independent checks made by this source. No worldwide novelty,
priority, physical preparation or measurement is certified. The kernel
checks the mathematical encoding; correspondence to the published
meaning is established by reading and independent fidelity review.
