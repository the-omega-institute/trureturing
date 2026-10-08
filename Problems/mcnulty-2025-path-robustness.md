---
slug: mcnulty-2025-path-robustness
bibkey: mcnulty2025pathrobustness
doi: null
url: https://arxiv.org/abs/2511.15954
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.result
---

# McNulty's path-robustness conjecture

## Problem

Daniel McNulty, “A Graph-Theoretic Approach to Quantum Measurement Incompatibility”,
arXiv:2511.15954v1, Conjecture 1, p. 9:

> For all $n\geq 1$, paths satisfy
> $\eta(P_{2n})=\eta(P_{2n+1})=\eta(C_{2n+2})=
> \frac{2}{2n+2}\csc\bigl(\frac{\pi}{2n+2}\bigr)$.

The source's Definition 1 and Eqs. (8)–(10) fix the observables and the
visibility convention. MCN-1 in #13934 fixes the strong statement for every
finite-dimensional realization: Hermitian involutions on $\mathbb C^d$,
$d\geq1$, anticommutation on distinct adjacent vertices, and commutation
on distinct nonadjacent vertices. No irreducibility is assumed.

## Motivation

The source's Corollary 7 supplies lower bounds for the two path sizes and
numerical semidefinite-programming evidence motivates their sharpness.
Corollary 6 supplies the even-cycle value. The settlement identifies one
greatest feasible visibility for all three families and every realization.

## Gap

The path upper bound must be sharp uniformly in $n$ and in the realization.
The cycle parent must respect the central loop sector of a reducible
realization; a fixed antiperiodic twist alone does not suffice.

## Route

Set $M=2n+2$ and $\theta=\pi/M$. The upper bound uses sine-product weights,
a Majorana extension, a shifted Fourier positive quadratic decomposition,
and the signed-marginal trace identity. The lower bound uses a Fourier
vacuum and its Clifford average to obtain a positive normalized Boolean
parent, then compresses it to the original Hilbert space. Even-cycle
outcomes are relabelled within the central involution's two sectors.

The noisy observable remains
$A_v^\eta=\eta A_v+\operatorname{tr}(A_v)d^{-1}(1-\eta)I$.
Trace vanishing is proved from the realization relations. Joint measurability
requires both signed marginals of a Boolean-indexed positive parent.

## Falsifier

A lawful realization of one of the three graphs with no parent at the stated
visibility, or with a feasible greater visibility, contradicts `result` in
its formal system. A mismatch between the source definitions and the literal
realization, noise, parent or greatest-element predicates invalidates fidelity.
A prior publication settling this conjecture changes the bounded literature
assessment in #13934.

## Evidence

`McNultyPathRobustness.claim` quantifies over every $n\geq1$, dimension and
lawful realization for the three families and states `IsGreatest` of
$\{\eta\in[0,1]:\mathrm{JM}(A,\eta)\}$ at the claimed threshold.
`McNultyPathRobustness.result : claim` proves that statement. The axiom closure
of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The Library note `mcnulty2025pathrobustness` locates the source definitions,
robustness formula and conjecture; the bounded source and literature checks
are recorded in #13934.

## Triage

Tier 1, settlement Proved for MCN-1 under the literal conventions of #13934.

### What the settlement shows

- **Proved — kernel-checked declaration:**
  `CliffordPathRealizations.arbitrary_path_majorana_extension` extends every
  lawful path realization by an ancilla to Hermitian, involutory, pairwise
  anticommuting Majoranas with exact bond equations.
- **Proved — kernel-checked declaration:**
  `ShiftedFourierOperatorCertificate.path_dual_operator_certificate` makes
  $\cot(\theta)I-H(A,w,a)$ positive semidefinite for every $P_{2n}$
  realization and outcome. The shifted Fourier split and sine-product weights
  give the sharp upper bound through the signed-marginal trace identity.
- **Proved — kernel-checked declarations:**
  `FourierCliffordVacuum.fourierVacuum_properties` and
  `CliffordBondParents.cycle_majorana_parent` give the Fourier-vacuum Clifford
  average and a positive normalized Boolean parent with every antiperiodic
  bond marginal at the threshold.
- **Proved — kernel-checked `McNultyPathRobustness.result`:**
  $P_{2n+1}$ uses $2n+2$ Majoranas after one ancilla extension.
  $P_{2n}$ first gives $2n+1$ Majoranas and gains one through
  `paddedMajoranas` and a second ancilla. $C_{2n+2}$ uses $2n+2$ Majoranas
  after the central-loop normalization in
  `CentralCycleRealizations.cycle_majorana_extension`. Compression gives
  parents on the original dimension, and central-sector outcome relabelling
  recovers the original cycle observables. The longer path and cycle upper
  bounds restrict their parents to the initial induced $P_{2n}$ subfamily.
  These are the precise relations yielding the common threshold.
- **Proved — paper argument and scratch kernel evidence cited in #13934:**
  the fixed-twist reduction fails for the $C_4$ realization $(X,Z,X,-Z)$.
  Its ordered loop product is $XZ X(-Z)=+I$, since $XZX=-Z$ and $Z^2=I$;
  the fixed antiperiodic Majorana bond product is $-I$. An isometric
  compression preserving these Hermitian involutions intertwines them, so
  preserves the loop product and cannot change its sign. The scratch theorem
  `McNultyProbe.route_step_four_fixed_twist_false` checks this obstruction;
  no standalone instance is retained. The general repair is kernel-checked
  by `CentralCycleRealizations.cycle_majorana_extension` and its consumed
  `central_relabel_parent`: normalize with the central loop involution,
  construct the parent in its sectors and undo the closing-outcome label.
  This is a method obstruction, not a counterexample to the conjecture.
- **Proved — paper deduction, not a new Lean theorem:**
  put $x_n=\pi/(2n+2)$. The threshold is
  $(2/\pi)(x_n/\sin x_n)$. Since $x_n\to0$ and
  $\sin x/x\to1$, it tends to $2/\pi$ as $n\to\infty$.
- **Open — neighbouring questions:** sharp parents and certificates for
  other trees, odd cycles and general anticommutation graphs, and whether a
  precisely specified Majorana-mode count alone determines their threshold.
  In particular, the comparison of $\eta(C_{2n+1})$ with
  $\eta(P_{2n-1})$, extensions to line graphs, and sharpness of the source's
  Theorem 1 Lovász bound outside the three settled families remain open here.
- **Proved — kernel result compared with the source:** Corollary 7's lower
  bounds for both path sizes are sharp. The settlement also recovers
  Corollary 6's even-cycle value for every lawful realization. Dependence on
  Conjecture 1 for these equalities is discharged; no further source result
  about other graphs is asserted.

## ASSUMED-UNVERIFIED

The literature assessment is not-found-in-searched-scope in #13934; worldwide
absence of a prior proof and completeness of the citation indexes are
unverified. The asymptotic limit and explicit loop obstruction above are
paper arguments; they are not additional delivered Lean declarations.
The three graph families remain the exact scope of the settling theorem.

Information-escape registration is paused under CLAUDE.md §3.9.
