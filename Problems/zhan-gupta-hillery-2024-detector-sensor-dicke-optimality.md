---
slug: zhan-gupta-hillery-2024-detector-sensor-dicke-optimality
bibkey: zhanguptahillery2024detectorsensor
doi: 10.1145/3655028
url: https://arxiv.org/abs/2306.17401v6
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.result
---

# Dicke optimality for detector-sensor identification

## Problem

C. Zhan, H. Gupta and M. Hillery, *Optimizing Initial State of Detector
Sensors in Quantum Sensor Networks*, arXiv:2306.17401v6, ACM Transactions
on Quantum Computing 5(2), Article 10, DOI 10.1145/3655028, Section 5,
Conjecture 1, asks whether a state with uniform coefficient-squares on
a minimizing weight partition is an optimal initial state. The
[Library note](../Library/QuantumBounds/zhanguptahillery2024detectorsensor.md)
contains the source quotation and locators.

There are $n\ge3$ qubit sensors, one firing event with equal priors
$1/n$, and a unitary with eigenvalues $e^{i\theta}$ and $e^{-i\theta}$.
Write $q=\lceil n/2\rceil$ and
$T=\tfrac12\arccos(-(q-1)/q)$. The conjecture concerns
$\theta\in(0,T]\cup[\pi-T,\pi)$.
For a tensor eigenbasis word $x$, its weight is the number of plus
eigenvectors. For two distinct sensors, $R_k$ and $L_k$ count weight-$k$
words whose selected bits agree or differ. Every minimizing $l$ of
$(R_k+\cos(2\theta)L_k)/(R_k+L_k)$, over $0\le k\le n$, is allowed.
The proposed state has coefficient-squares $1/\binom nl$ on weight $l$
and zero elsewhere, with arbitrary phases.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Qubit tensor eigenbasis | `Fin n → Bool`, true for the plus eigenvector | A coordinate representation of all pure input states |
| One firing event at sensor $i$ | `fire` | The local eigenphase multiplies each coefficient |
| Equal priors and global POVM | `isoSuccess`; the frozen `TriangleIndependentSourceNoise.LocalPOVM` | Positive semidefinite effects sum to the identity; no locality restriction |
| $n\ge3$ | `n`, `hn` in `claim` | Includes every permitted sensor number |
| Both angle intervals and threshold endpoints | `T`, the disjunction in `claim` | Radians replace degrees without changing the intervals |
| Every minimizing partition | `l`, `l ≤ n`, `IsMinOn` on `Set.Iic n` | The selected distinct sensor indices have values zero and one |
| Uniform coefficient-squares, arbitrary phases | `φ`, the pointwise `Complex.normSq` hypothesis | The weight-cardinality expression is inlined literally |
| Any normalized competing pure state | `ψ`, the sum of norm-squares equals one | No symmetry assumption on the competitor |
| Optimal initial state | For every `M`, an attaining `M'` with the success comparison | `result : claim` proves the universal comparison |

The natural division in `T` gives $\lceil n/2\rceil$. Fin-index proof
fields witness index bounds and impose no additional hypothesis.
The existing `LocalPOVM` supplies the stated POVM definition directly.
The weight expression is inlined rather than duplicated beside the
existing I-level `DynamicCoolingParallelTieUniqueness` definition;
the settling module has generality G. No source clause is dropped.

## Motivation

The settlement supplies a globally optimal pure probe on the stated
angle range, including arbitrary coefficient phases. It removes the
need to assume probe symmetry or to prove the source's stronger
strict-averaging Conjecture 2 before concluding Conjecture 1.

## Gap

Issue [#16668](https://github.com/the-omega-institute/trureturing/issues/16668)
preregisters the published named conjecture, the complete quantifiers,
the first-tier classification and the source and literature screen.
No prior settlement was located in that screen. Literature completeness
is ASSUMED-UNVERIFIED; the bounded screen does not prove publication
priority or exhaustive absence of another proof.

## Route

The settling module is
`D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.lean`.
Its private helpers reduce a measurement to a feasible Gram
decomposition, average over sensor permutations, bound the resulting
constant-overlap objective and construct an attaining measurement.
The public surface consists of `fire`, `isoSuccess`, `rCount`, `lCount`,
`T`, `claim` and the single settling theorem `result`.

The proof uses the published frozen owner theorems
`AntidistinguishabilityGram.hermitian_projection_complement_psd`,
`AntidistinguishabilityGram.matrix_penrose_exists` and
`AntidistinguishabilityGram.psd_summand_projection` in
`gram_decomposition_to_povm`; the complementary-projection theorem also
supplies `Q_psd`. The trace bound uses
`RHLinalg.trace_mul_nonneg_of_posSemidef`, owned by `RankTrace`.
The weight-class count uses Mathlib's `Finset.card_powersetCard`
through a word-to-finset equivalence. Positive-semidefinite
Cauchy–Schwarz uses Mathlib's matrix-induced inner-product structures
and `inner_mul_inner_self_le`.

The admission basis is `open-problem-resolution (#16668; Proved)`.
The declaration classification is bind-only after expansion to frozen
owners and pinned Mathlib; no escape witness is claimed. Every private
helper has a named consumer. Utility is `none`: there is no fixed
numerical certificate in the settling module.
This is deposit-uncovered, with no atom or coverage edge. The Gram
owner is re-pinned by the canonical `ledger-align --selector` writer.

## Falsifier

An admissible angle, a minimizing partition, a proposed state, a
normalized competing state and a global POVM whose success exceeds
every measurement on the proposed state would contradict `claim`.
The theorem quantifies over all such choices; a finite numerical
search alone does not prove the universal statement.

## Evidence

`D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.result`
has type `claim`. The axiom closure of every public declaration is
contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The Scribe carries one Proved `OpenProblemResolutionClaim` on `result`.

The four-slot escape audit is unfinished under
[#16824](https://github.com/the-omega-institute/trureturing/issues/16824).
Its targets are `result` and the three published Gram owner theorems
listed in Route. No Reg mirror is retained and no declared_validated
registration is claimed. Exact source reconstruction, variation,
sensitivity and actual observational-dependence evidence remain missing.

The independent numerical evidence is the
[pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/e457ba7b5c2c90bcfac1477711a5290e58f6ccd7/docs/reports/zhan-gupta-hillery-2024-global-dicke-optimality).
At that revision, run
`python3 docs/reports/zhan-gupta-hillery-2024-global-dicke-optimality/check.py`
from the experiments repository. The implementation seat reran those
exact bytes as `python3 /tmp/op-zgh/check.py`, exit 0, `ALL_OK`.
The script SHA-256 is
`6801a065b0f1dc2b867eb1280fb4b2ea30729e927c4d08e9d94c4cfb901d445a`.
The tested scope is $n\in\{3,4,5\}$ and
$\theta/T\in\{0.25,0.5,0.8,1\}$, with twelve random competitors per
setting. The numerical readings are stated in Triage; no experiment
program or data is embedded here.

## Triage

### What the settlement shows

**Mechanism — kernel-checked.** `N_psd`, `sum_N` and `isoSuccess_gram`
give the feasible Gram decomposition and its objective.
`avgN_psd`, `sum_avgN` and `avgN_objective` prove that relabeling
averages preserve feasibility and the objective.
`average_gram_overlap` identifies the averaged constraint as
$(1-\bar c)I+\bar cJ$, where $J$ is the all-ones matrix.
`moment_bounds` and `overlap_bounds` give $\bar c\ge c_*$, with
$c_*=1-4\lfloor n^2/4\rfloor\sin^2\theta/(n(n-1))$.
`constant_overlap_certificate` supplies the square-root certificate
$H=\sqrt aP+\sqrt bQ$, where $P=J/n$, $Q=I-P$,
$a=1+(n-1)\bar c$ and $b=1-\bar c$.
`d_antitone` and `global_success_upper_bound` give the bound
$d(\bar c)^2\le d(c_*)^2$, where
$d(c)=(\sqrt{1+(n-1)c}+(n-1)\sqrt{1-c})/n$.
`ratio_minimizer_balanced`, `dicke_gram` and `dicke_attainment`
identify the minimizing-weight Gram matrix and an attaining
square-root measurement. These are consumed private theorems in the
settling module; `result` is their public universal conclusion.

**Concavity and permutation invariance — proved in prose.** For a positive
semidefinite Gram matrix $G$, let $F(G)$ be the supremum of
$n^{-1}\sum_i(N_i)_{ii}$ over positive semidefinite families with
$\sum_iN_i=G$. For $n\ge3$ this feasible set is nonempty by assigning
$G$ to one outcome and zero to the others. Every objective is between
zero and $\operatorname{tr}(G)/n$, since $0\preceq N_i\preceq G$. For $0\le t\le1$, feasible families for $G_1$ and $G_2$
give the feasible family $tN_i+(1-t)N'_i$ for $tG_1+(1-t)G_2$,
with the corresponding convex combination of objectives. Taking suprema
gives $F(tG_1+(1-t)G_2)\ge tF(G_1)+(1-t)F(G_2)$.
Simultaneously permuting the indices and outcome labels is an invertible
map of feasible families that preserves the objective, so $F$ is
permutation invariant. The expression in `G_phase` is affine in the
coefficient-squares. This explains the averaging mechanism; no separate
Lean declaration of the abstract function $F$ is retained.

**Pure permutation-symmetric optimum — proved in prose from the
kernel-checked conclusion.** The finite nonempty set of weights
$0,\ldots,n$ has a ratio minimizer. Choose coefficient
$1/\sqrt{\binom nl}$ on each weight-$l$ word and zero elsewhere.
There are $\binom nl$ such words, so the state is normalized and has
the prescribed coefficient-squares. Permutations preserve weight
and the coefficients, hence preserve this pure state. Applying
`result` proves its optimality on the stated range. This consequence
is not a separate retained Lean theorem.

**Both middle weights for odd $n$ — proved in prose from the
kernel-checked conclusion.** The count identity in `ratio_formula`
expresses the ratio as
$1-4k(n-k)\sin^2\theta/(n(n-1))$.
For $n=2m+1$, the integer product $k(n-k)$ is maximized at both
$k=m$ and $k=m+1$, with value $m(m+1)=\lfloor n^2/4\rfloor$:
$(k-m)(k-m-1)\ge0$ for every integer $k$ proves the upper bound.
Thus both weights minimize the ratio, and `result` gives optimality
for both. Their Gram matrix is the same by `dicke_gram`, so
`dicke_attainment` gives the same success $d(c_*)^2$.
No separate odd-weight public theorem is retained.

**Error-position identification challenge — proved in prose for the
same range and model.** Skotiniotis–Llorens–Hotz–Calsamiglia–Muñoz-Tapia,
arXiv:1808.02729, Physical Review Research 6, 033329, Conclusions,
asks whether pure permutation-symmetric probes suffice. A common
unitary change of qubit basis diagonalizes the one-site unitary;
its tensor power conjugates every global effect and transforms every
probe, preserving normalization and Born probabilities. In this
eigenbasis, its single-position, equal-prior pure-probe model is
exactly `fire` and `isoSuccess`. The equal-phase construction above
therefore answers that challenge for $n\ge3$ on the stated two
intervals. This model correspondence and interpretation are proved
in prose, not a separate Lean theorem. The full-angle combination,
ancillary-probe reduction and mixed-probe reduction remain open here.

**Source consequences — proved conclusion; open stronger premise.**
The settlement establishes Conjecture 1 directly, supplying the
optimality conclusion of the source's Theorem 3 without its
strict-averaging Conjecture 2. It does not prove Conjecture 2 or
change the hypotheses or conclusions of the source's other results.

**Extensions — open.** Unequal priors, multiple simultaneous firing
events and noisy channels are outside `claim` and are not settled
by this module.

**Literature — bounded screen, completeness ASSUMED-UNVERIFIED.**
The source and literature checks in #16668 are orchestrator-verified.
The supplementary readings are reported by codex-cli research seat
`ccb43553212229ba9d007bfa`: Zhan's thesis, ProQuest 30991761,
Chapter 5, leaves the conjectures as future work; Chin–Chuang,
Physical Review A 111, 052447, DOI 10.1103/PhysRevA.111.052447,
establishes symmetric zero-error sensor existence and does not
settle minimum-error initial-probe optimality for nonorthogonal
outputs. The screen includes Semantic Scholar citations of both
source papers, relevant full texts and titles/abstracts of other
citing works. Not every citing full text was inspected. No prior
settlement was located in that scope.

**Experiment — computed, finite scope.** For the twelve tested
$(n,\theta/T)$ settings, the phase-independence error is at most
$3.3\times10^{-16}$. The independent iterative Dicke optimum
agrees with $d(c_*)^2$ at displayed precision; at $n=4$ and
$\theta=T/2$ both are $0.75$. The twelve random competitors per
setting stay below that bound. The certificate's smallest
computed eigenvalue is at least $-8.5\times10^{-17}$.
These floating-point checks are not proofs of exact positive
semidefiniteness, certified optima or any untested extension.
The experiment entry in Evidence supplies the command, revision,
exit code and script SHA-256.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not established.
Supplementary literature readings are research-seat reports.
Four-slot escape registration is unfinished under #16824.
The full-angle combination, ancillary and mixed probes, unequal
priors, multiple firing events and noisy channels are not settled.
