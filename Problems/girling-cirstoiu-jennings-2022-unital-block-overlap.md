---
slug: girling-cirstoiu-jennings-2022-unital-block-overlap
bibkey: girlingcirstoiujennings2022unitarity
doi: 10.1103/PhysRevResearch.4.023041
url: https://arxiv.org/abs/2104.04352
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.result
---

# The unital-block overlap lower bound fails for qutrit channels

## Problem

M. Girling, C. Cîrstoiu and D. Jennings, *Estimation of correlations and
non-separability in quantum channels via unitarity benchmarking*,
arXiv:2104.04352v3, *Physical Review Research* 4, 023041 (2022),
Appendix C.5 after Lemma C.3, state:

> However, we conjecture a stronger result that for any two quantum channels E₁, E₂ that ⟨T₁, T₂⟩ ≥ −1.

They also state:

> Since it is not essential to our work we leave it as an open problem.

Section II.C chooses a Hilbert-Schmidt orthonormal operator basis with
$X_0=I/\sqrt d$. Its positive-index Liouville entries are
$T_{ij}=\operatorname{tr}(X_i^\dagger\Phi(X_j))$.
The overlap is $\operatorname{tr}(T_\Phi^\dagger T_\Psi)$.
The [Library note](../Library/QuantumChannels/girlingcirstoiujennings2022unitarity.md)
gives the literal source and locators.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Any two quantum channels | `claim` quantifies over `d`, `Phi`, `Psi`; both satisfy the frozen `CoPRelativeQuantumnessRefutation.IsCPTP` | Complete positivity and trace preservation on all complex matrices |
| Orthonormal operator basis | `IsLiouvilleBasis` | All $d^2$ inner products, and normalized identity at zero |
| Positive-index unital block | `unitalBlock`, restricted in `overlap` | Both index values are nonzero |
| Hilbert-Schmidt overlap | `overlap` | Sum of conjugate products; `claim` compares its real part |
| Lower bound $-1$ | `claim` | Universal implication, with all channel and basis hypotheses |
| Refutation | `result` | Negation of `claim`, using one Hermitian qutrit basis |

The natural dimension and proof `h0` encode a nonempty finite-dimensional
system. Defining entries at every index does not add zero-index terms to
the overlap. The real-part comparison agrees with the paper on Hermitian
operator bases. Quantifying over complex orthonormal bases adds no
restriction on the explicit Hermitian witness.

## Motivation

The two Kraus families $(E_{00},E_{01},E_{12})$ and
$(E_{10},E_{11},E_{02})$, with $E_{ij}$ a matrix unit, give the actions

$$\Phi(A)=\operatorname{diag}(A_{00}+A_{11},A_{22},0),\qquad
\Psi(A)=\operatorname{diag}(A_{22},A_{00}+A_{11},0).$$

They are completely positive and trace preserving. In the explicit
nine-element Hermitian operator basis, their traceless blocks have a
single nonzero entry, at row one and column two, with values
$4/(\sqrt2\sqrt6)$ and its negative. Their overlap is $-4/3<-1$.
Both channels map the identity to a nonidentity diagonal matrix, so this
witness lies outside the source's unital and qubit cases.

## Gap

Issue [#16416](https://github.com/the-omega-institute/trureturing/issues/16416)
preregisters the first-tier published conjecture, source conventions and
refutation. The bounded literature screen reported by codex-cli seat `f21ccc5b9d0ae2606e8b4bff` covers the source,
Girling's 2023 thesis, seven citing works and later author works including
arXiv:2303.02662, 2508.08188 and 2609.12146. No prior settlement was located
in that screen. The thesis restates the conjecture as open on page 62.
These are seat-reported literature readings; they establish no exhaustive
absence or publication-priority claim. The preregistration separately
records the orchestrator's direct source checks.

## Route

The module imports `CoPRelativeQuantumnessRefutation` and reuses its
frozen `IsCPTP` definition without an alias. Complete positivity follows
by applying `FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive`.
Trace preservation applies the public `FiniteKrausChannel.finite_kraus_quantum_channel` through its channel action and trace-preserving field after checking Kraus completeness. The private trace-preservation owner belongs to a module with 114 transitive D5 importers at repository revision `05b8ab543cfb52c4a7c6485f1b0a4db11fa858aa`; the public owner supplies the same implication without changing that module. The private
`basis_orthonormal` and `basis_identity` proofs establish the Liouville
basis; `block_phi`, `block_psi` and `overlap_eq` evaluate the overlap.
The final `result` applies the proposed bound to that common witness and
contradicts its exact value.

The public surface is four definitions and one theorem, `result`.
The square-root equalities use the published owners
`EmpiricalReflexiveSeparation.complex_sqrt_two_sq` and
`CStarSmaleHigherOrder.sqrt3_sq`. Their four-slot escape audits are
unfinished under [#16616](https://github.com/the-omega-institute/trureturing/issues/16616);
no completed registration is claimed.
The module has `admission_basis: open-problem-resolution (#16416; Refuted)`;
all theorem proofs are classified bind-only with their actual helper
consumers. Utility is `certified-instance` with `basis=refutes` targeting
`claim`. This is deposit-uncovered, without an atom or coverage edge.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Falsifier

A single pair of CPTP maps and a valid Liouville basis with overlap below
$-1$ refutes the universal claim. The qutrit construction checks both
maps, the same basis and the overlap on one realization. Neither a
numerical approximation nor the unformalized family argument is needed
for the Lean contradiction.

## Evidence

The settling declaration is
`D5.S3.QuantumChannels.UnitalBlockOverlapRefutation.result`.
Its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The Blueprint carries one Refuted `OpenProblemResolutionClaim` on this
settling declaration.

The independent experiment is
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d5f176f83d2ac5246c53acb177cb101dc98d3b6e/docs/reports/girling-cirstoiu-jennings-2022-unital-block-overlap).
At that revision, run `python3 docs/reports/girling-cirstoiu-jennings-2022-unital-block-overlap/check.py`
from the experiments repository. The implementation seat reran that exact
script: exit 0, `ALL_OK`; SHA-256
`6443b54308432c02cddff9a5f6f9ac2d4fec59d0e2f4bf63120905685f74c1b2`.
The direct floating-point orthonormal-basis computation at $d=3,4,5$
agrees with $-4/3,-2,-12/5$, respectively, within the script's $10^{-9}$
comparison tolerance. Exact rational checks at $d=2,\ldots,12$ give
$-2\lceil d/2\rceil\lfloor d/2\rfloor/d$, below $-1$ exactly for the tested
$d\ge3$. No numerical check of an unbounded dimension range is claimed.

## Triage

### What the settlement shows

**Mechanism — kernel-checked qutrit instance.** The private `phi_apply`
and `psi_apply` establish opposite coarse-grainings of the same inputs;
`phi_channel`, `psi_channel`, `basis_liouville` and `overlap_eq` establish
CPTP, the basis and overlap $-4/3$ at $d=3$. The public `result` refutes
`claim`. The general classical-channel identity below is a prose
argument, not a theorem asserted by this module.

**Classical-channel identity — proved in prose.** For column-stochastic
real matrices $P,Q$, let
$\Phi_P(A)=\sum_{i,j}P_{ij}A_{jj}E_{ii}$ and similarly for $Q$.
Off-diagonal operators map to zero. On diagonal vectors, the traceless
projection is $H=I-\mathbf1\mathbf1^T/d$. Trace preservation gives
$\mathbf1^TPH=0$, so the unital block is the restriction of $PH$ between
traceless diagonal subspaces. Cyclicity of trace and $H^2=H$ give

$$\langle T_P,T_Q\rangle
=\operatorname{tr}(H P^TQH)
=\operatorname{tr}(P^TQ)-\frac{(P\mathbf1)\cdot(Q\mathbf1)}{d}.$$

Opposite deterministic output assignments have disjoint column supports,
so the first term vanishes. Their row totals increase the subtracted term.
This identifies the failure mechanism: trace preservation permits large,
nonunital image-of-identity vectors.

**Family — computed in the stated finite range, not formalized.** Put
$a=\lceil d/2\rceil$ and $b=\lfloor d/2\rfloor$. The experiment checks the
formula and threshold at $d=2,\ldots,12$, and directly evaluates the
operator-basis overlap only at $d=3,4,5$. Its exact tested scope and script
identity are in Evidence.

**Family extension — proved in prose.** For every $d\ge3$, send the first
$a$ inputs to output zero and the other $b$ inputs to output one, and swap
the assignments for the second channel. Matrix-unit Kraus operators
prove complete positivity and their squared adjoints sum to the identity,
proving trace preservation. The row totals are $(a,b,0,\ldots)$ and
$(b,a,0,\ldots)$. The displayed classical identity therefore gives
$-2ab/d$. Since $2ab=\lfloor d^2/2\rfloor>d$ for every $d\ge3$, the bound
fails throughout that family. This argument is not kernel-checked here;
formalizing the dimension-uniform family is a follow-up candidate.

**Positive-definite-Choi perturbation — unverified.** The search seat
reports qutrit perturbed overlaps $-27/25$ and $-264427/250000$ with
positive-definite Choi matrices. Neither the orchestrator nor this
implementation seat checked those perturbations, and the pinned
experiment does not test them. They are not evidence for this settlement.

**What survives — source literature.** Lemma C.4 proves the lower bound
when one channel is unital, and for arbitrary qubit channels. The qutrit
witness satisfies neither restriction. Appendix C.5 uses Lemma C.3's
proved bound to obtain the separable-channel correlated-unitarity bound;
the paper explicitly says the conjectured improvement is not essential.
Its nonseparability criterion therefore does not require the conjecture.
These source results are not formalized in this delivery.

**Sharp lower bound — open.** The source's Lemma C.3 gives $-d$.
The family gives an upper bound $-2\lceil d/2\rceil\lfloor d/2\rfloor/d$
on the infimum over pairs of channels. Determining the exact infimum as
a function of $d$, or proving optimality of this family, remains open.
No necessity or classification theorem follows from one counterexample.

## ASSUMED-UNVERIFIED

Publication priority and completeness of the bounded literature screen
are unverified. The codex-cli literature readings and the search seat's
Choi perturbation are attributed above. Source fidelity and proof-shape
classification require semantic review; they are not inferred from a
constant-dependency count. The general family and classical identity
have prose proofs only; Lean checks the fixed qutrit instance.
