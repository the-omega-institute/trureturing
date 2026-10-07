---
slug: siddiqui-wang-2026-concealment-kernel-necessity
bibkey: siddiquiwang2026concealment
doi: 10.48550/arXiv.2607.11762
url: https://arxiv.org/abs/2607.11762v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.result
---

# Concealment-equivalent channels with different adjoint kernels

## Problem

M. A. Siddiqui and Z. Wang, *Operational Concealment of Measurement Incompatibility by Quantum
Channels: Rank Loss versus Contraction*, arXiv:2607.11762v2, Section III, prove that two channels with
a common output space and equal adjoint kernels conceal the same POVM pairs, and state:

> Whether equality of adjoint kernels is also necessary for concealment-equivalence remains open.

The definitions are quoted in [the literature note](../Library/QuantumChannels/siddiquiwang2026concealment.md).
- A pair of POVMs is *concealed* by a channel $\mathcal E$ relative to an input set $\mathcal T$ if
  compatible POVMs reproduce its statistics on every output $\mathcal E(\rho)$, $\rho\in\mathcal T$.
- The adjoint kernel is $\ker(\mathcal E^\dagger)$ on Hermitian operators.

Issue [#14233](https://github.com/the-omega-institute/trureturing/issues/14233) reads the affirmative
answer with the hypothesis in its strongest form. For all finite dimensions, all trace-preserving
Kraus channels $\mathcal E_1,\mathcal E_2$ with common input and output spaces, and every tomographically
complete $\mathcal T$: if the two channels conceal the same pairs for every pair of finite outcome
sets, then their adjoint kernels coincide.

## Motivation

The source shows that the adjoint kernel decides whether concealment is possible at all, and that
kernel equality is a sufficient invariant for the whole concealment set. A necessary-and-sufficient
answer would make the kernel a complete invariant of concealment-equivalence.

## Gap

Issue #14233 records the literature check before any Lean:
- arXiv lists v1 and v2, and the sentence stands in v2;
- arXiv searches find only the source;
- Semantic Scholar lists no citing work;
- Zenodo has no record.

`not-found-in-searched-scope`.

## Route

On $\mathbb C^2$ take the complete dephasing $D(A)=\operatorname{diag}(A_{00},A_{11})$ and the complete
depolarization $R(A)=\operatorname{Tr}(A)I/2$, and let $\mathcal T$ be all density matrices.
- **Both conceal every pair of POVMs, for all finite outcome sets.** For $D$, the diagonal parts of the
  effects are compatible, through the joint POVM of products of diagonal entries. For $R$, the trace
  multiples of $I/2$ are compatible, through the joint POVM of products of traces. Both reproduce
  every output statistic.
- **The kernels differ.** $R^\dagger(Z)=0$, while $D^\dagger(Z)=Z\ne0$.

## Falsifier

The refutation depends on the reading of concealment-equivalence as equality of the concealment sets
of two channels with common input and output spaces, as in the source's theorem. A different notion
(for example one restricted to incompatible pairs) would not change the answer, since both channels
conceal every pair.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.lean`.
- It has public `IsPOVM`, `Compatible`, `Concealed`, `TomographicallyComplete`, `AdjointKernel`,
  `claim` and `result : ¬ claim`.
- It reuses the frozen Kraus carrier `MatrixMap.of_kraus` and its transplanted dual `MatrixMap.dual`,
  the density predicate and the Hermitian space of the frozen quantum-channel modules, and the frozen
  dephasing channel of `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation`, whose
  `dephase_apply` and `pinching_kraus` are made public at their origin, and the frozen Pauli carrier
  `Pauli`/`pauliMatrix` of `D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence` for the
  depolarizing Kraus operators.
- The axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`. There is no
  `sorry`, no `native_decide` and no new axiom.

The module statement is `sha256:9773b9f136826c316e78f3ccfff398b112fcb6093dda26799ff4966ea4ea1254`,
the `result` statement `sha256:e7fb999e85afe613f8e15e9453d76265fd17396c7288166ee78261eeda0a54d8` and the
`claim` statement `sha256:3971ed2f6455f7a415446ea94a6c56e8ea7851e42d01f47e20b12103ae81e551`. The Freeze
event is `sha256:08263f215d6184737b059eba1b394d15439ea823b9649309966243efd476d295`. Its project-level
prerequisites are `PositiveFilterTransposeRefutation`, `StabilizerPairLocalUnitaryInequivalence` and
the re-pinned `CumulantRenyiDataProcessingRefutation` (Freeze event
`sha256:0f6f4fff2e03748a2cf4315cd065d1e5b08b1a0e399a4e6ea6ec0584353b73f0`).

## Triage

Tier 1 open question of a July 2026 paper, preregistered in issue #14233 before any Lean. `theorem`;
resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none | open-problem-resolution |

The private helpers (the diagonal joint POVM, and concealment by channels with diagonal or scalar
outputs, for arbitrary finite outcome types) lie on the proof path of `result`. Utility is
`kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the refutation shows

**Proved by `result`:** the affirmative answer fails in dimension $2$. Complete dephasing and complete
depolarization conceal exactly the same pairs (all of them) for every pair of finite outcome sets,
but their adjoint kernels differ: $Z$ lies in the kernel of $R^\dagger$ ($R^\dagger(Z)=0$) and not in the
kernel of $D^\dagger$ ($D^\dagger(Z)=Z\ne0$).

**Proved inside the proof, for general data:** a channel whose outputs are all diagonal, or all
multiples of the identity, conceals every pair of POVMs with arbitrary finite outcome sets.

**Computed, not formalized:** on the Pauli basis, $D^\dagger$ maps $I,X,Y,Z$ to $I,0,0,Z$ and $R^\dagger$ maps them to
$I,0,0,0$ (exact SymPy check, issue #14233). By linearity the complete kernels are
$\operatorname{span}_{\mathbb R}\{X,Y\}$ for $D^\dagger$ and $\operatorname{span}_{\mathbb R}\{X,Y,Z\}$ for $R^\dagger$.

**Argued, not formalized.**
- *Mechanism.* When every output of a channel commutes with a fixed basis, any measurement is
  simulated on the outputs by its diagonal part. Diagonal effects are always compatible, through the
  product joint POVM. Such a channel conceals everything, whatever its kernel, so the concealment
  set forgets which observable directions are hidden.
- *Family.* The same argument applies in every dimension $d$: any two channels whose outputs are
  diagonal conceal all pairs. Their kernels all contain the off-diagonal Hermitian operators and may
  differ on the diagonal part. On $\mathbb C^d$ the kernel of the complete dephasing has codimension $d$,
  and that of the complete depolarization has codimension $1$.
- *What survives.* The counterexample uses channels whose concealment set is everything. Whether the
  kernel is a complete invariant among channels with a noncommutative output range, or whether the
  concealment sets determine the kernel up to the commutative part of the output algebra, is not
  addressed.

**Open.** The two refinements just stated are not settled here.

**Effect on the paper.** Kernel equality is sufficient but not necessary for concealment-equivalence.
The kernel is therefore not a complete invariant of the concealment sets. The paper's other results
(the existence criterion and kernel monotonicity) are unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent answer.
