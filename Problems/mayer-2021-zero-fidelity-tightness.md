---
slug: mayer-2021-zero-fidelity-tightness
bibkey: mayer2021zerofidelity
doi: 10.48550/arXiv.2109.09629
url: https://arxiv.org/abs/2109.09629v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.result
---

# Tightness of the 0-fidelity lower bound and the worst-case processes

## Problem

K. Mayer, *A short note on the 0-fidelity*, arXiv:2109.09629v1, proves for every $n$-qubit process
$\mathcal E$ that $1-\frac32(1-F_0)\le F\le F_0$, where $F$ is the process fidelity and $F_0$ the
0-fidelity on tensor products of single-qubit SIC-POVM states, and writes:

> This leads us to conjecture that the lower bound in Th.~1 is tight for all $n$.

> A description of the worst-case process is an open problem.

The verbatim statements are in [the literature note](../Library/QuantumChannels/mayer2021zerofidelity.md).
Issue [#14119](https://github.com/the-omega-institute/trureturing/issues/14119) reads the two
statements for every $n\ge1$, every choice of single-qubit SIC-POVMs and every finite Kraus family:
the lower bound holds with equality exactly when every Kraus operator lies in the span of the
identity and the single-qubit Pauli operators, and every value $f\in[\frac13,1]$ of $F_0$ is attained
with equality.

## Motivation

The 0-fidelity is estimated from product states only. If the lower bound is tight for every $n$,
the worst-case process fidelity does not approach the 0-fidelity as $n$ grows, so an estimate of
$F_0$ certifies only $1-\frac32(1-F_0)$; describing the worst cases identifies which errors the
product-state estimate cannot see.

## Gap

Issue #14119 records the literature check before any Lean: one arXiv version; arXiv full-text, web
and Zenodo searches and the citing work arXiv:2312.08590 contain no proof of tightness and no
description of the worst-case processes; the repository had no 0-fidelity result.
`not-found-in-searched-scope`.

## Route

Each qubit SIC is a 2-design: $\sum_kP_k\otimes P_k=\frac23(I+\mathrm{SWAP})$. Expanding a Kraus operator in
Pauli strings $\sigma_\beta$ (with $|\beta|$ non-identity factors) gives
$F_0=\sum_\beta3^{-|\beta|}q_\beta$ and $F=q_0$, where $q_\beta=d^{-2}\sum_j|\mathrm{tr}(\sigma_\beta^\dagger K_j)|^2\ge0$
and, by trace preservation, $\sum_\beta q_\beta=1$. Hence
$F-1+\frac32(1-F_0)=\frac12\sum_{\beta\ne0}(1-3^{1-|\beta|})q_\beta\ge0$, with equality iff
$q_\beta=0$ for every $|\beta|\ge2$. Depolarizing noise on one qubit,
$\{\sqrt pI,\sqrt{(1-p)/3}\,\sigma_a^{(1)}\}$, has $F=p$ and $F_0=p+\frac{1-p}3$.

## Falsifier

The statement concerns the 0-fidelity of the source (product single-qubit SIC states, uniform
weights) and finite Kraus families on $n$ qubits; other input ensembles or weightings are outside the
claim.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.lean`, with
public `IsQubitSIC`, `productState`, `zeroFidelity`, `processFidelity`, `HasWeightOneSupport`, `claim`
and `result : claim`. It contains the
single-qubit SIC frame identity `sic_frame` (the 2-design property of SIC-POVMs, entered as a
literature prerequisite; see [the note](../Library/QuantumStates/renes2004sic.md)). It reuses the
frozen `Pauli`, `pauliMatrix`, `tensorOp`, `wordOp` and the tensor product law `tensor_mul` of
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence`, the frozen maximally entangled
carrier `maxEntangledVector`, `maxEntangled` and its trace identity `max_entangled_trace` of
`D5/S3/QuantumBounds/PeritoTsirelson`, the frozen two-qubit swap `swapMatrix` of
`D5/S3/Resource/CompositeConeProperness` with its trace identity `hswap_trace`, Mathlib's `hammingDist`
for the Pauli weight, the frozen Kraus carrier `MatrixMap.of_kraus` and the rank-one transport
`hsandwich` of `D5/S3/Quantum/Measurement/ExactConditionalPreparationCost`, and the Pauli-word
expansion `word_expansion`, the unit `wordUnit` and the identities `tensor_one`, `word_one`,
`tensor_trace`, `pauli_trace_pair`, `pauli_hermitian` and `word_hermitian` of
`D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation`. Each of these was a private
declaration or a local step at its origin and is made public there, with its statement and proof
unchanged.
The axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no
`sorry`, `native_decide`, or new axiom.
The module statement is `sha256:207677a8f33b9dd5698be1a72aaddf2cf8220c1ef9d80607297f8da5d317cfda`,
the `result` statement `sha256:a5920d009739edf5671ef0802d3d3bc20d9adaeeed545c59b97a1c554535c065` and the
`claim` statement `sha256:0c567f7c43c7080bc672bd69401520dbe949740e5b88791c3428680b44d326cf`. The Freeze
event is `sha256:e354c9094fed1af2bbf82833bc9c8804febc056779ed106613cb31df97dac7ac`.

## Triage

Tier 1 conjecture and open problem of a 2021 note, preregistered in issue #14119 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | `channel_bound` (the Pauli-weight form of $F-1+\frac32(1-F_0)$ and its equality case) and `tight_channel` | open-problem-resolution |

The other theorems of the module lie on the proof path of `result` (CLAUDE.md §3.2
「有消费的辅助声明」); each has free arguments. Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\ge1$, every choice of single-qubit SIC-POVMs and every finite
Kraus family on $n$ qubits, $F\ge1-\frac32(1-F_0)$, with equality if and only if every Kraus operator
has zero coefficient on every Pauli string with at least two non-identity factors; and every
$f\in[\frac13,1]$ is the 0-fidelity of a process with $F=1-\frac32(1-f)$.

**Established inside the proof, for general data.** For every Kraus family,
$F_0=\sum_\beta3^{-|\beta|}q_\beta$ and $F=q_0$ with the Pauli-twirl weights
$q_\beta=d^{-2}\sum_j|\mathrm{tr}(\sigma_\beta^\dagger K_j)|^2$, which are nonnegative and, for a trace-preserving family, sum to one.

**Argued, not formalized.**

- *Mechanism.* Moving Pauli-twirl weight $\varepsilon$ from the identity to a Pauli string of weight
  $w$ lowers $F$ by $\varepsilon$ and $F_0$ by $(1-3^{-w})\varepsilon$; the decrease of $F_0$ is smallest,
  $\frac23\varepsilon$, for $w=1$. So for a given $F_0\in[\frac13,1]$ the process fidelity is lowest
  exactly when all error weight sits on strings acting on one qubit; errors of higher weight are more
  visible to the product-state average. Below $\frac13$ the affine bound is negative and is not the
  minimum (next item).
- *The low-fidelity range.* Since $q_\beta\ge0$ and $3^{-|\beta|}\ge3^{-n}$, every process has
  $F_0\ge3^{-n}$; for $f\in[3^{-n},\frac13]$ the minimum of $F$ is $0$, attained by Pauli channels supported
  on non-identity strings. So the tight lower boundary is $\max\{0,\frac{3f-1}2\}$ on $[3^{-n},1]$.
- *Upper bound.* The paper's upper bound $F\le F_0$ and its SDP improvement are not addressed here.

**Open.** A closed form of the best-case process fidelity for given $F_0$ (the paper's SDP upper bound)
is not settled here.

**Effect on the paper.** The §III conjecture holds for every $n$, and the §IV open problem has an
answer on $F_0\in[\frac13,1]$: the worst-case processes, that is, the equality cases of the bound
$F\ge1-\frac32(1-F_0)$, are exactly those whose Kraus operators lie in the span of the identity and the
single-qubit Pauli operators. For $F_0<\frac13$ the minimum of $F$ is $0$ (item above).

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof.
