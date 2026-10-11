---
slug: cepollaro-2025-power-of-two-zero-magic-gap
bibkey: cepollaro2025stabilizer
doi: 10.48550/arXiv.2512.23013
url: https://arxiv.org/abs/2512.23013v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.result
---

# Zero-magic-gap three-dimensional subspaces in every power-of-two dimension

## Problem

S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma and S. Lloyd, *Stabilizer
Entropy of Subspaces*, arXiv:2512.23013v1, define the average stabilizer entropy gap of an
isometry $\mathcal E:\mathbb C^{d_S}\to\mathbb C^{d_B}$ as the Haar average over pure states of
the difference between the linear stabilizer entropy of $\mathcal E(\psi)$ for the single-qudit
Weyl–Heisenberg group of $\mathbb C^{d_B}$ and that of $\psi$ for the group of $\mathbb C^{d_S}$,
and write it in closed form as
$\Delta M(\mathcal E)=d_S\,\mathrm{tr}(Q_S\mathcal A_4^S)-d_B\,\mathrm{tr}(Q_B\mathcal E^{\otimes4}(\mathcal A_4^S))$.
In §V.A they report from numerical optimization that "when $d_B$ is a power of 2, a zero ASE
subspace of dimension three is always achievable", and in their conclusion that "it is unclear
why" this happens. The verbatim definitions and statements are in
[the literature note](../Library/QuantumStates/cepollaro2025stabilizer.md).

Issue [#13822](https://github.com/the-omega-institute/trureturing/issues/13822) reads a
three-dimensional subspace as the image of an isometry $V:\mathbb C^3\to\mathbb C^{d_B}$ and the
Haar fourth moment in the paper's closed form $\binom{6}{4}^{-1}\frac1{24}\sum_{\sigma\in S_4}T_\sigma$.

## Motivation

The ASE gap measures the extra nonstabilizerness that an encoding into a larger system costs on
average. The paper proves zero or negative gap for stabilizer codespaces, which cannot have
dimension three inside $\mathbb C^{2^m}$, and leaves the power-of-two family unexplained.
`D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.result` proves the family for every
$m\ge2$, and its proof gives the mechanism.

## Gap

Issue #13822 records the literature check before any Lean: arXiv lists only v1; web searches
for the title, "zero ASE gap", "average magic gap" and "power of 2" return the paper and
related stabilizer-entropy work but no proof; Zenodo phrase searches return no record; the
repository had no result on the ASE gap. `not-found-in-searched-scope`.

## Route

Let $d_B=4r$ and $V=WV_4$ with $W|k\rangle=|kr\rangle$ from $\mathbb C^4$ to $\mathbb C^{4r}$ and
$V_4e_1=|1\rangle$, $V_4e_2=|3\rangle$, $V_4e_3=(|0\rangle-|2\rangle)/\sqrt2$, so the subspace is
$\mathrm{span}\{|r\rangle,|3r\rangle,(|0\rangle-|2r\rangle)/\sqrt2\}$.

1. **Compression.** $\mathrm{tr}(Q\,V^{\otimes4}\mathcal A_4V^{\dagger\otimes4})=d^{-2}\sum_{\mathbf a}\mathrm{tr}((A_{\mathbf a}\otimes A_{\mathbf a}^\dagger\otimes A_{\mathbf a}\otimes A_{\mathbf a}^\dagger)\mathcal A_4)$
   with $A_{\mathbf a}=V^\dagger D_{\mathbf a}V$, and the phases $\tau^{a_1a_2}$ cancel.
2. **Subgroup reduction.** $W^\dagger X^aZ^bW=0$ unless $r\mid a$, and
   $W^\dagger X^{ur}Z^bW=X_4^uZ_4^{b\bmod4}$; each residue of $b$ has $r$ lifts, so the extrinsic
   term of $WU$ equals that of $U$ for every $U:\mathbb C^3\to\mathbb C^4$.
3. **Fourth moments.** $\mathrm{tr}((A\otimes A^\dagger\otimes A\otimes A^\dagger)T_\sigma)$ is a
   product of traces over the cycles of $\sigma$. For the sixteen $V_4^\dagger X_4^uZ_4^vV_4$ the
   moments are $1$ once, $1/5$ three times and $1/15$ twelve times, so the extrinsic term is
   $\frac14(1+\frac35+\frac{12}{15})=\frac35$; for the nine qutrit operators they are $1$ once and
   $1/10$ eight times, so the intrinsic term is $\frac13(1+\frac8{10})=\frac35$.
4. $2^m=4\cdot2^{m-2}$ for $m\ge2$.

## Falsifier

The settlement would fail under a normalization of $Q$ or of the fourth moment different from
the paper's closed forms, or if the paper's ASE gap were meant for a subspace treated as
$m$ qubits; §V.A states the observation "if the overall system is treated as a qudit".

## Evidence

The canonical source is `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.lean`. Its public
declarations are `tau`, `paperDisplacement`, `power4`, `alt`, `T`, `Q`, `A4`, `score`, `aseGap`,
`claim` and `result`. It reuses the frozen shift, clock and root of unity of
`D5/S3/Observer/WindowRegister` (`shiftMatrix`, `clockMatrix`, `windowRoot`), the frozen Weyl
displacement words and their laws of `D5/S3/Quantum/Algebra/WeylDisplacement*` and
`WeylPhaseArithmetic`, and the frozen fourfold product `productMap` of
`D5/S3/Quantum/Recovery/PurifiedLocalPath`; it imports `D5.S3.Quantum.Recovery.PurifiedLocalPath`,
`D5.S3.Quantum.Algebra.WeylDisplacementTrace` and `D5.S3.Quantum.Algebra.WeylDisplacementPowers`.
The qudit space is indexed by `ZMod d`. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.
The module statement is `sha256:8f9ead647b3f781c754d4fbb980c859963f522e0559270f764171d4fc29eb0ac`,
the `result` statement `sha256:e29d0703a6ca13d191f857cd2e0037d9f43c170f9a85ad5afa828b50844db2de` and the
`claim` statement `sha256:abf425867cb43678f35693d893580ed4cff32c95c77245cb5d382a135cc33645`. The Freeze
event is `sha256:64f465f55b52a7fc1dc609c8ccff284a0525809915df6e2f45f4347838b5d886`; its project-level
prerequisites are the three frozen modules it imports.

## Triage

Tier 1 observation of a December 2025 paper, preregistered in issue #13822 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The private theorems (`tau_unit`, `displacement_entry`, `product4_mul`, `product4_adjoint`,
`perm_trace`, `pair_cycle_sum`, `moment_formula`, `alt_phase`, `compressed_trace`,
`score_weyl`, `W_isometry`, `windowRoot_restrict`, `subgroup_compression`, `lift_sums`,
`score_lift`, `lift_solution`, `power_two_factor`) are bind-only and are used on the proof path
of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `none`: every theorem of the module
has a free dimension, matrix, function or exponent parameter, and the fixed scalar identities,
the isometry check of $V_4$, the two moment tables and the two base values are local steps in the
proof of `lift_solution`, which is general in $r$. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $m\ge2$ some isometry $V:\mathbb C^3\to\mathbb C^{2^m}$ has zero
ASE gap.

**Established inside the proof.** The private `lift_solution` proves zero gap for the
subspace $\mathrm{span}\{|r\rangle,|3r\rangle,(|0\rangle-|2r\rangle)/\sqrt2\}$ of $\mathbb C^{4r}$ for every
$r\ge1$, that is, for every $d_B$ divisible by four; `result` applies it with $r=2^{m-2}$. The
extrinsic term of $WU$ equals that of $U$ for every $U:\mathbb C^3\to\mathbb C^4$ and every $r\ge1$
(`score_lift`). The qutrit intrinsic term and the extrinsic term of the ququart subspace
$\mathrm{span}\{|1\rangle,|3\rangle,(|0\rangle-|2\rangle)/\sqrt2\}$ are both $3/5$ (local steps of
`lift_solution`).

**Argued, not formalized.**

- *Mechanism.* The reduction of step 2 holds for every $k$: if $U:\mathbb C^{d_S}\to\mathbb C^k$
  and $W|j\rangle=|jr\rangle$ from $\mathbb C^k$ to $\mathbb C^{kr}$, then $W^\dagger X^{ur}Z^bW=X_k^uZ_k^{b\bmod k}$,
  other shifts compress to zero, and $kr\cdot(kr)^{-2}\cdot r=k\cdot k^{-2}$, so the extrinsic term
  of $WU$ equals that of $U$. Zero-gap subspaces therefore propagate from $\mathbb C^k$ to every
  $\mathbb C^{kr}$. The power-of-two family is the propagation of one zero-gap subspace of the
  ququart; taking $k=d_S$ and $U$ the identity explains the paper's other observation, zero gap
  "when $d_S$ is a factor of $d_B$".
- *Values.* With the control subspace $\mathrm{span}\{|0\rangle,|1\rangle,|2\rangle\}$ the gap is
  $1/15$ for $d_B=4$ and $2/15$ for $d_B=6,8,10,12,16$ (floating-point evaluation of the closed form recorded in #13822), so zero gap depends on the choice of subspace.

**Open.** Whether a zero-gap three-dimensional subspace exists for $d_B$ divisible by neither 3
nor 4 (for example $d_B=5,7,10,11,13,14$) is not determined here.

**Effect on the paper.** The power-of-two observation of §V.A holds, and the mechanism the
conclusion asks for is the subgroup embedding of a ququart zero-gap subspace.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof.
