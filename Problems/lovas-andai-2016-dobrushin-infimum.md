---
slug: lovas-andai-2016-dobrushin-infimum
bibkey: lovas2016volume
doi: 10.48550/arXiv.1607.01215
url: https://arxiv.org/abs/1607.01215
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.result
---

# Lovas and Andai's conjecture on the least trace-distance contraction over a classical channel

## Problem

Lovas and Andai represent a qubit channel `Q : M_2 → M_2`, a completely
positive trace-preserving map, by its Choi block matrix, whose blocks
`Q_11 = Q(|0⟩⟨0|)` and `Q_22 = Q(|1⟩⟨1|)` have diagonals `(a, 1−a)` and
`(f, 1−f)` in the parametrization (eq:matQ). The trace-distance contraction
coefficient is

> η^Tr(Q) = sup { Tr|Q(ρ) − Q(σ)| / Tr|ρ − σ| : ρ, σ ∈ M_2 },

and `Q_C(a,f)` denotes the set of qubit channels over the classical channel
`((1−a, a), (1−f, f))` with respect to that parametrization. The subsection
on the distribution of `η^Tr` over classical channels states

> We conjecture that inf{η(Q) : Q ∈ Q_C(a,f)} = |a−f| which is equal to the
> trace-distance contraction coefficient of the underlying classical channel.

Issue #10033 fixes the readings: `M_2` is the set of qubit states and a qubit
channel is a completely positive trace-preserving map; `Q_C(a,f)` is fixed by
the upper-left entries `a` and `f` of `Q(|0⟩⟨0|)` and `Q(|1⟩⟨1|)`, trace
preservation giving the other diagonal entries; the source writes positivity
of the Choi matrix as `Q > 0`, and complete positivity is read as a positive
semidefinite Choi matrix; in the ratio a pair of equal states contributes the
value zero; `a, f ∈ [0,1]`.

## Motivation

The frozen declaration
`D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.result` proves that,
for all `a, f ∈ [0,1]`, `|a − f|` is the least value of `η^Tr` over
`Q_C(a,f)`: the infimum equals `|a − f|` and is attained. The trace-distance
contraction coefficient is the quantum analogue of the Dobrushin coefficient
of ergodicity and bounds mixing times of quantum Markov processes; the
theorem says that fixing the classical channel of a qubit channel forces no
contraction beyond that of the classical channel itself.

## Gap

Issue #10033 preregisters this published conjecture and its literature
check. MathDB `/p/333535` has status `open` with zero solutions; Semantic
Scholar lists one citation of arXiv:1607.01215, a paper of the same authors
on locally diagonalizable bipartite states that does not address the
conjecture. The source proves that every value strictly between `|a − f|` and
`√((1−a)f) + √(a(1−f))` is attained, and its simulations estimate the
infimum numerically.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

Lower bound: for `Q ∈ Q_C(a,f)`, the matrix `A = Q(|0⟩⟨0|) − Q(|1⟩⟨1|)` has
`A_00 = a − f` and, by trace preservation, `A_11 = f − a`. The variational
formula `Tr|A| = max_U re Tr(UA)` over unitaries, tested with
`U = diag(s, −s)` for the sign `s` of `a − f`, gives `Tr|A| ≥ 2|a − f|`, while
`|0⟩⟨0|` and `|1⟩⟨1|` are at trace distance one. So the ratio for this pair is
at least `|a − f|`, and so is `η^Tr(Q)`.

Attainment: the measure-and-prepare channel
`Q_0(X) = Σ_{i,j} p_j(i) X_jj |i⟩⟨i|`, with `p_0 = (a, 1−a)` and
`p_1 = (f, 1−f)`, has Kraus operators `√p_j(i) |i⟩⟨j|` and lies in
`Q_C(a,f)`. For states `ρ, σ` with `t = ρ_00 − σ_00`, it sends `ρ − σ` to
`diag((a−f)t, (f−a)t)`. Every unitary has diagonal entries of modulus at most
one, so the variational formula gives `Tr|Q_0ρ − Q_0σ| ≤ 2|a − f||t|`, while
the same test unitary as above gives `Tr|ρ − σ| ≥ 2|t|`. Every ratio is
therefore at most `|a − f|`, and `η^Tr(Q_0) = |a − f|`.

## Falsifier

A counterexample would be a channel in `Q_C(a,f)` with `η^Tr < |a − f|`;
under every such channel the images of the pair `|0⟩⟨0|, |1⟩⟨1|`, which are
at trace distance one, have trace distance at least `|a − f|`. A failure of attainment would require every channel in `Q_C(a,f)`
to exceed `|a − f|`; the measure-and-prepare channel does not.

## Evidence

For 3000 random Stinespring channels with a four-dimensional environment,
`η^Tr` computed as the largest singular value of the Bloch matrix of
(eq:matT) never falls below `|a − f|`; the least excess is `0.00152`. For
`(a,f) = (.3,.8), (.1,.15), (.5,.5), (.9,.2), (0,1), (1,1)` the
measure-and-prepare channel has `η^Tr = |a − f|`, and direct sampling over
pure-state pairs agrees within `7·10^{-4}`; the positive control
`η^Tr(Q_0) ≥ |a − f| + 0.01` fails in all six cases. The Lean proof has only
the standard axiom closure `propext`, `Classical.choice`, and `Quot.sound`.
These finite checks support the reading but do not establish the universal
theorem.

## Triage

First-tier external named open problem: Lovas and Andai, arXiv:1607.01215
(2016), Conjecture `\label{conj}` of the subsection on the distribution of
`η^Tr` over classical channels, preregistered in issue #10033. Resolution:
`proved`, with the infimum attained.

The public surface is exactly `classicalFiber`, `dobrushin`, `claim`, and
`result`. This is a uniform theorem, not bounded enumeration, checker
infrastructure, numeric reduction, or a certified finite instance, so
`utility: none` applies.

## ASSUMED-UNVERIFIED

Whether the journal version, Rev. Math. Phys. 30 (2018) 1850019 (DOI
10.1142/S0129055X18500198), retains or changes the conjecture has not been
checked. The bounded literature check does not establish exhaustive worldwide
novelty, priority, or the absence of an independent proof. The Lean kernel
does not authenticate the external source, its version history, or the
literature-check coverage. The finite checks do not establish the universal
theorem.
