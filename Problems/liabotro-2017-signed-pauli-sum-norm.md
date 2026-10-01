---
slug: liabotro-2017-signed-pauli-sum-norm
bibkey: liabotro2017improved
doi: 10.1103/PhysRevA.95.052315
url: https://arxiv.org/abs/1607.02667v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result
---

# A signed sum of three-qubit Pauli words of norm 21

## Problem

O. Liabøtrø (arXiv:1607.02667, quant-ph; Phys. Rev. A 95, 052315 (2017))
studies maximal `(4^m − 1, m, p)` quantum random access codes. Their
worst-case success probability is governed by the signed sums
`Σ(β) = Σ_{k=1}^{4^m−1} (−1)^{β(k)} σ_{c_1(k)} ⊗ ⋯ ⊗ σ_{c_m(k)}` of all
non-identity Pauli words, for arbitrary signs `β`. The paper states:

> We have checked numerically that no $\Sigma(\beta)$ has an eigenvalue less
> than $1-(1+\sqrt(3))^m$ for $m=1,2$. … We conjecture that this is the case for
> all $m$, i.e.:
> $||\sum_{k=1}^{4^m-1}(-1)^{\beta(k)}\bigotimes_{i=1}^m\sigma_{c_i(k)}||\leq (\sqrt{3}+1)^m-1$

Issue #11468 fixes the reading. `k ↦ (c_1(k), …, c_m(k))` is a bijection onto
the non-identity words, `‖·‖` is the operator norm, and the conjecture is the
displayed inequality for every `m` and every `β`. The formal `claim` is that
inequality; the result refutes it.

## Motivation

If the conjecture held, the matrix `I − (I + σ_x + σ_y + σ_z)^{⊗m}` would be
extremal, and the worst-case success probability of these codes would equal
`(1 + 1/((1+√3)^m − 1))/2`. The frozen declaration
`D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result` shows that for
`m = 3` some sign function gives `‖Σ(β)‖ ≥ 21`. The eigenvalue form of the
paper's sentence fails too, since `−Σ(β)` has eigenvalue `−21 < 1 − (1+√3)³`;
that form is not formalized.

## Gap

Issue #11468 preregisters the reading, the counterexample and the literature
check. The conjecture is in the latest arXiv version. INSPIRE lists 18 citing
records. The arXiv sources of the 15 with arXiv identifiers were read at every
citation of the paper, and none treats the bound `(√3+1)^m − 1`. The
counterexample vector is a known fiducial vector of Hoggar's 64 lines in `ℂ⁸`.
Its connection to this conjecture was not found in the searched scope.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Take `m = 3` and `v = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1)`, the first coordinate
   being the all-zero basis label.
2. For every non-identity word `P`, `⟨v, P v⟩ = ±4`. Choose the signs so that
   each term has `⟨v, ε(P) P v⟩ = 4`.
3. Over the Gaussian integers, `Σ(β) v = 21 v`; the map to `ℂ` carries this to
   the complex matrices.
4. The operator norm bounds `‖Σ(β) v‖ ≤ ‖Σ(β)‖ ‖v‖`, so `‖Σ(β)‖ ≥ 21`, while
   `(√3 + 1)³ − 1 = 9 + 6√3 < 21`.

## Falsifier

The answer would change if `‖·‖` were read as a norm that can be smaller than
the largest eigenvalue modulus. For the Hermitian matrix `Σ(β)`, the operator
norm is that modulus. It would also change if only a restricted family of
signs were allowed; the paper states that `β` can be any function.

## Evidence

Exact SymPy arithmetic (issue #11468) gives `Σ(β) = 2vv* − 3I₈` for these
signs, with eigenvalues `21` (once) and `−3` (seven times). As positive
controls, exhaustive searches for `m = 1, 2` reproduce the paper's values
`√3` and `(√3+1)² − 1`.

The canonical source is
`D5/S3/Quantum/Information/SignedPauliSumNormRefutation.lean`. Its public
declarations are `signedPauliSum`, `claim` and `result`. The frozen module
state has statement identity
`sha256:8edd164a36313a1d853705c5850f4494eb475a969fc1c1cc4d716f42ff3fd27e`.
The result declaration has statement identity
`sha256:8dfb1711bc592ab97d98ca9a33fecc3cdefd7764b3779911494541cecaef7b3e`.
The Freeze event is
`sha256:784c85553037aa53888b9d56759bce852e3a203fe88927262c0fb6a0d5c19e02`.
Its one project-level frozen prerequisite is the Freeze event
`sha256:4e8b836150fe2870e8d48e5b319b779266b9ea7ffd050d33e8d7f31fb3c2cfc4` of
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence`, the only
project import, which supplies `Pauli`, its `Fintype` instance, `pauliMatrix`,
`tensorOp` and `wordOp` (and, through `D5/S3/Quantum/FiniteDimensional`,
`qubitX` and `qubitZ`). The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2016 quant-ph paper, preregistered in issue #11468
before any Lean. `theorem`; resolution `refuted`. The public theorem has
`proof_shape: bind-only`: it evaluates the definitions at the explicit sign
function. Its admission basis is `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

## ASSUMED-UNVERIFIED

The published Phys. Rev. A text was not read, so it is unverified whether the
conjecture was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.
