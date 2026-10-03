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
   being the all-zero basis label; this is the fiducial `orbitG 0` of Hoggar's
   lines in `D5/S3/Quantum/Measurement/HoggarSicSumNegativity`.
2. The base-4 digits of `k = 1, …, 63` run once over the 63 non-identity words.
   For every non-identity word `P`, `⟨v, P v⟩ = ±4`; choose `β(k)` so that the
   term of `k` has `⟨v, (−1)^{β(k)} P v⟩ = 4` for the word `P` of its digits.
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
declarations are `sigmaOfDigit`, `signedPauliSum`, `claim` and `result`. The
frozen module state has statement identity
`sha256:5ebb858ca5b718085a5638734fe6923fb7a213d41c6f94d30e589264a10feb5c`.
The result declaration has statement identity
`sha256:8dfb1711bc592ab97d98ca9a33fecc3cdefd7764b3779911494541cecaef7b3e`.
The Freeze event is
`sha256:de20fca6148f3d61962ff00cb9b2cbd54a1ce4f50d52a0aaaf98afc681077d21`.
Its project-level frozen prerequisites are the Freeze events
`sha256:4e8b836150fe2870e8d48e5b319b779266b9ea7ffd050d33e8d7f31fb3c2cfc4` of
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence`, which
supplies `Pauli`, its `Fintype` instance, `pauliMatrix`, `tensorOp` and
`wordOp`, and
`sha256:6aca55a44811da2e4d06216d3b20ecd7d186121bb94590962da71149c212312f` of
`D5/S3/Quantum/Measurement/HoggarSicSumNegativity`, which supplies the
fiducial `orbitG` (and, through `D5/S3/Quantum/FiniteDimensional`,
`qubitX` and `qubitZ`). The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2016 quant-ph paper, preregistered in issue #11468
before any Lean. `theorem`; resolution `refuted`. The public theorem has
`proof_shape: bind-only`: it evaluates the definitions at the explicit sign
function. Its admission basis is `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

### What the settlement shows

**Proved (Lean):** for `m = 3` some sign function gives `‖Σ(β)‖ ≥ 21`, above
`(√3 + 1)³ − 1 = 9 + 6√3`, so the conjectured bound fails at `m = 3`.

**Mechanism (argument, not formalized):** for a unit vector `u` and any signs,
`⟨u, Σ(β) u⟩ = Σ_{P≠I} ±⟨u, P u⟩ ≤ Σ_{P≠I} |⟨u, P u⟩|
≤ ((4^m − 1) Σ_{P≠I} ⟨u, P u⟩²)^{1/2} = ((4^m − 1)(2^m − 1))^{1/2}`, since
`Σ_P ⟨u, P u⟩² = 2^m` for a pure state. So `‖Σ(β)‖ ≤ ((4^m − 1)(2^m − 1))^{1/2}`
for every `m` and every `β`, with equality only for a unit vector whose
non-identity Pauli expectations all have modulus `(2^m + 1)^{−1/2}` and signs
matching them up to an overall sign. The conjectured bound is the value of the all-equal signs, whose
top eigenvector is a product vector; the witness instead aligns every sign with
a vector whose Pauli expectations are flat.

**Computed (NumPy, not formalized):** at `m = 3` the bound is `21`, and the
vector `v/√12` of Route has all 63 non-identity expectations of modulus `1/3`,
so the witness attains it: the maximum of `‖Σ(β)‖` over all `β` is exactly
`21`. At `m = 1` the bound is `√3`, the paper's value. At `m = 2` the
exhaustive maximum is `3 + 2√3 ≈ 6.464`, below the bound `√45 ≈ 6.708`, so no
two-qubit unit vector has all fifteen expectations of modulus `1/√5`.

**Argument (not formalized), checked numerically for `m = 4, 5, 6`:** the
conjecture fails for every `m ≥ 3`. With signs that are products over blocks of
three qubits (the witness) and single qubits (`X + Y + Z`), the signed sum over
all words, the identity included, is the tensor product of the blocks'
`I + Σ_b`, of norms `22` and `1 + √3`. So for `m = 3k + r` with `k ≥ 1` and
`r ∈ {0, 1, 2}` some `β` gives `‖Σ(β)‖ ≥ 22^k (1 + √3)^r − 1`, which exceeds
`(1 + √3)^m − 1` because `22 > (1 + √3)³`; for `m = 4, 5, 6` these values are
`59.11`, `163.21` and `483` against `54.71`, `151.21` and `414.85`. The growth
rate of `max_β ‖Σ(β)‖` per qubit lies between `22^{1/3} ≈ 2.802` and
`2^{3/2} ≈ 2.828`, not at the conjectured `1 + √3 ≈ 2.732`. The paper's random
searches (best `18.528` at `m = 3`) did not reach these sign functions.

**Source consequences (argument, not formalized):** the paper's worst-case
success probability of the maximal `(4^m − 1, m, p)` QRACs with optimally
scaled Bloch vectors is `p = (1 + 1/λ)/2` (its Eq. `poflambda` with `d = 2`),
where `λ = max_β ‖Σ(β)‖`. Its upper bound
`p ≤ (1 + 1/((1 + √3)^m − 1))/2` (Eq. `maximalnbound`) remains valid, but the
claimed equality fails for every `m ≥ 3`. For `m = 3` the value is
`p = (1 + 1/21)/2 = 11/21 ≈ 0.5238`, not `≈ 0.5258`; for `m ≥ 4` it lies
between `(1 + 1/((4^m − 1)(2^m − 1))^{1/2})/2` and the value given by the block
construction above. The paper's constructions and its results for `m = 1, 2`
do not depend on the conjecture and stand.

**Open:** the exact value of `max_β ‖Σ(β)‖` for `m ≥ 4`, and whether the
per-qubit growth rate tends to `2^{3/2}`.

## ASSUMED-UNVERIFIED

The published Phys. Rev. A text was not read, so it is unverified whether the
conjecture was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.
