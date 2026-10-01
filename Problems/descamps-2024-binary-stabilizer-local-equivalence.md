---
slug: descamps-2024-binary-stabilizer-local-equivalence
bibkey: descamps2024stabilizer
doi: 10.1088/1751-8121/ad8607
url: https://arxiv.org/abs/2309.09815v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.result
---

# A binary-stabilized six-qubit state that is not locally a stabilizer state

## Problem

É. Descamps and B. Dakić (arXiv:2309.09815, quant-ph; J. Phys. A 57, 455301
(2024)) call a state of `N` qubits stabilized by a stabilizing set `𝒜` when it
is, up to a complex factor, the unique common `+1` eigenvector of finitely many
tensor products of elements of `𝒜`. Standard stabilizer states are those
stabilized by `𝒫 = {±1, ±i}·{𝟙, X, Y, Z}`. After an exhaustive analysis of two
and three qubits the paper states:

> \begin{conj} All states stabilized by the set $\mathcal A$ composed of binary
> operators and the identity {\it i.e.}, $\mathcal{A}=\{A_{\theta,\phi},\1_2\}$,
> are locally equivalent to standard stabilizer states (\textit{i.e.},
> stabilized by the Pauli group
> $\mathcal{P}=\{\pm 1,\pm i\}\cdot\{\1,\sigma_X,\sigma_Y,\sigma_Z\}$).
> \end{conj}

Issue #11565 fixes the reading. `A_{θ,φ} = cos θ Z + sin θ (cos φ X + sin φ Y)`,
stabilization needs no commutativity, and local equivalence is
`ψ = (U_1 ⊗ ⋯ ⊗ U_N) φ` with `U_i ∈ U(2)`. The formal `claim` is the conjecture
for every `N`; the result refutes it.

## Motivation

If the conjecture held, binary stabilization would describe nothing beyond the
standard stabilizer formalism up to local unitaries. The frozen declaration
`D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.result` shows
that six qubits already give a state stabilized by four tensor products of
binary operators that no local unitary maps to a standard stabilizer state.

## Gap

Issue #11565 preregisters the reading, the witness, the route and the
literature check. The conjecture is in the only arXiv version. Semantic
Scholar lists 6 citing records; the arXiv sources of the five with identifiers
were searched, and none treats the conjecture. Author and abstract searches on
arXiv found no follow-up on binary stabilization. The paper notes that the
analogous statement fails for the XS stabilizing set of Ni et al., which is not
a set of binary operators.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Let `v` have coefficient `1` on the six labels of Hamming weight one, `−1`
   on the six of weight five and `0` elsewhere, and take
   `O_1 = (−X) ⊗ X^{⊗5}`, `O_2 = (−Z) ⊗ Z^{⊗5}`, `O_3 = H^{⊗6}`, `O_4 = K^{⊗6}`
   with `H = (X+Z)/√2 = A_{π/4,0}` and `K = (X+Y)/√2 = A_{π/2,π/4}`.
2. `O_2` kills even weights, `O_1` makes complementary coefficients opposite,
   `O_4` kills weight three, and `O_3` at six weight-three labels forces the
   weight-one coefficients to be equal; all four fix `v`.
3. For a state `φ` stabilized by phased Pauli words, every Pauli word `P`
   anticommutes with some stabilizer `T`, giving `⟨φ, Pφ⟩ = −⟨φ, Pφ⟩ = 0`, or
   commutes with all of them, giving `Pφ = ±φ`. So the pair purity
   `Σ_{g,h} |⟨φ, (g ⊗ h ⊗ 𝟙^{⊗4}) φ⟩|²` is an integer multiple of `‖φ‖⁴`.
4. The pair purity is `4 tr(ρ₁₂ ρ₁₂†)` for the unnormalized reduced state of
   qubits 1, 2, and local unitaries conjugate `ρ₁₂` by a unitary, so it and
   `‖φ‖` are invariant under local equivalence. For `v` the pair purity is
   `192` and `‖v‖⁴ = 144`.

## Falsifier

The answer would change if stabilization required the operators to commute,
or if local equivalence allowed non-unitary local maps; the paper defines
neither restriction. It would also change if binary operators excluded the
signs `−X`, `−Z`; these are `A_{π/2,π}` and `A_{π,0}`.

## Evidence

Exact SymPy arithmetic (issue #11565) gives `O_a v = v`, each `O_a` Hermitian
with `O_a² = 𝟙`, a one-dimensional common `+1` eigenspace, and the marginal
`ρ₁₂` of `v/‖v‖` with `tr(ρ₁₂²) = 1/3`. As a positive control, the Pauli
stabilizer state `(|0⁶⟩ + |1⁶⟩)/√2` gives `4 tr(ρ₁₂²) = 2`, an integer.

The canonical source is
`D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.lean`. Its public
declarations are `binaryOp`, `binarySet`, `pauliSet`, `StabilizedBy`,
`LocallyEquivalent`, `claim` and `result`. The frozen module state has
statement identity
`sha256:6f7d09fe6589c9cd9f0d6519093013695a5d05a890462b95ea44ec07457b1c0e`.
The result declaration has statement identity
`sha256:1728416a009c8e60a1ff43fe1a0335498101aaec112556e56c78cb36403ce42d`.
The Freeze event is
`sha256:c83def4626e900f66ec9bc6a27f2f58482bcc26454dbd84d6bdfa01f6f814934`.
Its project-level frozen prerequisite is the module providing `Pauli`,
`pauliMatrix`, `tensorOp` and `wordOp`, which itself builds on `qubitX` and
`qubitZ`. The proof uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2023 quant-ph paper, preregistered in issue #11565
before any Lean. `theorem`; resolution `refuted`. The public theorem has
`proof_shape: content`, with escape witness form (2), the conclusion itself:
inside its proof, the expectation trichotomy for Pauli stabilizer states and the
local-unitary invariance of the pair purity are established as local steps on
its live path. Its admission basis is `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

### What the settlement shows

**Proved (Lean):** the six-qubit state `v`, which is `|W₆⟩ − X^{⊗6}|W₆⟩` for
the W state `|W₆⟩` up to normalization, is stabilized by four tensor products
of binary operators and is not locally equivalent to any state stabilized by
phased Pauli words.

**Mechanism (proved inside `result` for qubits 1 and 2):** for a state `φ`
stabilized by phased Pauli words, every Pauli word `P` has
`⟨φ, Pφ⟩ ∈ {0, ±‖φ‖²}`, so the unnormalized pair purity
`Σ_{g,h} |⟨φ, (g ⊗ h ⊗ 𝟙^{⊗4}) φ⟩|²` is an integer multiple of `‖φ‖⁴`, and
local unitaries preserve it and `‖φ‖`. For `v` it is `192` with
`‖v‖⁴ = 144`; in normalized form, `4 tr(ρ₁₂²) = 4/3` for `ρ₁₂` the two-qubit
marginal of `v/‖v‖`, while every Pauli stabilizer state gives an integer.

**Computed (NumPy, not formalized):** every two-qubit marginal of `v` has
spectrum `(1/3, 1/3, 1/3, 0)`, every one-qubit marginal is maximally mixed and
every three-qubit marginal has purity `1/4`. The six-qubit XS-stabilizer state
of Ni et al. that the paper cites has maximally mixed two-qubit marginals
(purity `1/4`), so `v` is not locally equivalent to it either.

**Open:** the weaker conjecture that the paper states for binary operators in
the `(XZ)`-plane (`A = {A_θ, 1}`); the witness uses `K = (X + Y)/√2`, which is
not in that plane. Also open: whether a counterexample exists on four or five
qubits (the paper's exhaustive analysis covers two and three qubits).

**Source consequences:** the paper's theorem on generalized Clifford groups and
its two- and three-qubit analysis do not depend on the conjecture and stand;
the stabilization by binary operators and the identity is strictly larger, up
to local equivalence, than the Pauli stabilizer formalism.

## ASSUMED-UNVERIFIED

The published J. Phys. A text was not read, so it is unverified whether the
conjecture was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.
