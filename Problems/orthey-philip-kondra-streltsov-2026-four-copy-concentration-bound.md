---
slug: orthey-philip-kondra-streltsov-2026-four-copy-concentration-bound
bibkey: ortheyphilipkondrastreltsov2026optimality
doi: 10.1103/bz3j-9njg
url: https://arxiv.org/abs/2509.09423v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.result
---

# Direct four-copy universal entanglement concentration beats the bound of Eq. (8)

## Problem

A. C. Orthey, A. Philip, T. V. Kondra and A. Streltsov, *Optimality of universal conclusive entanglement concentration protocols*, Phys. Rev. A 113, 062404 (2026), arXiv:2509.09423v2, study LOCC protocols that turn copies of an unknown two-qubit pure state into the Bell state ϕ+.
- **Universality.** Definition 1: an n-to-1 LOCC map E1 is a universal conclusive protocol if ⟨ϕ+|E1(ρ⊗n)|ϕ+⟩ = Tr E1(ρ⊗n) for every input in the set, here every pure state |ψ⟩ = c1|00⟩ + c2|01⟩ + c3|10⟩ + c4|11⟩ (Eq. (1)).
- **The bound.** Theorem 3 bounds the four-copy success probability of concatenated protocols based on two-qubit operations by B(c) = 2|c2⁴c3⁴| + 2|c1⁴c4⁴| − 4Re[c1²c4²(c2*)²(c3*)²] (Eq. (8)).
- **The conjecture.** §VIII: "protocols that process four copies directly without intermediate Schmidt-state conversion warrant investigation. We conjecture that such protocols cannot surpass the success probability bound in Eq. (8)".

The verbatim statements are in [the literature note](../Library/QuantumBounds/ortheyphilipkondrastreltsov2026optimality.md).

Issue [#17404](https://github.com/the-omega-institute/trureturing/issues/17404) fixes the reading: for every universal conclusive LOCC map on four copies and every normalized ψ, Tr E1(ψ⊗4) ≤ B(c).

The conjecture is refuted.

## Motivation

Universal protocols must work without knowing the Schmidt basis of the input, and the paper quantifies the cost of universality by comparing Eq. (8) with Vidal's state-dependent optimum. The conjecture would make the two-stage protocol of Kálmán et al. optimal among all universal four-copy protocols.

## Gap

Issue #17404 records the literature check before any Lean:
- arXiv v1 and v2 both state the conjecture, and the journal version is listed;
- OpenAlex and INSPIRE list no citing work;
- no settlement was found on Zenodo, Crossref or in the repository Naixu-Guo/quantum-open-problems;
- the repository had no entry for the paper.

The mechanism used here is Hayashi–Matsumoto's universal concentration (quant-ph/0209030), which the paper does not cite.

`not-found-in-searched-scope`.

## Route

1. **The protocol.** Each party applies the same local success operator K = |0⟩⟨u| + |1⟩⟨v| to its four qubits, and the parties keep the output when both succeed. Here:
   - u and w are the products of two singlets on positions (1, 2), (3, 4) and on positions (1, 3), (2, 4);
   - v = (2w − u)/√3, so K K† = 1 and K†K is a projection.
2. **Universality.** For every coefficient matrix C, (C ⊗ C) maps the singlet to det C times the singlet. So C^{⊗4} fixes the span of u and w up to the factor (det C)², and the output coefficient matrix is K C^{⊗4} Kᵀ = (det C)² I.
3. **The success probability** is 2|det C|⁴ for every ψ.
4. **The counterexample.** At ψ0 = (|00⟩ + |01⟩ − |10⟩ + |11⟩)/2, a maximally entangled state, det C = 1/2. The success probability is 1/8, while B = 0.

## Falsifier

The refutation would not settle the conjecture if:
- the protocol were not LOCC;
- it were not universal for every pure two-qubit state;
- it used an intermediate Schmidt-state conversion;
- the module's B differed from Eq. (8);
- the success probability were computed for a different branch.

The module states the conjecture for every pair of local contractions K_A, K_B whose product success operator is universal, and each such pair completes to local instruments. It gives the exact output (det C)² times the Bell array for every C, and evaluates the literal Eq. (8) at ψ0.

## Evidence

The canonical source is `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.lean` (155 lines, `generality: I`, `utility: kind=certified-instance; basis=refutes`).
- It defines `Q`, `normalized`, `amp4`, `output`, `universal`, `success`, `B` and `claim`, and the witness `u`, `v`, `K` and `C0`, and proves `result : ¬ claim`.
- It reuses:
  - the frozen `FiniteDimensional.QubitMatrix`, `QubitWitnesses.bellCoefficients` and `QutritThresholdSharing.normalization`;
  - `StatisticalStrengthMagicSquare.rationalSinglets`, made public for this settlement, as the pairing vector on positions (1, 3), (2, 4), and through a coordinate permutation as u.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the designated refutation result and is exempt from the escape registration (CLAUDE.md §3.9); `rationalSinglets` is a definition.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.lean.json`, statement `sha256:f338a5562015cc769b3a09c11d969bf566f68053301d14ee9ec6ddfd7bdc4a2f`.

Declaration statements:
- `result`: `sha256:6b92e6162359d2efddbc8fd88ecde5f7c8c765fb537b0b3c551a4fa578b0fc2a`;
- `claim`: `sha256:6c6bd115986b2f367a38423db80b60df8dc840df25d07d702351c7faf97aa043`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the output identity, the coisometry, the contraction and the values at C0 are instantiations of frozen D5 and pinned Mathlib results followed by normalization and polynomial arithmetic | open-problem-resolution |
| the output, coisometry, contraction, universality and value helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 8 private theorems are bind-only helpers consumed on the proof path of `result`, and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

## Triage

### What the settlement shows

**Refuted by `result`:** a single universal one-round LOCC protocol on four copies has success probability 2|det C|⁴, which exceeds Eq. (8) at the maximally entangled input ψ0 (1/8 against 0).

**Computed, not formalized** (orchestrator, 15 October 2026; recorded in #17404):
- the identity K C^{⊗4} Kᵀ = (det C)² I holds exactly for symbolic C (SymPy);
- the maximal deviation over 2000 random normalized inputs is 1.7 × 10⁻¹⁶ (NumPy).

**Argued, not formalized.**
- With Δ = c1c4 − c2c3 and Σ = c1c4 + c2c3, Eq. (8) equals 2|Δ|²|Σ|². So the protocol beats Eq. (8) exactly when |Δ| > |Σ|, that is when Re(c1c4 · conj(c2c3)) < 0.
- The protocol is the Young-index (2, 2) sector of Hayashi–Matsumoto's universal concentration. Their index (3, 1) sector yields a three-dimensional maximally entangled state, which LOCC converts into ϕ+ deterministically. By the Schur weights dim V_λ · s_λ(x, y) of the Schmidt weights x and y, this raises the success probability to 3xy(x² + xy + y²) + 2x²y², which is 11/16 at ψ0.
- At ψ0 the concatenated protocol of the paper succeeds with probability 0, since its Eq. (10) carries the factor of Eq. (8).

**Open.**
- The optimal success probability of universal four-copy concentration into ϕ+, and whether the combined Schur-sector protocol attains it.

**Effect on the paper.** The conjecture of §VIII is false: direct four-copy processing beats Eq. (8), and Schmidt-basis alignment is not an optimal strategy for universal operations. Theorem 3 is unaffected, since it concerns concatenated two-qubit protocols only.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
