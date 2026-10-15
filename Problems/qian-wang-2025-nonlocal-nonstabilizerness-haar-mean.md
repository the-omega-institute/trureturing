---
slug: qian-wang-2025-nonlocal-nonstabilizerness-haar-mean
bibkey: qian2025nonlocalnonstabilizerness
doi: 10.1103/PhysRevA.111.052443
url: https://arxiv.org/abs/2502.06393v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.result
---

# The Haar mean of two-qubit non-local nonstabilizerness is 10/3 − π

## Problem

D. Qian and J. Wang, *Quantum Non-Local Nonstabilizerness*, arXiv:2502.06393v4, Phys. Rev. A **111**, 052443 (2025), define the non-local nonstabilizerness (NN) of a state as the stabilizer Rényi entropy minimized over local unitaries. For two-qubit pure states it depends only on the Schmidt weight x = cos²θ (Eq. (C1)): M(x) = ln(1/(1 + 4x(x − 1)(1 − 2x)²)). For Haar-random states x has density 3(1 − 2x)², and Appendix C derives the density (C5) of y = M(x) on 0 < y < ln(4/3).

§III states that "a closed-form expression for the average value of M … remains unclear" and reports approximately 0.192. Appendix C writes: "we have not been able to find a simple closed-form expression for the average amount of NN, ȳ ≡ ∫ yP(y)dy, for the Haar random state", and gives ȳ ≈ 0.1917 by numerical integration. The verbatim statements are in [the literature note](../Library/QuantumStates/qian2025nonlocalnonstabilizerness.md).

Issue [#16544](https://github.com/the-omega-institute/trureturing/issues/16544) fixes the reading. With P the literal (C5) on (0, ln(4/3)) and 0 elsewhere, y·P(y) is integrable and ȳ = ∫ y P(y) dy = 10/3 − π. It is proved.

## Motivation

The mean is the typical amount of magic that no local basis change can remove from a random two-qubit state. A closed form puts it alongside Page's mean entanglement entropy, which the source names as the analogue.

## Gap

Issue #16544 records the literature check before any Lean:
- arXiv v4 is the latest version and keeps the sentence;
- the citing works arXiv:2610.06791, arXiv:2608.08346 and arXiv:2604.27055 contain no closed form for this mean;
- Zenodo and web search return no settlement;
- the repository's earlier settlement of this paper (#14115) concerns Appendix F.

`not-found-in-searched-scope`.

## Route

1. **The primitive.** Put q(t) = t⁴ − t² + 1 and F(t) = −t³ ln q(t) + (4/3)t³ + 2t − 2(arctan(2t + √3) + arctan(2t − √3)).
   - The factorization q(t) = (t² + √3t + 1)(t² − √3t + 1) gives F′(t) = −3t² ln q(t).
   - F(0) = 0. Since 2 + √3 and 2 − √3 are reciprocal, F(1) = 10/3 − π.
2. **The branches.** For 0 < y < a = ln(4/3), put w = √(4e^{−y} − 3) and t± = √((1 ± w)/2). Then q(t±) = e^{−y}, and (C5) equals 3e^{−y}(t₋ + t₊)/(2w).
3. **The antiderivative.** G(y) = F(t₋(y)) − F(t₊(y)) has G′(y) = y·P(y) on (0, a). It extends continuously with G(0) = −(10/3 − π) and G(a) = 0.
4. **Integrability.** 0 ≤ y·P(y) ≤ a√3/√(a − y), so the integral converges. The fundamental theorem of calculus gives ȳ = G(a) − G(0) = 10/3 − π.

## Falsifier

The proof would not settle the question if:
- the module's density differed from (C5) or from its support;
- its integral differed from the source's ȳ ≡ ∫ yP(y)dy.

The module's `nnDensity` is (C5) symbol by symbol on 0 < y < ln(4/3), the range of M, and 0 elsewhere. `claim` takes the Lebesgue integral over ℝ, which is the source's integral.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.lean` (404 lines).
- It defines `zC`, `nnDensity` and `claim`, and proves `result : claim`.
- It uses pinned Mathlib calculus (derivatives of `Real.log`, `Real.sqrt`, `Real.exp` and `Real.arctan`), the fundamental theorem of calculus on intervals with endpoint limits, the integrability of (a − y)^{−1/2}, and set integrals of functions vanishing off an interval. It has no frozen D5 dependency.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.lean` reads out the value 10/3 − π of `claim`. Its rejected realization, the value 0, fails because π < 3.15. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.lean.json`, statement `sha256:6487e89dfff1f453b424f59388b903e7930017e79cf68b980466269b94a0b04a`.

Declaration statements:
- `result`: `sha256:d9fccd4b709356696318d71436397ecd3b99eb794c86cfa41b636eae5ee0c7c8`;
- `claim`: `sha256:5dd9d4dd564bff9b9d49218dd544a30055c4d0805c3ad2bcd13355e6c9c89c51`.

## Triage

Tier 1 open question of a 2025 paper, preregistered in issue #16544 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the primitive, the branch derivatives, the integrability bound and the fundamental theorem of calculus are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |
| the primitive, branch, antiderivative, bound and integral helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the source's mean ȳ = ∫ y P(y) dy of (C5) converges and equals 10/3 − π ≈ 0.19174.

**Computed, not formalized** (orchestrator, 14 October 2026):
- `scipy.integrate.quad` of (C5): ∫ P = 1.0000000001 and ∫ yP = 0.19174067973865, against 10/3 − π = 0.19174067974354;
- the Monte Carlo mean of M(x) over 2 × 10⁶ Haar-random two-qubit states is 0.19163 ± 0.00006;
- brute-force minimization of M₂ over local unitaries agrees with (C1) to within 10⁻⁶ for 6 random states;
- control: the mean under the uniform distribution of x is 0.148.

**Argued, not formalized.**
- Through the substitution t = 1 − 2x, the mean equals ∫₀¹ M(x)·3(1 − 2x)² dx = −3∫₀¹ t² ln(t⁴ − t² + 1) dt. This is the Haar average of M under the source's (C1) and the Page distribution P(x) = 3(1 − 2x)² of the Schmidt weight. The density (C5) is the push-forward of that distribution.
- The same primitive also gives the normalization ∫ P = 1, through H(y) = t₋(y)³ − t₊(y)³.

**Open.**
- The Haar mean of NN for more than two qubits, for which the source has no formula of the type (C1).
- Closed forms for the higher moments of y, for example ∫ y² P(y) dy.

**Effect on the paper.** The closed form asked for in §III and Appendix C is 10/3 − π, which replaces the numerical ≈ 0.1917.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
