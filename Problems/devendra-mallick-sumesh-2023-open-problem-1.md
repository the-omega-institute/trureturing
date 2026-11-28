---
slug: devendra-mallick-sumesh-2023-open-problem-1
bibkey: devendra2023mapping
doi: 10.1007/s11117-022-00956-4
url: https://arxiv.org/abs/2105.14991v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted
  - D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_indecomposable_kEB
---

# Devendra–Mallick–Sumesh Open Problem 1

## Problem

“Is every 2-EB map Φ : 𝕄₍d₁₎ → 𝕄₍d₂₎ decomposable?” The question is Open Problem 1 in §7 of *Mapping cone of k-entanglement breaking maps* (Positivity 27, article 5), p. 26 of the versioned author text. The input and output dimensions are independently positive integers. The maps are complex-linear on the full complex matrix algebras. [Source and predicate locators](../Library/Resource/devendra2023mapping.md)

Definition 3.1 requires positivity of the left amplification idₖ ⊗ Φ and separability of its output for every positive semidefinite input. The amplification acts on the matrix blocks in product-index order. The separable cone consists of finite sums of Kronecker products of positive semidefinite matrices, including zero. Decomposability means Φ = P + Q, where every positive-size left amplification of P is positive and the same holds for Q composed with transpose on its output.

## Motivation

Decomposability is a restriction on positive maps that can be tested by duality with matrices positive under partial transpose. An affirmative answer would apply that restriction to every map satisfying the paper's 2-entanglement-breaking condition.

## Gap

The search recorded in the tier-3 preregistration found the problem posed in the original paper and still called open in Park's preprint. It checked the 2018 Gaussian construction and later work on qutrit and structured cases. Priority beyond the checked literature is unverified. [Preregistration #34948](https://github.com/the-omega-institute/trureturing/issues/34948)

## Route

For a traceless Hermitian matrix H in input-first product order, use W = I − (16/d)H as the Choi matrix and ρ = (I + H/(4d))/d² as the trace-one test matrix. The bound |v*Hv| ≤ d/(32k) for unit vectors of Schmidt rank at most k makes the k-dimensional input compressions of W separable. Rectangular local congruences and finite rank-one decomposition extend this to every positive semidefinite amplified input. If ρ and its output partial transpose are positive semidefinite and Tr(H²) ≥ d⁴/2, then Re Tr(Wρ) ≤ −1. The pairing is nonnegative for the Choi matrix of any decomposable map.

The finite sign cube uses zero diagonal and upper entries (3/5)(±1 ± i), with Hermitian conjugation below the diagonal. Its fixed energy and net bounds for the Schmidt-rank test and both operator tests imply that the union of the three failure events has measure less than one. A single sign assignment therefore satisfies all the hypotheses. [Construction Blueprint](../Blueprint/D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.md)

## Falsifier

At k = 2 and d₁ = d₂ = 4,194,304, the same complex-linear map satisfies the complete 2-EB predicate and violates decomposability. The existential counterexample instantiates the independent input and output dimensions of the universal claim and yields its literal negation. [Refutation Blueprint](../Blueprint/D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.md)

## Evidence

The settling declaration is `devendraMallickSumesh_openProblem1_refuted : ¬ claim`. Its declaration statement ID is `sha256:6ad2843317017ec478bd9023c3f85604d4075c2ac55d33ccbaa16f6259c670b6`. The family theorem `exists_indecomposable_kEB` has declaration statement ID `sha256:23e9b00d0eae941f7210de67ec66b3b82bb7f7df9e3e4784404367688443557e`. The axiom closure of both endpoints is `propext`, `Classical.choice`, and `Quot.sound` on pinned official Mathlib. [Refutation freeze](../Golden/Frozen/state/D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.lean.json) · [Family freeze](../Golden/Frozen/state/D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.lean.json)

The scoped registration evidence validates `candidate_trace_bound` with an unknown residual. The designated refutation is exempt. The other 52 public theorem or lemma registrations are unfinished. [§3.9 disclosure and missing evidence](https://github.com/the-omega-institute/trureturing/issues/34948#issuecomment-7230742748)

## Triage

Tier 3, preregistered in #34948. Open Problem 1 is refuted by `devendraMallickSumesh_openProblem1_refuted`. The stronger family is proved by `exists_indecomposable_kEB` for every natural k ≥ 2 and every natural d ≥ 524,288 k³. `finiteSignSample_unconditional` supplies the same-sample Choi witness at that threshold.

### What the settlement shows

- `candidate_isKEB` and `candidate_indecomposable` show how all required local compressions can be separable while one global PPT test separates the map from the decomposable cone.
- The paper's §7 cites decomposability of 2-positive maps when d₁d₂ ≤ 6. That range also gives decomposability for 2-EB maps by Definition 3.1. The least square counterexample dimension and sharp growth in k remain open here.
- Theorem 7.1 assumes an affirmative answer. Its proof uses decomposability of Γ ∘ Φ for positive Γ and a PPT 2-EB map Φ. The present settlement leaves the square-composition conclusion for PPT 2-EB maps unresolved. [Author text, §7](https://arxiv.org/html/2105.14991v2#S7)

## ASSUMED-UNVERIFIED

The preregistration records the literature search scope. The least counterexample dimension, optimal threshold in k, and unconditional square-composition statement from Theorem 7.1 remain open here.
