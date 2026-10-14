---
slug: milne-jennings-jevtic-rudolph-2014-chsh-centre-bound
bibkey: milne2014fullyentangledfraction
doi: 10.1103/PhysRevA.90.024302
url: https://arxiv.org/abs/1404.3951v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.result
---

# CHSH nonlocality is tightly bounded by the steering-ellipsoid centre

## Problem

A. Milne, D. Jennings, S. Jevtic and T. Rudolph, *Quantum correlations of two-qubit states with one maximally mixed marginal*, Phys. Rev. A **90**, 024302 (2014), arXiv:1404.3951v2, define the CHSH nonlocality in §II as β(ρ) = max_B |tr(ρB)|, with B = α·σ ⊗ (β + β′)·σ + α′·σ ⊗ (β − β′)·σ and the maximum over all directions α, α′, β, β′. §V, Conjecture 1:

> Let ρ be a general two-qubit state with E centred at c. The CHSH nonlocality is tightly bounded as β(ρ) ≤ max[2√(2(1 − c)), 2].

Here E is Alice's steering ellipsoid and c = |c⃗| is the length of its centre. The verbatim statements and the centre convention are in [the literature note](../Library/QuantumBounds/milne2014fullyentangledfraction.md). The repository settled Conjecture 2 of the same paper in [the fully-entangled-fraction dossier](milne-jennings-jevtic-rudolph-2014-fully-entangled-fraction.md).

Issue [#16558](https://github.com/the-omega-institute/trureturing/issues/16558) fixes the reading:
- β is the supremum of |tr(ρB)| over four unit vectors of ℝ³;
- the centre is the companion module's `centre`: (a − Tb)/(1 − |b|²) for |b| ≠ 1 and a for |b| = 1.

The conjecture is proved in this form. "Tightly bounded" is proved as a supremum at every centre length t ∈ [0, 1]: for every ε > 0 some state with c = t has β > max(2√(2(1 − t)), 2) − ε.

## Motivation

The paper proves the bound only for canonical states, whose Bob marginal is maximally mixed (Theorem 1). §V explains why that does not extend: CHSH nonlocality does not transform simply under the local filtering that makes a state canonical. The bound turns the centre of the steering ellipsoid, a geometric quantity, into a sharp limit on Bell violation for every two-qubit state.

## Gap

Issue #16558 records the literature check before any Lean:
- arXiv v2 and the published version state Conjecture 1;
- Milne's 2016 PhD thesis (Imperial College London, DOI 10.25560/44111, read in full) restates it, still open, as Conjecture 6.4, supported by 10⁵ random states;
- A. F. Ducuara, C. E. Susa and P. Skrzypczyk, Phys. Rev. A **110**, 022435 (2024), arXiv:2406.03945, state that the centre bounds lack an analytical proof;
- searches of arXiv, journals, Zenodo and SSRN found no proof or refutation.

`not-found-in-searched-scope`.

## Route

Write M(ρ) for the largest value of |Te₁|² + |Te₂|² over orthonormal pairs, where T is the correlation matrix, and Δ(X) = tr X² − tr (tr_B X)².
1. **CHSH to a plane.** For unit b, b′ write b ± b′ = r e₁, s e₂ with e₁ ⊥ e₂ and r² + s² = 4. Cauchy–Schwarz gives |tr(ρB)| ≤ 2√(|Te₁|² + |Te₂|²).
2. **CHSH–purity.** With n = e₁ × e₂ and the flipped state ρ̃ₙ = (σ_y ⊗ (n·σ)σ_y) ρᵀ (σ_y ⊗ (n·σ)σ_y)*, the identity |Te₁|² + |Te₂|² + (b·n)² + 2 Re tr(ρρ̃ₙ) = 1 + 2Δ(ρ) holds. Since ρ̃ₙ ⪰ 0, the plane sum is at most 1 + 2Δ(ρ).
3. **Filtering covariance.** Δ((I ⊗ F)X(I ⊗ F)*) = |det F|² Δ(X) for every Hermitian X and every 2 × 2 F, by the polarization tr(AB) − tr A tr B = det A + det B − det(A + B) on 2 × 2 blocks.
4. **Canonical purity.** A canonical state σ with |a(σ)| = c satisfies σ ⪯ (1 − c/2)I (the companion's `canonical_bound`), hence Δ(σ) ≤ 1/2 − c.
5. **Canonicalization.** For |b| < 1, an explicit 2 × 2 Cholesky factor F of 2ρ_B makes σ = (I ⊗ F⁻¹)ρ(I ⊗ F⁻¹)* canonical, with a(σ) = c⃗ and |det F|² = 1 − |b|². For |b| = 1, ρ_B is a projector and Δ(ρ) = 0.
6. **Assembly.** M(ρ) ≤ 1 + (1 − |b|²)(1 − 2c) ≤ max(2(1 − c), 1), so β(ρ) ≤ 2√max(2(1 − c), 1) = max(2√(2(1 − c)), 2).
7. **Tightness.** The states R(t, s) = ½|v⟩⟨v| + t(1 − s)/2 |01⟩⟨01|, with v = √(1 + s)|00⟩ + √((1 − t)(1 − s))|11⟩, have centre (0, 0, t) for s < 1.
   - For t ≤ 1/2, s = 0 with the standard CHSH directions gives 2√(2(1 − t)).
   - For 1/2 < t < 1, s = 2/(2 + ε) with all directions along z gives more than 2 − ε.
   - For t = 1, the state |00⟩⟨00| gives 2.

## Falsifier

The proof would not settle the conjecture if:
- the module's β differed from §II's maximum over directions;
- its centre differed from the steering-ellipsoid centre;
- its tightness statement were weaker than the source's "tightly bounded".

The module's `chsh` is the supremum of |tr(ρ · bell a a′ b b′)| over unit a, a′, b, b′, which is §II's definition. `centre` is the companion's, frozen with Conjecture 2 under the same convention. The second conjunct of `claim` gives, at every centre length, states whose β comes arbitrarily close to the bound. Attainment at every t would be false: for 1/2 < t < 1 the bound is approached but not attained.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.lean` (743 lines).
- It defines `bell`, `chshValues`, `chsh`, `bound` and `claim`, and proves `result : claim`. Two-qubit matrices are the frozen `CHSHWitness.TwoQubitMatrix`, and the spin operators α·σ are the frozen `spin` of `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness`.
- It reuses the frozen companion `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction`: `pauli`, `blochA`, `blochB`, `corr`, `vlen`, `centre` and `canonical_bound`, together with the canonicalizing filter `canonical_filter`, `canonical_trace` and the Bloch and trace lemmas that this delivery makes public there. It also reuses the qubit purity identity `matrix_energy` of `D5/S3/Quantum/Information/ActualPureQubitCostInfimum` and `det_bloch` and `pure` of `D5/S3/Quantum/Information/ActualQubitChordObstruction`, both extracted here from local steps of their owners. Further dependencies are the frozen partial traces of `D5/S3/Quantum/Information/PartialTraceMutualInformation`, `pauli_hermitian` from `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation`, and pinned Mathlib.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.lean` reads out the bound function `bound` of `claim`. Its rejected realization, the constant 2, fails because the tightness conjunct at t = 0 gives a state with β > 2. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.lean.json`, statement `sha256:4b476770868684c36d467552a89a9adc4384fa4c118363bc53ba9bd03eec3e0f`.

Declaration statements:
- `result`: `sha256:b0c949d50db4c960afdfac8ba1cd5ed034a779cb1176d9fc644a558d1e6a7b43`;
- `claim`: `sha256:abdf7765e888d4366a59fc61fddfae1ffb370270b8cc8ad62ba52a3fc2ed859e`.

## Triage

Tier 1 conjecture of a 2014 paper, preregistered in issue #16558 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the plane reduction, the flip identity, the filtering covariance, the canonical bound and the tightness family are instantiations of frozen and pinned Mathlib results followed by normalization | open-problem-resolution |
| the plane, purity, filtering, canonicalization and tightness helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:**
- β(ρ) ≤ max(2√(2(1 − c)), 2) for every two-qubit density matrix;
- for every t ∈ [0, 1], the bound is the supremum of β over states with centre length t.

**Proved on the way, not public.** The private lemmas `planeSum_le_purity`, `delta_le_centre` and `chsh_le_of_plane_bound` combine, inside the proof of `result`, into the stronger inequality β(ρ) ≤ 2√(1 + (1 − |b|²)(1 − 2c)). It depends on the Bloch length |b| of Bob's marginal as well as on c. At |b| = 0 it is the canonical bound s₁² + s₂² ≤ 2(1 − c) of the paper's Theorem 1.

**Computed, not formalized** (orchestrator, 14 October 2026; NumPy, random complex-Wishart states of every rank):
- over 400 local maximizations of M − max(2(1 − c), 1), the maximum is 1.1 × 10⁻¹⁵ at c = 0.229, so the bound is tight in the interior;
- control: without the max(…, 1) branch the same optimizer finds violations of size 0.999;
- over 2 × 10⁵ states, the maximum of M − (1 + (1 − |b|²)(1 − 2c)) is 2.7 × 10⁻¹⁵.

**Argued, not formalized.**
- The bound is attained exactly when t ∈ [0, 1/2] ∪ {1}. For 1/2 < t < 1 the stronger inequality gives M < 1 unless |b| = 1, and |b| = 1 forces a product state with M = c² < 1, so 2 is not attained.

**Open.**
- The F₃-steering half of the conjecture used by Ducuara–Susa–Skrzypczyk 2024: that the maximal violation of the F₃ steering inequality is bounded by a function of the centre length alone.
- Bounds on β by the full steering ellipsoid (semiaxes and centre together) rather than by the centre alone.

**Effect on the paper.**
- Conjecture 1 holds, and so does Conjecture 6.4 of Milne's thesis, which restates it. The bound of the paper's Theorem 1 for canonical states is the case |b| = 0 of the stronger inequality.
- The abstract of Ducuara–Susa–Skrzypczyk 2024 states that their criterion for locally inaccessible hidden correlations relies on two centre bounds, for the CHSH and the F₃ inequalities. The CHSH bound is now proved; the F₃ bound is not addressed here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. Xing–Yang, Phys. Scr. **101**, 135103 (2026), give volume-based bounds; their full text was not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
