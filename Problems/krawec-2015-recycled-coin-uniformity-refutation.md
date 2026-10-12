---
slug: krawec-2015-recycled-coin-uniformity-refutation
bibkey: krawec2015history
doi: 10.1016/j.physa.2015.02.061
url: https://arxiv.org/abs/1411.6298v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result
---

# A resonant memory parameter refutes Krawec's recycled-coin uniformity conjecture

## Problem

W. O. Krawec, *History dependent quantum walk on the cycle with an unbalanced coin*, Physica A
428 (2015), arXiv:1411.6298v1, studies a two-coin walk on the d-cycle.
- The coin flip applies C(π/4) or C(π(1+φ)/4) to the second coin according to the first coin.
- The second coin moves the walker one step left or right.
- The coins are then swapped.

The memory parameter is φ ∈ [0, 8). §III.B and §IV conjecture, from numerics for d ≤ 300 on the grid φ = m/10, that the time-averaged position distribution is uniform for every φ outside E_d. Here E_d = {0, 2, 4, 6} if 12 ∤ d and E_d = {0, 1, 2, 4, 5, 6} if 12 ∣ d. The source states it for every initial coin state at position 0. The verbatim statements are in [the literature note](../Library/QuantumChannels/krawec2015history.md).

Issue [#15747](https://github.com/the-omega-institute/trureturing/issues/15747) fixes the reading: d ≥ 2, every unit coin α ∈ ℂ⁴ at position 0, and the Cesàro averages over times 1 … T converging to 1/d.

## Motivation

The paper uses the time-averaged distribution to classify the walk's behaviour by memory parameter, initial state and cycle size. It names the conjecture an open problem. If the conjecture held, only the integer parameters φ = 0, 1, 2 would need further study.

## Gap

Issue #15747 records the literature check before any Lean:
- arXiv lists only v1;
- the four citing works found by Semantic Scholar either use the walk for random-number generation (arXiv 2207.08973, 2102.02252) or for key distribution (arXiv 1710.07979), or predate the paper (arXiv 1301.2905). None treats the limiting distribution at non-integer φ;
- Zenodo, Crossref, google-deepmind/formal-conjectures and web searches return no settlement;
- the repository had no related result.

`not-found-in-searched-scope`.

## Route

Fix d = 12, a = √2/2, κ = (√5 − 1)/2, c = aκ, θ = arccos c and φ★ = 4θ/π − 1 ≈ 0.4241.
1. **Parameter.** 2a² = 1, κ² + κ = 1 and 0 < c < a give π/4 < θ < π/2, so 0 < φ★ < 1 and φ★ ∉ E₁₂. The resonance identity c² + ac = 1/2 holds.
2. **Modes.** On a spatial mode n ↦ χ(n)·u, with χ a character of ℤ/12, one step of the walk acts by a 4 × 4 block B(χ(1)).
   - For the trivial character and for the momentum-2 character (χ(1) = e^{iπ/3}), the resonance gives a common eigenvalue λ with |λ| = 1.
   - Division-free identities give explicit eigenvectors, with a nonzero coin overlap.
3. **Limit.** The mean ergodic theorem for the conjugation isometry A ↦ U A U* on the Hilbert–Schmidt space gives convergence of the Cesàro averages of the return probabilities.
   - The fixed space contains the rank-one cross term built from the two resonant eigenvectors.
   - Its projection makes the summed limit over the four computational-basis coins strictly larger than 4/12, so some basis coin has a limit larger than 1/12.

## Falsifier

The refutation would fail if the conjecture were read only on the source's grid φ = m/10: φ★ ≈ 0.4241 is not a grid value, and the grid value φ = 1.3 at d = 12 is uniform (to within 6·10⁻¹⁵ numerically).

φ★ is moreover irrational (argued, not formalized; `result` does not use it).
- cos 2θ = 2c² − 1 = (1 − √5)/2, so 2cos 2θ = 1 − √5 is an algebraic integer whose conjugate 1 + √5 exceeds 2.
- For rational r, every conjugate of 2cos(rπ) is again of the form 2cos(r′π) and lies in [−2, 2].
- Hence 2θ/π is irrational, and so is φ★ = 4θ/π − 1.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.lean` (954 lines).
- Public declarations: the model definitions (`angle`, `coinFlip`, `shift`, `swap`, `U`, `initial`, `p`, `avg`, `exceptional`, `unitCoin`), `claim` and `result`.
- It reuses the frozen coin matrix `FreeSpectrahedronFeasibilityWitness.X3` and the frozen character `FinitePoisson.character`.
- It uses Mathlib's mean ergodic theorem (`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`), the golden-ratio identities, and the additive characters of `ZMod`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.lean.json`, statement `sha256:cf8f6a9441961faedaf197035ace1dc88db02b6df98f51952aa1073b2eb7cafe`.

Declaration statements:
- `result`: `sha256:ab06f2fd6bd3163060cb781b343a8c1a5daeef477dd0769f63158b855b263a36`;
- `claim`: `sha256:4fe7e12e1a47ded520a304ffbdaf50d2fe8365b65408d71d799ef4448d7ca38f`.

## Triage

Tier 1 conjecture of a 2015 paper, preregistered in issue #15747 before any Lean, with the witness fixed in its comment before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every private declaration is bind-only and lies on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」); the module's comment block lists each with its consumer. Utility is `certified-instance` with basis `refutes` of `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the conjecture is false. At d = 12 and the non-integer φ★ ∉ E₁₂, some computational-basis coin at position 0 has a return average converging to a value larger than 1/12.

**Established inside the proof.** The Cesàro averages of the return probabilities converge for every basis coin. A shared eigenvalue between the trivial and the momentum-2 Fourier blocks, with nonzero coin overlap, produces a strictly positive surplus of the summed limit over 4/12.

**Argued, not formalized.**
- The resonance mechanism gives a family. For every d ≥ 12 the parameter φ_d = 4·arccos(c_d)/π − 1, with c_d = (√2/2)(−h + √((1−h)(3−h))) and h = cos(2π/d), lies in (1, 2). By the same argument with momentum 1, it gives a non-uniform return average. Hence both branches of the conjecture fail, for 12 ∤ d as well.
- NumPy readings, recorded in #15747 and its comment:
  - φ_d for d = 12, 13, 14, 24 gives return averages 0.0955, 0.0822, 0.0807, 0.0450 against 1/d;
  - φ★ at d = 24 gives 0.0439 against 1/24;
  - φ★ at d = 13 is uniform.
- Non-uniformity at a non-integer φ comes from two Fourier blocks sharing an eigenvalue with nonzero coin overlap. Such resonant parameters are isolated values that a finite grid such as φ = m/10 need not contain.

**Open.** Whether the time-averaged distribution is uniform for all φ outside E_d and outside the resonant set, i.e. the natural repair of the conjecture, is not decided here.

**Effect on the paper.** The §III.B observation and the §IV conjecture are false as stated: non-integer memory parameters can produce non-uniform time-averaged distributions, in both divisibility branches.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The family statement and the d ≥ 12 readings in "Argued, not formalized" are not formalized.
