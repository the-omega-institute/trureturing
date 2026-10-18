---
slug: mukhopadhyay-sazim-pati-2018-qutrit-magic-coherence-bound
bibkey: mukhopadhyay2018coherencemagic
doi: 10.1088/1751-8121/aac8e8
url: https://arxiv.org/abs/1801.04807v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/QutritMagicCoherenceBound.result
---

# A coherence lower bound on the magic of pure qutrits

## Problem

C. Mukhopadhyay, S. Sazim and A. K. Pati, *Coherence makes quantum systems 'magical'*, J. Phys. A 51, 414006 (2018), arXiv:1801.04807v3, Eq. (18), stated from numerical simulation:

> The following condition on quantum coherence, quantified via the $l_1$-norm, and 'magic', quantified by the sum negativity, holds for qutrit pure states $M_{SN}[|\psi\rangle] \geq \frac{C_{l_{1}}[|\psi\rangle]}{2}\sqrt{1- \frac{C_{l_{1}}[|\psi\rangle]}{2}}$

Here $M_{SN} = \sum_u |W_u| - 1$ for the discrete Wigner function $W$ of the paper's Eq. (12), and $C_{l_1}$ is the sum of the moduli of the off-diagonal entries. The verbatim statements are in [the literature note](../Library/QuantumChannels/mukhopadhyay2018coherencemagic.md).

Issue [#18729](https://github.com/the-omega-institute/trureturing/issues/18729) fixes the reading: the bound for every normalized x ∈ ℂ³ with ρ = x x†. This is proved.

## Motivation

The sum negativity is a magic monotone for odd dimensions, and incoherent states are stabilizer states. Eq. (18) asks how much coherence forces magic in the smallest odd dimension.

## Gap

Issue #18729 records the literature check before any Lean:
- arXiv v3 is the latest version and keeps Eq. (18) without proof;
- five citing works were read in the cited passages, and two more are reported by the proof seat; none proves Eq. (18). The 2026 citing paper of Zhang–Luo–Zhang was read only in its abstract;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Write r_j = |x_j|, s = r₁r₂ + r₁r₃ + r₂r₃ = C/2, v = 1 − s, δ_i = r_i² − r_j r_k and D = Σ_i max(−δ_i, 0).
1. **Positive and negative parts.** For three reals with positive mass P and negative mass N, the sum of squares is at most P² + N².
2. **One column.** Each column of 3W has sum 3A and sum of squares 3A² + 6R², with A = r_i² and R = r_j r_k. Its negative mass is therefore at least √3·max(R − A, 0).
3. **The amplitude defect.** Σδ_i = v and Σδ_i² = 1 − s², so D² + vD ≥ sv.
4. **The constant.** A square identity gives D ≥ (√3/2) s √v.
5. **Conclusion.** M = (2/3)·(negative mass of 3W) ≥ (2/√3) D ≥ s√v = (C/2)√(1 − C/2).

## Falsifier

The theorem would not settle the question if the module's quantities differed from the source's. The module takes:
- the nine Wigner entries exactly as printed, with λ₁ + iμ₁ = ρ₁₂, λ₂ + iμ₂ = ρ₁₃, λ₃ + iμ₃ = ρ₂₃, in zero-based indices;
- the sum negativity of Eq. (13);
- the l₁ coherence of `CorrelatedCoherenceMonogamyRefutation` and the rank-one density of `PureStateHandshake`.

## Evidence

The canonical source is `D5/S3/Quantum/Information/QutritMagicCoherenceBound.lean` (258 lines).
- **Definitions.** It defines `wigner`, `sumNegativity` and `claim`, and proves `result : claim`.
- **Reuse.** It reuses `PureStateHandshake.rankOneDensity`, `CorrelatedCoherenceMonogamyRefutation.l1Coherence` and Mathlib's positive-part lemmas.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registration:** `Reg/D5/S3/Quantum/Information/QutritMagicCoherenceBound.lean` (`result`, `declared_validated`).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/QutritMagicCoherenceBound.lean.json`, statement `sha256:9590a4cb5b40feb704e7cff10f72499ce3921cee6725839d9a53eed5b3c44b0a`.

Declaration statements:
- `result`: `sha256:551cbc62424984cf114d1b63e098496b8e9ef32bf5ca38e7db6e6fb3bc252a8a`;
- `claim`: `sha256:8b8939dbd3ddb671a6d5fa244d7eee69d2022fb74efbd1be370b986f9178203b`.

## Triage

Tier 1 conjecture of a 2018 paper, preregistered in issue #18729 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the moment bounds, the defect identity and the square identity are instantiations of existing lemmas and polynomial normalization | open-problem-resolution |
| `wigner`, `sumNegativity`, `claim` | bind-only | none | definitions used by `claim` |
| the moment, defect and column helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The module is a general theorem over all pure qutrit states, so `utility` is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Eq. (18) holds for every pure qutrit state.

**Computed, not formalized** (orchestrator, recorded in #18729): over 200 000 random pure states the minimum of M − (C/2)√(1 − C/2) is about 10⁻⁷, reached only near C = 2.

**Argued, not formalized.**
- *Equality and strictness.* Equality holds at the incoherent state (1, 0, 0) and at the maximally coherent stabilizer state (1, 1, 1)/√3. For 0 < C < 2 the inequality is strict (the proof seat's lemma L7).
- *Mechanism.* Magic is forced by an imbalance of the amplitudes. If the product of two amplitudes exceeds the square of the third, r_j r_k > r_i², then the Wigner column of the i-th diagonal entry has a negative entry, whatever the phases; this is a sufficient condition, and phases can produce negativity without it. The quantity D measures that imbalance, and the bound is the sharp consequence of two moment identities: one for each Wigner column, one for the defects δ_i.
- *Scope.* The proof uses purity through |ρ_jk| = r_j r_k, and the bound fails for mixed states: the mixture ½|+⟩⟨+| + ½|0⟩⟨0| of two stabilizer states, with |+⟩ = (1, 1, 1)/√3, has C = 1 and a nonnegative Wigner function, so M = 0 < (1/2)√(1/2).
- *The second conjecture.* The paper's trade-off for qutrit–qubit states, 16E² + 9M² < 4 (Eq. (19)), is not addressed. With any standard normalization of the negativity E, the embedded Bell state (|00⟩ + |11⟩)/√2 has an incoherent reduced qutrit state (M = 0) and 16E² ≥ 4, so the strict inequality fails there; whether the non-strict form holds is not determined here.

**Effect on the paper.** The numerically observed coherence bound for pure qutrits is a theorem.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The full text of the 2026 citing paper of Zhang–Luo–Zhang was not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
