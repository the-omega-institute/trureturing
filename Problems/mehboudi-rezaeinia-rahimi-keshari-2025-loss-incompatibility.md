---
slug: mehboudi-rezaeinia-rahimi-keshari-2025-loss-incompatibility
bibkey: mehboudi2025lossincompatibility
doi: 10.1103/s9sp-2fd7
url: https://arxiv.org/abs/2411.05920v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/PureLossIncompatibility.result
---

# n + 1 displaced on-off measurements stay incompatible under pure loss of transmissivity 1/n

## Problem

M. Mehboudi, F. Rezaeinia and S. Rahimi-Keshari, *Measurement incompatibility under loss*, arXiv:2411.05920v3 (Phys. Rev. Lett. 135, 100202 (2025)), model pure loss by a beam splitter of transmissivity τ with vacuum in its second input, E_τ(ρ) = tr₂(U_BS(ρ ⊗ |0⟩⟨0|)U_BS†), and define the dual by tr(M E_τ(ρ)) = tr(ρ E*_τ(M)). Result 2 shows that for τ ≤ 1/n the images under E*_τ of any n measurements are jointly measurable. Result 3 asserts that some n + 1 measurements stay incompatible at τ = 1/n: "We prove this result numerically for 2 ≤ n ≤ 13, and conjuncture it to hold for arbitrary n." The measurements are the displaced on-off detections of Eq. (4), M^k_1 = |μ_k⟩⟨μ_k| and M^k_2 = I − M^k_1, with coherent states of equal modulus separated by the phase 2π/(n + 1). The verbatim statements are in [the literature note](../Library/QuantumBounds/mehboudi2025lossincompatibility.md).

Issue [#15985](https://github.com/the-omega-institute/trureturing/issues/15985) fixes the reading. For every n ≥ 1 there are n + 1 binary POVMs on the single-mode Fock space ℓ²(ℕ) whose images under E*_{1/n} have no parent POVM. A parent ranges over all 2^{n+1} outcome strings and has exactly the given effects as marginals.

The Lean statement takes E*_τ in the source's own form: N is the image of M when tr(M E_τ(|ψ⟩⟨ψ|)) = ⟨ψ, N ψ⟩ for every ψ. Here E_τ(|ψ⟩⟨ψ|) = tr₂(U_BS(|ψ⟩⟨ψ| ⊗ |0⟩⟨0|)U_BS†) is built from the frozen beam splitter and partial trace, and the trace is the Fock-basis sum. Pure states determine an operator, so this relation determines E*_τ(M). The statement asserts both that such images exist and that no family of them has a parent.

## Motivation

Loss is the dominant noise in optical quantum communication. Result 2 shows that transmissivity 1/n destroys the incompatibility of every n measurements, and so every steering test built from n settings. Result 3 says that one more setting always survives the same loss. Together they would make 1/n a sharp threshold, and they rest the sharpness on displaced on-off detectors, which are standard laboratory equipment.

## Gap

Issue #15985 records the literature check before any Lean:
- arXiv v3 is the latest version and states the conjecture;
- the one citing work found (arXiv:2509.10381) cites the paper for loss robustness only;
- the related works checked (arXiv:1704.05734, 2403.14785, 2407.07711, 2605.18243, 2605.21245, 2606.08189, 2610.06642) do not give the sharp setting count;
- the source's own unambiguous-discrimination argument (Result 4) needs (n + 1)! > nⁿ at m = n + 1, τ = 1/n, which holds only for n ≤ 2;
- Zenodo, Crossref and web searches return no settlement.

`not-found-in-searched-scope`.

## Route

Let m ≥ 2, 1/m < τ ≤ 1 and Δ = mτ − 1. Take distinct unit phases z_1, …, z_m, put Q = Σ_{i<j} |z_i − z_j|^{−2}, x = Δ/(2(m + 4Q)) and μ_j = √x z_j.
1. **Compression.** Compress every effect to span{|0⟩, |1⟩}. This is exact for the vacuum and one-photon inputs of the beam splitter, preserves positivity and sums, and so sends a parent on ℓ² to a parent of the 2 × 2 compressions. With A = e^{−x}, the compressed click effect of E*_τ(I − |μ_j⟩⟨μ_j|) is C_j = [[a, −b z̄_j], [−b z_j, c]], where a = 1 − A, b = √τ A √x and c = 1 − A(1 − τ + τx).
2. **Scalars.** δ := c − b²/a satisfies 0 ≤ δ ≤ a ≤ x, and c ≥ τ − x.
3. **Common subeffects.** If 0 ≤ H ≤ C_i and H ≤ C_j, then evaluating the quadratic forms at u_j = ((b/a) z̄_j, 1) gives |z_i − z_j|² H₁₁ ≤ 4δ ≤ 4x.
4. **Counting.** For a parent (G_S) indexed by click sets S, with g_S = (G_S)₁₁: Σ g_S ≤ 1, mc = Σ |S| g_S, and |S| ≤ 1 + C(|S|, 2). Summing the pair bounds gives mc ≤ 1 + 4xQ. But mc − 1 − 4xQ ≥ Δ − x(m + 4Q) = Δ/2 > 0.

Result 3 is the case m = n + 1, τ = 1/n and z_j = e^{2πij/(n+1)}.

## Falsifier

The settlement would fail if the trace relation in `IsLossDual` did not define the source's E*_τ, for instance if the beam splitter kept the reflected mode (amplitude √(1−τ)) or used a non-vacuum environment, or if `HasParent` dropped outcome strings or allowed approximate marginals. The module proves that the Stinespring form V†(M ⊗ I)V satisfies that relation and is the only operator that does. It also proves the compressed click matrix from the frozen beam splitter's Fock action, so its entries carry √τ. `HasParent` requires exact marginals over all outcome strings. The claim also fails if the construction degenerates: x > 0 needs mτ > 1, and Q > 0 needs distinct phases. Both are proved, including at n = 1, where τ = 1.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/PureLossIncompatibility.lean` (954 lines).
- Public declarations: `H` (the frozen `FockSpace`), `K`, `Op`, `amplify`, `vacuumEmbedding`, `stinespring`, `dualLoss`, `IsLossDual`, `IsBinaryPOVM`, `HasParent`, `inverseTransmissivity`, `claim` and `result`.
- It reuses frozen declarations:
  - `beamSplitter`, `tensor`, its Fock action `beamUnitary_fock` and `coherent` (`FockAttenuator/BeamSplitter`);
  - the pure-state partial trace `purePartialTrace` (`FockAttenuator/DisplacementCovariance`);
  - `coherentDensity` (`FockAttenuator/Attenuator`), whose `trace_one` gives the unit norm of coherent states;
  - the Fock basis `e` and the compression `compression` (`TransmissivityBetaPriorProbeRefutation`);
  - `fockPair_apply` (`FiniteFockBeamSplitterNonExtremality`, made public here);
  - `IsPOVM` (`ConcealmentKernelNecessityRefutation`).
- It also uses Mathlib's `lp`, adjoints, `Finset.card_product_filter_lt` and `Circle.exp_injOn_Ico`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration `Reg/D5/S3/Quantum/Measurement/PureLossIncompatibility.lean` (template `DependentFamily.realize`, readout the binary effect M b of each measurement; the rejected realization returns the identity for both outcomes, which violates binary normalization since I + I ≠ I) is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/PureLossIncompatibility.lean.json`, statement `sha256:0f55391b8e5da52873d52a827a7857946e3036fc19547493412707b74ff3edec`.

Declaration statements:
- `result`: `sha256:85d853dd71cd8fb2cf913d845f502053ae0e14efa15d981101222298d752122e`;
- `claim`: `sha256:3263b3984a4574d057da3f214b45626503c168cdb0931c3fd236b02c6c4654c8`.

## Triage

Tier 1 conjecture of a 2025 paper, preregistered in issue #15985 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every other declaration is a definition used by `claim` or a private helper on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every n ≥ 1, the n + 1 displaced on-off measurements with regular phases e^{2πij/(n+1)} and squared amplitude x = Δ/(2(m + 4Q)), where m = n + 1, Δ = mτ − 1 and Q = Σ_{i<j} |z_i − z_j|^{−2}, have images under E*_{1/n}. No family of these images has a parent. The case n = 1 (τ = 1, two measurements, no loss) is included.

**Established inside the proof.**
- For every m ≥ 2, 1/m < τ ≤ 1 and distinct unit phases, the displaced on-off measurements with x = Δ/(2(m + 4Q)) are incompatible after E*_τ.
- The Stinespring form V†(M ⊗ I)V satisfies the source's trace relation tr(M E_τ(|ψ⟩⟨ψ|)) = ⟨ψ, N ψ⟩ and is the only operator that does.
- The compression to span{|0⟩, |1⟩} is exact for the pure-loss dual of these effects, and any parent compresses to a 2 × 2 parent.
- Any common subeffect of two compressed clicks has (1,1) entry at most 4x/|z_i − z_j|², and every parent satisfies mc ≤ 1 + 4xQ. (The sharper constant δ = c − b²/a ≤ x in place of x follows from the same quadratic-form argument; that specialization is not on the proof path.)

**Computed.** For regular phases, Q = m(m² − 1)/24, by the identity Σ_{k=1}^{m−1} csc²(πk/m) = (m² − 1)/3 (checked numerically for m ≤ 11). At m = n + 1 and τ = 1/n this gives Δ = 1/n and the closed form x = 3/(n(n + 1)(n² + 2n + 6)), which rests on that identity and is not formalized. It reproduces the values 1/28, 1/84, 1/200, 1/410 and 1/756 of the preregistration table for n = 2, …, 6. With the source's fixed amplitude r = 0.015 instead, the sufficient condition r²(m + 4Q) < Δ used here holds exactly for n ≤ 11. The proof therefore lets the amplitude shrink with n; whether r = 0.015 itself fails for large n is not decided.

**Argued, not formalized.**
- *The sharp threshold.* Combined with the source's Result 2, which this module does not formalize, the private theorem gives the exact threshold for m settings. Every m measurements become compatible when τ ≤ 1/m, and some m displaced on-off measurements stay incompatible for every τ > 1/m. This is stronger than Result 3: it allows any τ above 1/m, not only 1/(m − 1).
- *The mechanism.* After compression each click effect carries weight c ≈ τ on the one-photon level, so the m clicks together ask for mτ > 1 of a unit budget. A parent can pay for this only through outcomes that click on several settings at once. Distinct phases make every pairwise overlap at most of order x/|z_i − z_j|², and small x makes the total overlap negligible. Incompatibility is therefore a weak-field effect, with r = √x of order √3/n². The proof is the analytic counterpart of the source's own method, which also projects the effects onto the qubit subspace d = 2 and tests them with an SDP; the source fixes r = 0.015 there.
- *Robustness.* The margin mc − 1 − 4xQ ≥ Δ/2 = 1/(2n) shrinks with n. The preregistration's SDP readings show the same trend: the largest visibility admitting a parent is t* = 0.918, 0.981, 0.995, 0.998 and 0.9992 for n = 2, …, 6. The theorem gives incompatibility, not a robustness value.

**Open.**
- The optimal amplitude r, the exact incompatibility robustness of the n + 1 settings at τ = 1/n, and whether a fixed amplitude works for every n.
- Whether the same threshold 1/m holds for measurements with more outcomes or for multimode loss.

**Effect on the paper.** Result 3 holds for every n, not only 2 ≤ n ≤ 13 (or 14), and its construction is the paper's own displaced on-off family. The paper's statement that n + 1 measurements stay incompatible for τ ≥ 1/n follows for every n ≥ 1.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
