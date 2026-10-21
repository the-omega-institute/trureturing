---
slug: berardini-et-al-2024-csst-doubling-map-improvement
bibkey: berardini2025csst
doi: 10.1109/JSAIT.2025.3582156
url: https://arxiv.org/abs/2412.08586v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Codes/CssTDoublingMapImprovement.result
---

# A CSS-T doubling map with better distance than the identity

## Problem

E. Berardini, R. Dastbasteh, J. Etxezarreta Martinez, S. Jain and O. Sanz Larrarte, *Asymptotically good CSS-T codes and a new construction of triorthogonal codes*, arXiv:2412.08586v2, Remark 1:

> Finding maps $\phi$ giving CSS-T codes with better parameters than the choice $\phi=I$ or a permutation is an interesting open question.

For a binary CSS code (C₁, C₂) and a linear map φ on C₁ satisfying the triple-product parity condition of the source's Proposition 1, the CSS-T code (C₁^{Nφ}, C₂^{Nφ}) has C^{Nφ} = {(x, φ(x)) : x ∈ C}. Every such φ gives length 2n and dimension k = dim C₁ − dim C₂. The definitions are quoted in [the literature note](../Library/QuantumContext/berardini2025csst.md).

Issue [#19814](https://github.com/the-omega-institute/trureturing/issues/19814) fixes the reading. The question asks for some CSS code and some admissible φ for which the φ-extension has strictly larger CSS distance than the identity extension. Such a pair is constructed.

## Motivation

The source proves that the identity map turns every [[n, k, d]] CSS code into a [[2n, k, ≥ d]] CSS-T code, which supports a transversal T gate, and uses this to obtain asymptotically good CSS-T codes. It shows that coordinate permutations give the same parameters as the identity. Whether other admissible maps can do better is left open, and arXiv:2507.17611 restates the question for the identity map's optimality.

## Gap

The literature check before any Lean is recorded in #19814:
- the source's Remark 1 and conclusion;
- arXiv:2507.17611, which restates the question;
- the authors' 2025 slides, which list it among further questions;
- the two OpenAlex citing works and two further CSS-T papers, none of which treats alternative maps;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Let A be the 13 × 13 circulant with (Ax)_i = x_i + x_{i+1} + x_{i+2} (indices mod 13).
- **The code.** C₁ = {(x, x) : x ∈ 𝔽₂¹³}, C₂ = {(x, x) : Σ x_i = 0}, so k = 1.
- **The map.** φ(x, x) = (Ax, Ax).
- **Admissibility.** Every vector involved consists of two equal blocks, so every triple product has even weight.

1. **Identity extension.** (e₀, e₀, e₀, e₀) is a logical X operator of weight 4, so its distance is at most 4.
2. **X-distance of the φ-extension.** A logical X operator of the φ-extension is (x, x, Ax, Ax) with x of odd weight. Its weight is 2(wt x + wt Ax) ≥ 8, because A is invertible and wt(Ae_i) = 3.
3. **Z-distance of the φ-extension.** A logical Z operator (a, b, c, d) of the φ-extension satisfies a + b + Aᵀ(c + d) = 𝟏.
   - With w = c + d, its weight is at least wt(w) + 13 − wt(Aᵀw).
   - Since wt(Aᵀw) ≤ 3 wt(w), this is at least 13 − 2 wt(w) ≥ 5 when wt(w) ≤ 4, and at least 5 otherwise.
4. **Conclusion.** The φ-extension has distance at least 5 > 4.

## Falsifier

The construction would not answer the question if the module's admissibility condition or its CSS distance differed from the source's. The module:
- requires φ to be linear on C₁ and to satisfy the source's parity condition for all x, y ∈ C₁ and z ∈ C₂;
- takes the CSS distance as the least weight of C₁ ∖ C₂ and C₂^⊥ ∖ C₁^⊥, as in the source's Theorem 1;
- compares the two extensions of the same pair, so that length and dimension agree.

## Evidence

The canonical source is `D5/S3/Quantum/Codes/CssTDoublingMapImprovement.lean` (500 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Codes/CssTDoublingMapImprovement.lean.json`, statement `sha256:df103087b497b444cb14d857341e50bf32e0beb5d35d2f5d59cc34595cf1e7dc`.

Declaration statements:
- `result`: `sha256:6662389e031520c8adf26fe5d3a2bc2ff8721b6eae9ed57db53800caa06f68d2`;
- `claim`: `sha256:c8da02f58e6da37f62f84f12a5cc662e96e8c7ecf876ac2efc360e3738d12372`.

## Triage

Tier 1 question of a 2024 paper, preregistered in issue #19814 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for the code and map above, φ is admissible, and the CSS distance of the φ-extension is strictly larger than that of the identity extension.

**Computed, not formalized** (orchestrator, exhaustive over 𝔽₂¹³, recorded in #19814):
- the input code is [[26, 1, 2]];
- the identity extension is [[52, 1, 4]] (X-distance 4, Z-distance 13);
- the φ-extension is [[52, 1, 5]] (X-distance 8, Z-distance 5).

**Argued, not formalized.**
- *Mechanism.* The identity extension repeats each logical X operator four times and leaves the Z side untouched, so its distance is limited by the X side. A weight-spreading map φ trades: it raises the X-distance (here 4 → 8) at the cost of the Z-distance (13 → 5), and the balance improves the minimum. A permutation preserves weights on both sides, which is why the source's Proposition 3 finds no gain from permutations.
- *Scope.* The construction answers the existence question. It does not show that a non-identity map beats the identity for codes that are already good, nor does it classify the admissible maps. Doubled inputs make the parity condition automatic; whether non-doubled admissible maps give further gains remains open.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the accepted journal text was not read, and the HAL version is seat-reported. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
