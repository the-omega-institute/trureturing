---
slug: ambainis-2024-random-access-code-two-setting-advantage
bibkey: ambainis2024racadvantage
doi: 10.1088/1367-2630/ad9bdf
url: https://arxiv.org/abs/1510.03045v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.result
---

# Every (n,d)↦1 random access code has a quantum advantage with two measurement settings

## Problem

A. Ambainis, D. Kravchenko, S. Sazim, J. Bae and A. Rai, *Quantum advantages in (n,d)↦1 random access codes*, arXiv:1510.03045v4, New J. Phys. 26 (2024) 123023, Section 5:

> We conjecture that the quantum advantages would appear in $(n,d) \mapsto 1$ RACs in general and leave it as an open question. The problem also addresses minimal resources, i.e., two measurement settings, to achieve quantum advantages in information theory.

The scenario, the figure of merit and the classical strategies with shared randomness are quoted in [the literature note](../Library/QuantumContext/ambainis2024racadvantage.md).

Issue [#19414](https://github.com/the-omega-institute/trureturing/issues/19414) fixes the reading. For all n, d ≥ 2, some pure-state quantum strategy decoded by two projective measurements has an average success probability strictly above that of every classical strategy with shared randomness. The conjecture is proved.

## Motivation

The source proves that majority encoding with identity decoding is classically optimal. It gives closed forms for n = 2, 3, 4 and numerics for n ≤ 11, d ≤ 6 and for n ≤ 6, 7 ≤ d ≤ 21; the binary family d = 2 was settled later for all n. Two settings are the least possible, since the source proves that one measurement setting gives no advantage.

## Gap

The literature check before any Lean is recorded in #19414:
- arXiv v4 is the latest version and keeps the open sentence;
- OpenAlex lists 9 citing works. The orchestrator checked arXiv:2111.08890, which treats n = 3 and MUB conditions. The search seat checked the others, including the d = 2 results arXiv:2506.19369 and arXiv:2604.21274;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Classical optimum.** A mixture is bounded by its best deterministic strategy. For a deterministic decoder the best encoder scores Σ_x max_r (matches of x with row r). If a decoder column repeats a symbol, replace one occurrence by a missing symbol. The column score summed over symbols does not decrease, because the words that lose are paired with words that gain. This exchange reduces the number of missing symbols, so some decoder whose columns are permutations is optimal. Relabeling gives the classical optimum C(n,d) = (1/(n dⁿ)) Σ_x max_i #{t : x_t = i}.
2. **Baseline quantum strategy.** Queries 1, …, n−1 are measured in the standard basis. Query n is measured in the columns of F, whose first 2×2 block is [[3/5, 4/5], [4/5, −3/5]] and which is the identity elsewhere. For a prefix z with counts N_i, maximum m and maximiser set M, Alice sends the normalized projection of f_b onto the coordinates in M, or e_a for some a ∈ M if that projection vanishes. Summed over the last letter b, the quantum score is d·m + |M|, which equals the classical score on the words (z,b). So the baseline value is exactly C(n,d).
3. **Improvement.** Encode 0ⁿ by (2n e₀ + e₁)/√(4n² + 1). This raises the score of that word from n − 1 + 9/25 by (23n + 32)/(25(4n² + 1)) > 0.

## Falsifier

The proof would not settle the conjecture if the module's classical class were smaller, or its quantum class larger, than the source's. The module:
- takes as classical strategies all shared-randomness mixtures of deterministic encoders Xⁿ → X and decoders X × J → X, as in §3.1. Private randomness of either party is a further mixture of deterministic maps;
- restricts the quantum side to pure states and two projective measurements, a subclass of the source's quantum strategies;
- averages uniformly over words and queries, as in Eq. (4).

## Evidence

The canonical source is `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.lean` (642 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The §3.9 registration is `Reg/D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.lean.json`, statement `sha256:0f14e2cf11e6ccd55ad8442ba45e29ab341120b63a7cf31bdff88fdc0ee68aee`.

Declaration statements:
- `result`: `sha256:2b2be18c4a8404c6d34d5739a1df3239d0c731851e59cc626d8097da83fd8611`;
- `claim`: `sha256:c68603a75ca10dcc37c4fd673700c5baa56048633b3d9ba786e41cbe40c7459a`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #19414 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:**
- for all n, d ≥ 2 there is a quantum strategy with two projective measurements whose average success exceeds that of every classical strategy;
- in the course of the proof, the classical optimum is at most C(n,d) (the source's Theorem 1).

**Computed, not formalized** (orchestrator, recorded in #19414): the constructed quantum value against C(n,d) for nine pairs (n,d), for example 0.772941 against 3/4 at (2,2). Brute force over all deterministic classical strategies confirms C(n,d) for six small pairs.

**Argued, not formalized.**
- *Mechanism.* Classically, the optimal score of a word is its majority count. The baseline quantum strategy reproduces this on average over the last letter: the second measurement only redistributes the one extra correct answer that the last letter can add. The advantage comes from a single word: for 0ⁿ the majority symbol and the last letter agree, and a state tilted toward the second basis vector gains on the last query more than it loses on the first n − 1.
- *Size.* The advantage of this construction is (23n + 32)/(25(4n² + 1) n dⁿ). It decays exponentially in n, so it is an existence statement, not a large-advantage bound.
- *Scope.* The construction uses one real rotation of two basis vectors and works for every d, including composite d, where complete sets of mutually unbiased bases are not known.

**Effect on the paper.** The open question of Section 5 has a positive answer, with the minimal number of two measurement settings.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v4. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
