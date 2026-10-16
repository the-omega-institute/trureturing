---
slug: hirche-george-nuradha-wilde-2026-conditional-hockey-stick-orthogonal-reduction
bibkey: hirchegeorgenuradhawilde2026conditional
doi: null
url: https://arxiv.org/abs/2608.27171v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.result
---

# Conditional hockey-stick contraction coefficients reduce to orthogonal states and do not depend on γ

## Problem

C. Hirche, I. George, T. Nuradha and M. M. Wilde, *Conditional contraction coefficients and their applications to quantum networks*, arXiv:2608.27171v1, study contraction coefficients with reference systems.
- **The coefficient.** η^Δ_D(N) := sup over |R| and ρ_RA ≠ σ_RA of [D((id ⊗ N)(ρ_RA)‖(id ⊗ N)(σ_RA)) − D(ρ_R‖σ_R)] / [D(ρ_RA‖σ_RA) − D(ρ_R‖σ_R)] (Eq. (2.14)), over pairs with a strictly positive finite denominator (Remark 2).
- **The divergence.** E_γ(ρ‖σ) := Tr(ρ − γσ)₊ (Eq. (5.1)). For γ = 1 the coefficients η^c_Tr and η^Δ_Tr are optimized by orthogonal states (Proposition 8).
- **The open problem.** "When considering the hockey-stick divergence, can the optimization in the contraction coefficient be restricted to orthogonal states, similar to Proposition 8? This would directly imply that the associated contraction coefficient is monotone in γ" (§9, p. 72).

The verbatim statements are in [the literature note](../Library/QuantumChannels/hirchegeorgenuradhawilde2026conditional.md).

Issue [#17637](https://github.com/the-omega-institute/trureturing/issues/17637) fixes the reading for the conditional coefficient η^Δ_{E_γ}, γ ≥ 1:
- S_γ(N) is the set of ratios over every finite reference system R and all states ρ, σ on R ⊗ A with a positive denominator;
- S^⊥_γ(N) is its subset from pairs with ρσ = 0;
- (i), the question asked: S_γ(N) = S^⊥_γ(N);
- (ii), a strengthening: S_γ(N) = S_δ(N) for all γ, δ ≥ 1.

Both are proved in this reading. The complete coefficient η^c_{E_γ} is not addressed.

## Motivation

For the trace distance, the restriction to orthogonal states turns the conditional coefficients into tractable optimizations (Proposition 8). Remark 6 explains why the same restriction for the hockey-stick divergence matters: without reference systems it gives monotonicity of the coefficient in γ, while with reference systems this monotonicity was open, with "some preliminary numerical evidence" that it "might not hold".

## Gap

Issue #17637 records the literature check before any Lean:
- arXiv v1 is the only version;
- the citing works arXiv:2610.03706, 2609.09629 and 2608.19685 do not treat the question;
- the older works arXiv:2202.10717 (the orthogonal reduction for the coefficient without reference systems), 2503.22823 (complete coefficients) and 2512.16778 do not give this conditional reduction;
- Naixu-Guo/quantum-open-problems, Zenodo and Crossref have no matching entry;
- the repository had no entry for the paper.

The Semantic Scholar citation list was not retrieved (rate limited).

`not-found-in-searched-scope`.

## Route

1. **Jordan parts.** For an admissible pair (ρ, σ) at γ, write ρ − γσ = P − Q with P, Q ⪰ 0 and PQ = 0, and put p = Tr P, q = Tr Q.
2. **Flags.**
   - For δ ≥ 1, put c = 1/(1 + p + q/δ), a = 1 − cp and b = δ − cq. Then c > 0, a ≥ 0 and b ≥ 0.
   - On R′ = R ⊕ C ⊕ C, with a pure state τ on A, put ρ′ = cP ⊕ aτ ⊕ 0 and σ′ = (cQ/δ) ⊕ 0 ⊕ (bτ/δ).
   - These are orthogonal states, and ρ′ − δσ′ = c(ρ − γσ) ⊕ aτ ⊕ (−bτ).
3. **Blockwise evaluation.**
   - id ⊗ N and Tr_A act blockwise. The positive-part trace is additive on direct sums and positively homogeneous.
   - So both conditional gaps of (ρ′, σ′) at δ are c times those of (ρ, σ) at γ, and the ratio is unchanged.
   - δ = γ gives (i), and arbitrary δ gives S_γ(N) ⊆ S_δ(N), hence (ii).

## Falsifier

The theorem would not answer the question if:
- the module's divergence, amplification, reference marginal or ratio set differed from Eqs. (2.14) and (5.1) with Remark 2;
- or its orthogonality condition differed from orthogonal states.

The module uses E_γ(ρ‖σ) = Re Tr(ρ − γσ)₊ with the continuous-functional-calculus positive part, the amplification id_R ⊗ N of a completely positive trace-preserving map, and the reference marginal Tr_A. The ratio set ranges over every finite reference type and all states with a positive denominator. Orthogonality is ρσ = 0, which for positive semidefinite matrices is orthogonality of supports. The subtracted output marginal equals the input marginal because N is trace preserving.

## Evidence

The canonical source is `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.lean` (755 lines).
- It defines `posTrace`, `E`, `amp`, `gap`, `ratios` and `claim`, and proves `result : claim`. It also proves two lemmas used by other modules: `posSemidef_blockDiagonal` (block-diagonal matrices with positive semidefinite blocks are positive semidefinite) and `partialTraceRight_smul`.
- It uses:
  - the frozen `QuantumChannel`, `FiniteDiamondDistance.referenceLinear`, `PartialTraceMutualInformation.partialTraceRight` and `RHLinalg.rtrace`;
  - `FiniteTraceDistance.re_trace_eq_trace`, made public for this settlement;
  - the continuous-functional-calculus positive part.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations, all `declared_validated`:
  - in `Reg/D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.lean`:
    - `result` reads out the orthogonal ratio set ratios N γ true, with the rejected realization its complement;
    - `posSemidef_blockDiagonal` reads out the block-diagonal matrix of the blocks, with the rejected realization its negative;
    - `partialTraceRight_smul` reads out the partial trace of X, with the rejected realization the partial trace of Xᵀ;
  - in `Reg/D5/S3/Quantum/Foundation/FiniteTraceDistance.lean`: `re_trace_eq_trace` reads out the trace of A, with the rejected realization the trace of the matrix that repeats one row of A in every row.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.lean.json`, statement `sha256:1753b66aaa990c80ddabec89f782d91759ea04586c977c7c6a354e7375b36cd6`.

Declaration statements:
- `result`: `sha256:4ac00c273033db6068c2c48645fc4f297eee67167bd3af387d0719d536f1a369`;
- `claim`: `sha256:b70515a2e1b666e5c9d22b560ffdd9cd2a066735dfb74226aa080600acf4e374`.

## Triage

Tier 1 open problem of a 2026 paper, preregistered in issue #17637 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the Jordan decomposition, the flag construction, the blockwise positive-part traces and the scalar identities are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| posSemidef_blockDiagonal, partialTraceRight_smul | bind-only (consumed on the proof path of `result` and by other modules) | none | consumed helpers |
| the block, trace, channel and flag helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every channel N between finite systems and every γ ≥ 1:
- the ratio set of the conditional hockey-stick coefficient equals its subset from orthogonal pairs, so η^Δ_{E_γ}(N) is optimized by orthogonal states;
- the ratio sets at γ and δ are equal for all γ, δ ≥ 1, so η^Δ_{E_γ}(N) = η^Δ_Tr(N) for every γ ≥ 1.

**Computed, not formalized** (orchestrator, NumPy, recorded in #17637):
- on one random instance (dim R = dim A = dim B = 2, a three-Kraus channel, γ = δ = 2), the ratio 0.68647 is reproduced exactly by the orthogonal flag pair;
- on 300 random instances with independent γ, δ ∈ [1, ∞), the defect of the gap scaling and of the orthogonality is at most 1.2 × 10⁻¹⁵.

**Argued, not formalized.**
- *Mechanism.* The flags add a pure direction carrying the mass a to the positive part and a direction carrying b to the negative part. This fixes the normalizations and makes the pair orthogonal, and it changes the reference marginals by exactly the same amount as the joint states. The cancellation in the conditional gap, which subtracts the marginal divergence, is what makes the construction exact. The complete coefficient η^c requires ρ_R = σ_R, which the flags destroy.
- *Consistency.* Proposition 10 gives η^Δ_{E_γ}(BSC_p) ≥ 1 − 2p for the binary symmetric channel with (1 − p)/p = γ. With the theorem, this becomes a lower bound on η^Δ_Tr(BSC_p).

**Open.**
- The complete coefficient η^c_{E_γ}: whether its optimization reduces to orthogonal states, and whether it is monotone in γ.
- Whether the orthogonal pairs can be taken pure; the source notes this is unclear already for the trace distance.

**Effect on the paper.**
- The first open problem of §9 is answered affirmatively for the conditional coefficient.
- The monotonicity question of Remark 6 is answered for η^Δ: it holds, and the coefficient is constant on γ ≥ 1. Numerical non-monotonicity with reference systems, if observed for η^Δ, would contradict the theorem; for η^c it remains possible.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
