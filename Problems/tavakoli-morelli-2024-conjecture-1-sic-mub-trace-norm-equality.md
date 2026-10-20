---
slug: tavakoli-morelli-2024-conjecture-1-sic-mub-trace-norm-equality
bibkey: tavakolimorelli2024schmidttracenorm
doi: 10.1103/PhysRevA.110.062417
url: https://arxiv.org/abs/2402.09972v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.result
---

# The MUB and SIC correlation trace norms agree up to the factor K

## Problem

A. Tavakoli and S. Morelli, *Enhanced Schmidt number criteria based on correlation trace norms*, arXiv:2402.09972v2, Phys. Rev. A 110, 062417 (2024), Conjecture 1:

> Provided that both a SIC and a complete set of MUBs exist in dimension $d_A$ and $d_B$, the criteria in Result 1 and 2 are equivalent. It then holds that $\left\|\mathbf{Q}\right\|_\text{tr}=K\left\|\mathbf{P}\right \|_\text{tr}$.

The SIC and MUB definitions, the correlation matrices P and Q and the constant K = √(d_A(d_A+1)) √(d_B(d_B+1)) are quoted in [the literature note](../Library/QuantumBounds/tavakolimorelli2024schmidttracenorm.md).

Issue [#19503](https://github.com/the-omega-institute/trureturing/issues/19503) fixes the reading. For all d_A, d_B ≥ 2, every density matrix ρ, every pair of local SICs and every pair of complete local MUB families, ‖Q‖_tr = K ‖P‖_tr. The conjecture is proved.

## Motivation

Results 1 and 2 of the source give Schmidt-number criteria ‖P‖_tr ≤ (1 + r)/K and ‖Q‖_tr ≤ 1 + r. The equality makes the two criteria equivalent, so one SIC measurement per side certifies exactly what d + 1 local bases certify. The source proves the equality when each SIC element is a fixed combination of the MUB projectors (its Result 3) and checks it numerically in prime dimensions below 20.

## Gap

The literature check before any Lean is recorded in #19503:
- arXiv v2 is the latest version;
- OpenAlex lists 16 citing works. A keyword search of arXiv:2506.18211 and 2505.02297 found no proof of the mixed-state equality; 2506.18211 Lemma 2 gives a pure-state specialization;
- the repository had settled the paper's Conjectures 2 and 3 but had no record of Conjecture 1.

`not-found-in-searched-scope`.

## Route

1. **SIC frame.** The d² SIC projectors are linearly independent, from their Gram matrix (d δ_ij + 1)/(d + 1), so they form a basis of the operator space. Hence X = Σ_i Tr(E_i X)(d(d+1)E_i − I) for every operator X.
2. **MUB frame.** For a complete set of MUBs, Σ_{l,a} Tr(G_{l,a} X) G_{l,a} = X + Tr(X)·I for every X.
3. **Coefficient matrix.** Step 1 writes each MUB projector in the SIC frame, G_k = Σ_i Θ_{k,i} E_i with Θ_{k,i} = (d+1)Tr(Π_i G_k) − 1. So Q = Θ^A P (Θ^B)ᵀ.
4. **Isometry.** Step 2 gives ΘᵀΘ = d(d+1)·I, with Θ real.
5. **Trace norms.** The positive square root of Q†Q is √(d_A(d_A+1)/(d_B(d_B+1))) Θ^B √(P†P) (Θ^B)ᵀ. Taking traces gives ‖Q‖_tr = K‖P‖_tr.

## Falsifier

The proof would not settle the conjecture if the module's objects were narrower than the source's. The module:
- takes every family of d² unit vectors with pairwise squared overlaps 1/(d + 1) as a SIC, with effects E_i = |ψ_i⟩⟨ψ_i|/d;
- takes every family of d + 1 unitary bases with cross overlaps 1/d as a complete set of MUBs (the frozen `MUBFamily`), with the rank-one projectors as effects;
- uses the joint probabilities Tr(ρ (E ⊗ F)) as the entries of P and Q;
- uses the trace norm of rectangular matrices.

## Evidence

The canonical source is `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.lean` (488 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The §3.9 registration is `Reg/D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.lean.json`, statement `sha256:05437f40bcec86fca5213c597bb62c330f35e9a4d718fc394759f7d1967e27de`.

Declaration statements:
- `result`: `sha256:73bda79cd36700d4c07679887b63fef4cad7f34b5aedb4635de8e3c3b1b95a85`;
- `claim`: `sha256:3266bf853a61bd0b4c5dbffeff0c954aacadcb5d17de6580421936f94e3d21d3`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #19503 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** ‖Q‖_tr = K‖P‖_tr for every state, all local SICs and complete MUB families, and every pair of local dimensions, equal or not. So the SIC criterion and the MUB criterion of the source are equivalent whenever both families exist.

**Computed, not formalized** (orchestrator, numpy, recorded in #19503): the equality holds to 6·10⁻¹⁵ on 200 random mixed states for each of (d_A,d_B) ∈ {(2,2), (3,3), (2,3), (3,2)}.

**Argued, not formalized.**
- *Mechanism.* Both a SIC and a complete set of MUBs are complex projective 2-designs. Their frame operators on the operator space are therefore both multiples of Id + |I⟩⟩⟨⟨I|, differing by the factor d(d+1). The correlation matrix of either measurement is the state seen through its frame, so the two tables differ by a scaled isometry on each side, and every singular value scales by K.
- *Generalization.* The same argument applies to any two weighted 2-designs. The trace norms of their correlation tables are proportional, with the ratio fixed by the frame constants; and every unitarily invariant norm, not only the trace norm, scales by the same factor.
- *Effect on Conjecture 3.* For incomplete MUBs (m < d + 1) the frame operator is not of this form. This is why the incomplete case of Conjecture 3 needs a separate argument.

**Effect on the paper.** Conjecture 1 holds without the extra condition of Result 3. The two Schmidt-number criteria are equivalent in every dimension where both measurements exist.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v2. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
