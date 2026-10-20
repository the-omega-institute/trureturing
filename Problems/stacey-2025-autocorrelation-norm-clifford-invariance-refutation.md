---
slug: stacey-2025-autocorrelation-norm-clifford-invariance-refutation
bibkey: stacey2025sicsmajorization
doi: null
url: https://arxiv.org/abs/2509.16819v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.result
---

# A Clifford unitary that changes the operator norm of the MUB autocorrelation matrix

## Problem

B. C. Stacey, *SICs, the Stabilizer Polytope and Majorization*, arXiv:2509.16819v1, Section III, defines A(ψ)_{mk} = Σ_j p_{m,j} p_{m,j+k}, where p_{m,j} are the outcome probabilities in the Weyl–Heisenberg mutually unbiased bases. It then states:

> Acting upon $\ket{\psi}$ with a Clifford unitary can at most permute the rows and columns of the matrix $A$. … Indeed, let $||\cdot||$ be any unitarily invariant norm; because permutation matrices are a very special subset of the unitary matrices, left- and right-multiplying $A$ by any pair of permutation matrices will leave $||A||$ unchanged. It seems, then, that we have a large family of new candidate monotones that are all extremized by Weyl--Heisenberg SIC fiducials.

The verbatim passage is in [the literature note](../Library/QuantumContext/stacey2025sicsmajorization.md).

Issue [#18928](https://github.com/the-omega-institute/trureturing/issues/18928) fixes the reading: for d = 5, the Euclidean operator norm of A is invariant under every Clifford unitary, for every pure state. It is refuted.

## Motivation

A magic monotone must be invariant under the free Clifford unitaries. The proposed family would supply many new monotones extremized by SIC fiducials.

## Gap

The literature check before any Lean is recorded in #18928:
- arXiv v1 is the only version;
- INSPIRE lists no citation, and OpenAlex has no record;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

The witness is ψ = (|0⟩ + |1⟩)/√2 with the Fourier unitary F, where F X F† = Z and F Z F† = X⁻¹.
1. **Clifford.** F is unitary and conjugates the shift and the clock to displacement operators.
2. **Probabilities.** The tables p(ψ, m, j) and p(Fψ, m, j) are exact values in ℚ(cos(π/5)).
3. **Separation.** The operator norm of A(ψ) is bounded above through ‖M‖ ≤ ‖M‖_F applied to M = AᵀA. The operator norm of A(Fψ) is bounded below by an explicit test vector, and the two bounds separate.

## Falsifier

The refutation would fail if the module's quantities differed from the source's. The module:
- uses the native MUB labels of the source, D(p, q) = τ^{pq} X^p Z^q with τ = ω³, with the label ∞ for the Fourier basis;
- takes A from the Born probabilities;
- takes a Clifford unitary as a unitary conjugating the shift and the clock to displacement operators up to phase;
- uses Mathlib's L2 operator norm.

## Evidence

The canonical source is `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.lean` (408 lines).
- **Proof.** It proves `result : ¬ claim` for the witness above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.lean.json`, statement `sha256:f7a62b7cb09ecaad6117c8a8242fda30d689754c39ec2960225a242a66b0fdde`.

Declaration statements:
- `result`: `sha256:a518e704544ca5781d5400415ca6bf126f2d9507468c47c165ad6b4541b09cb0`;
- `claim`: `sha256:985c8c90d26424200237b4079b44fe88d2f7b1a96aed5046bba4f8179db7331d`.

## Triage

Tier 1 assertion of a 2025 paper, preregistered in issue #18928 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: the tables are finite normalization, and the separation instantiates existing operator-norm inequalities followed by arithmetic | open-problem-resolution |
| definitions | bind-only | none | definitions used by `claim` |
| private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2.

`utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the Fourier Clifford changes the operator norm of A for ψ = (|0⟩ + |1⟩)/√2 in d = 5.

**Computed, not formalized** (orchestrator, recorded in #18928):
- ‖A(ψ)‖_op = 1.16835 and ‖A(Fψ)‖_op = 1.20503, while both Frobenius norms equal 1.22474;
- for ψ ∝ (5, 5, 1, 1, 1), the trace norms are 1.56301 and 1.48773;
- over 2000 random states, the largest change of the operator norm under F is 0.0385.
- for a random state z, every row of A(Fz) is an entry permutation of some row of A(z), but no single column permutation, combined with a row permutation, maps A(Fz) to A(z).

**Argued, not formalized.**
- *Where the argument fails.* A Clifford unitary maps each MUB to an MUB and relabels outcomes within it, but the relabelling of the difference index k need not be the same column permutation in every row. The rows are permuted, and each row's entries are permuted separately. Such a transformation preserves every entrywise norm, including the Frobenius norm, but not norms that depend on the matrix as a whole, such as the operator and trace norms.
- *What survives.* The Frobenius norm, and any function of the matrix that is symmetric under row permutations and under permutations within each row (a function of the multiset of row multisets), remain Clifford-invariant.

**Effect on the paper.** The proposed family is not Clifford-invariant in general: the operator norm fails. The result does not classify the other unitarily invariant norms.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
