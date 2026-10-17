---
slug: parzygnat-2021-two-qubit-conditional-domain-refutation
bibkey: parzygnat2021conditionaldistributions
doi: 10.4204/EPTCS.343.1
url: https://arxiv.org/abs/2102.01529v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.result
---

# Two-qubit conditional domains need not be C*-subalgebras

## Problem

A. J. Parzygnat, *Conditional Distributions for Quantum Systems* (QPL 2021, EPTCS 343, 1–13; arXiv:2102.01529), constructs quantum conditionals by categorical Bayesian inversion. For a density matrix ν on M_m ⊗ M_n with invertible marginals ρ = tr_B ν and σ = tr_A ν (Corollary 4.5), the conditional domains are:
- B_ν = {B : tr_B(ν(1 ⊗ B)) commutes with ρ};
- A_ν = {A : tr_A((A ⊗ 1)ν) commutes with σ} (Definition 5.5).

They are the largest operator systems on which the conditionals are positive (Lemma 5.8, Corollary 5.13).
- After Example 5.10 the author asks whether the domains are always C*-subalgebras, and answers no with an unrecorded 9 × 9 density matrix of rank 2.
- Footnote 13 adds: "Also, I could not find a 4 × 4 density matrix ν for which the conditional domains are not C∗-subalgebras, and I suspect that this may always be the case. I hope to resolve this in future work."

The verbatim statements are in [the literature note](../Library/QuantumChannels/parzygnat2021conditionaldistributions.md).

Issue [#18167](https://github.com/the-omega-institute/trureturing/issues/18167) fixes the reading: for every two-qubit density matrix with invertible marginals, both conditional domains are C*-subalgebras of M₂(ℂ). This suspicion is refuted.

## Motivation

On a conditional domain the conditional is a positive map, so inference by conditioning is valid there. If the domain is a C*-subalgebra, the restricted conditional is a positive map between C*-algebras, and the algebraic structure of the observables on which one can condition is preserved. The suspicion would give this structure for every pair of qubits.

## Gap

Issue #18167 records the literature check before any Lean:
- arXiv versions v1, v2 and v3 all retain the footnote;
- the full texts of the citing works mention the source only in their bibliographies;
- web and Zenodo searches found no settlement;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

In the basis (00, 01, 10, 11), let ν = (1/32)·[[11, 1, 1, 0], [1, 7, 0, −1], [1, 0, 9, −1], [0, −1, −1, 5]].
1. **A state with invertible marginals.**
   - ν is Hermitian with trace 1.
   - 32ν = diag(9, 5, 7, 3) + v₁v₁ᴴ + v₂v₂ᴴ + v₃v₃ᴴ + v₄v₄ᴴ, with v₁ = e₀₀ + e₀₁, v₂ = e₀₀ + e₁₀, v₃ = e₀₁ − e₁₁ and v₄ = e₁₀ − e₁₁. So ν is positive, indeed ν ≥ (3/32)·1.
   - Its marginals are ρ = diag(9/16, 7/16) and σ = diag(5/8, 3/8).
2. **The domain B_ν.** For B = [[a, b], [c, d]], tr_B(ν(1 ⊗ B)) = (1/32)·[[11a + b + c + 7d, a − d], [a − d, 9a − b − c + 5d]]. Since ρ is diagonal with distinct entries, this commutes with ρ exactly when a = d. So B_ν = {[[a, b], [c, a]]}.
3. **Failure of multiplication.** The matrix units E₀₁ and E₁₀ lie in B_ν, but E₀₁E₁₀ = E₀₀ does not. So B_ν is not closed under multiplication and is not a C*-subalgebra.

## Falsifier

The refutation would not settle the suspicion if:
- the module's conditional domains differed from Definition 5.5;
- its state space differed from the setting of Corollary 4.5;
- its notion of C*-subalgebra differed from the source's.

The module takes:
- the first tensor factor as A and the second as B, with tr_B and tr_A the partial traces over the second and first factor;
- the domains as the matrices whose partial trace commutes with the corresponding marginal;
- the states as two-qubit density states with invertible marginals;
- a C*-subalgebra as the carrier of a unital star subalgebra. Both domains contain 1 (Lemma 5.8), and a *-subalgebra of M₂(ℂ) is norm-closed.

A 4 × 4 density matrix with a trivial factor (m = 1 or n = 1) has the full algebra or the scalars as domains, so the suspicion concerns m = n = 2.

## Evidence

The canonical source is `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.lean` (161 lines).
- It defines `conditionalDomainB`, `conditionalDomainA` and `claim`, and proves `result : ¬ claim`.
- It reuses `FiniteStateChannel.DensityState`, the partial traces `partialTraceLeft` and `partialTraceRight` of `PartialTraceMutualInformation` with its trace lemma `trace_partialTraceRight`, and the Mathlib Kronecker product, positivity and star-subalgebra API.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.lean.json`, statement `sha256:d85ed91421ed37005b5140bd93099f81555b1479e2dcc6c5e8f01803f1533895`.

Declaration statements:
- `result`: `sha256:0c8439ee02d9561cbf2428e15b7e4eaa7f0211559a2930fb0641ae62b1c647bc`;
- `claim`: `sha256:baaef267eb165cd350e56d7d734b1ea4ab58bd29a213fcd3e7b38ef5c1172765`.

## Triage

Tier 1 question of a 2021 paper, preregistered in issue #18167 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the positivity, the marginals and the domain memberships are finite matrix identities | open-problem-resolution |
| the witness helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every public declaration is bind-only; the definitions are used by public statements. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** the two-qubit density matrix ν above has invertible marginals, and its conditional domain B_ν is not closed under multiplication.

**Computed, not formalized** (orchestrator, exact SymPy check recorded in #18167).
- ν ≥ (3/32)·1, by the sum of squares in step 1 of the route, so ν has full rank; the module proves positive semidefiniteness.
- tr_A((A ⊗ 1)ν) = (1/32)·[[11a + b + c + 9d, a − d], [a − d, 7a − b − c + 5d]] for A = [[a, b], [c, d]], so A_ν = {[[a, b], [c, a]]} as well. Both conditional domains fail.

**Argued, not formalized.**
- *When the domain is an algebra.* Write T(B) = tr_B(ν(1 ⊗ B)), so B_ν is the preimage under T of the commutant of ρ.
  - If ρ is scalar, B_ν is all of M₂(ℂ).
  - Otherwise the commutant of ρ is two-dimensional. If moreover T is invertible, B_ν is a two-dimensional operator system, of the form span{1, X} with X Hermitian, and X² = (tr X)X − (det X)·1 lies in it by Cayley–Hamilton.

  So a two-qubit counterexample needs a non-scalar marginal and a singular T, and the same holds for A_ν. In the witness, T has rank 3: its kernel contains E₀₁ − E₁₀.
- *Genericity.* det T is a polynomial in the entries of ν. It does not vanish at the Bell state (1/2)(e₀₀ + e₁₁)(e₀₀ + e₁₁)ᴴ, where T(B) = Bᵀ/2. The same holds for the corresponding map of A_ν. So the suspicion holds for every two-qubit state with invertible marginals outside the zero sets of these two determinants, a proper algebraic subset. Counterexamples can occur only within that subset, and the witness shows that one occurs there with full rank.

**Effect on the paper.** The answer "no" to "Is this always the case?" already holds for two qubits, with a full-rank state and invertible, non-degenerate marginals. The 9 × 9 example of the source is not the smallest.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
