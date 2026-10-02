---
slug: han-zhang-zhang-2026-cycle-five-strong-one-resistance
bibkey: han2026resistant
doi: null
url: https://arxiv.org/abs/2606.08561v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result
---

# The five-cycle graph state is strongly 1-resistant

## Problem

Han, Zhang and Zhang, arXiv:2606.08561v1, page 8, Discussion, ask:

> Several open problems remain. First, do C₅ and C₆ give strongly m-resistant graph states for m = 1 and m = 2, respectively? Here, “strong” means genuine multipartite entanglement rather than mere entanglement.

This dossier concerns the C₅, m = 1 clause. The five-cycle graph-state
amplitudes are the cyclic controlled-Z phase on five qubits, divided by
√32. Definition 2 of arXiv:2505.06567v1 requires initial genuine
multipartite entanglement (GME), GME after every one-qubit loss, and full
separability after every two-qubit loss. The formal claim is
`IsStrongResistant 1 (cycleGraphState 5)`.

## Motivation

The external Tier-1 question, its quantified claim and a proposed proof
route were preregistered in #11551. The frozen declaration
`D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result`
answers the C₅ clause Yes by proving all three conjuncts of strong
1-resistance. The C₆, m = 2 clause is a separate question settled by the
frozen refutation in
`D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.result`.

## Gap

The cited paper labels the C₅ and C₆ clauses open in its Discussion. The
repository intake and pinned-Mathlib searches recorded for #11551 found no
previous frozen settlement of the C₅ conclusion in the searched scope. Those
search readings do not establish worldwide priority or exhaustive literature
coverage. The source's ordinary-resistance results do not by themselves
certify the stronger GME and full-separability conditions.

## Route

For the initial density matrix ρ₅ use the witness W = I/2 − ρ₅. For each
four-qubit marginal ρ₄ use W = I/2 − 2ρ₄. The proof checks the exact
expectation −1/2 and positive semidefiniteness of every partial transpose
across every nontrivial cut by finite graph-basis Gram decompositions.
Trace-pairing reindexing gives nonnegative expectation on each cut-product
state and therefore on every biseparable mixture, proving GME for the initial
state and every one-qubit-loss marginal. For every two-qubit loss set, the
three-qubit marginal is an equal mixture of four products of local Pauli
eigenstates; the four weights are 1/4, proving full separability.

## Falsifier

A non-GME initial state, a one-qubit loss with a biseparable marginal, or a
two-qubit loss whose marginal is not fully separable would falsify the
formal conclusion. Each universal range is finite and is covered by the
corresponding exact witness or Pauli-product decomposition in `result`.
Numerical agreement without these exact decompositions would not settle the
claim.

## Evidence

The public declarations are
`D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.claim` and
`D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result`.
The latter has frozen statement ID
`sha256:ff1971d63c9d87ea1166cca200630f65ffa272c38b4933ba82611e14c068fe6b`.
Its direct frozen prerequisite is
`sha256:28de6f8730bb127ce3dd0dd0ca0dabf5f88223a0a726c007a65d8f5fec8fcfa9`,
which is the freeze event for
`D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.lean`.
The kernel axiom closure is the standard three axioms: `propext`,
`Classical.choice`, and `Quot.sound`.

## Triage

The C₅ strong-1-resistance clause is proved. The delivery uses
`admission_basis: open-problem-resolution` and `proof_shape: content`.
The live proof path contains exact graph-basis Gram decompositions,
trace-reindexing identities, and Pauli-product marginal decompositions; no
bind-only wrapper is delivered. Registration is paused under CLAUDE.md §3.9.
No atom or coverage edge is used.

### What the settlement shows

- Proved in this module: the five-cycle graph state is GME, every one-qubit
  loss marginal is GME, and every two-qubit loss marginal is fully separable.
- Proved in this module: the witness mechanism covers all 30 oriented cuts
  of the five-qubit state and all 14 oriented cuts for each four-qubit
  marginal; the ten two-qubit loss sets have four-term Pauli-product
  decompositions.
- The result settles the C₅ clause of the cited Discussion question. It does
  not settle the C₆ clause, other cycle sizes, ordinary resistance, or any
  stronger uniform statement beyond the finite C₅ instance.

## ASSUMED-UNVERIFIED

The Lean kernel verifies the formal statement and its standard axiom closure,
not the external publication, source quotations, or completeness of the
literature search. Fidelity of the finite-dimensional density-matrix encoding
to the published definitions is a semantic review obligation. Registration
status is governed by the current CLAUDE.md §3.9 pause.
