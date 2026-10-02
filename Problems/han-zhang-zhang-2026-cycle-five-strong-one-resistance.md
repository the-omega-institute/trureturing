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

- [proved: D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result]
  The decisive separation is between cut-product mixtures and the loss
  marginals: graph-basis Gram decompositions make every partial transpose of
  W positive semidefinite, so trace reindexing makes its expectation
  nonnegative on every biseparable mixture, whereas the initial state and
  each one-loss marginal have expectation −1/2. Four equal-weight local
  Pauli products certify each two-loss marginal. Ordinary 1-resistance of C₅
  is the known weaker result of Han–Zhang–Zhang; strong 1-resistance is this
  settlement and implies the ordinary one by Definition 2 of
  arXiv:2505.06567v1, p. 3.
- [computed: python3 /tmp/op-c5-settlement/cycle_certificates.py →
  C5_TWO_LOSS: marginals=10, rank_each=4, weights=(1/4,1/4,1/4,1/4);
  PAULI_PRODUCTS: max_entry_error=0]
  Exact cyclic-phase partial traces and local Pauli eigenprojectors give
  rank four for all ten three-qubit marginals and reconstruct every entry
  with four pure product terms. Thus four is the minimum number of pure
  product terms in these decompositions: fewer than four rank-one matrices
  cannot have rank four. This sharpness concerns decomposition length, not
  an optimal entanglement or noise bound.
- [computed: python3 /tmp/op-c5-settlement/cycle_certificates.py →
  C3: initial_wpt_min=0; PAULI_PRODUCTS: marginals=3, rank=2, terms=2,
  weight=1/2, max_entry_error=0; C3/C4: one_loss_wpt_min=−1/2]
  The same two certificate types reach the smaller C₃, m=0 case: the
  initial projector witness has nonnegative partial transposes, and all
  three one-loss marginals are equal mixtures of two Pauli product states.
  In contrast, the one-loss witness I/2 − 2ρ has a negative partial
  transpose for every single loss of C₃ and C₄. That particular Gram
  certificate fails; its failure alone is not a test for biseparability.
- [computed: python3 /tmp/op-c5-settlement/cycle_certificates.py →
  C6/C7/C8: one_loss_wpt_min=0, passing_losses=6/7/8;
  two_loss_pt_min=−1/8, loss_sets=15/21/28]
  Enumerating supported cycle stabilizers and their exact Walsh spectra
  extends the single-loss witness certificate to every single loss for
  n=6,7,8. However, every two-loss marginal in these three cycles has an
  NPT cut, with minimum eigenvalue −1/8, so it cannot have the required
  full-product decomposition. The GME part of the m=1 method extends in
  this finite range; the full-separability part obstructs strong
  1-resistance. An NPT cut establishes entanglement, not GME.
- [computed: python3 /tmp/op-c5-settlement/cycle_certificates.py →
  SEPARATOR: n=5,6,7,8, 2≤m≤n−2, cases=14, terms=2^m,
  weight=2^(−m), max_entry_error=0; C6 lost={0,2}: rank=4,
  cut_{1}_pt_min=0, all_cut_pt_min=−1/8]
  Losing {0,2}, with additional losses {3,…,m} when m>2, isolates qubit 1
  in the retained graph. For each lost-bit configuration the cyclic phase
  factors across {1}|rest; averaging gives an exact cut-product mixture
  with 2^m equal weights. This supplies a biseparable m-loss marginal in
  each of the fourteen cases. For C₆, m=2 (#11641), the marginal is
  entangled across another cut but biseparable across {1}|{3,4,5}:
  ordinary 2-resistance cannot substitute for strong 2-resistance.
  Together with the proved C₅ answer, this resolves both clauses of the
  first Discussion question, rather than invalidating the paper's
  ordinary-resistance results.
- [open] Uniform versions of the computed mechanisms require new proof
  obligations: a graph-basis spectrum/Gram identity and nonnegative
  coefficients for every n≥5 single-loss cut, and a conditional-phase
  cut-product identity for n≥4 and every 2≤m≤n−2. The fixed five-qubit
  coefficient tables do not supply either quantified theorem. The C₄
  one-loss case needs a different witness or an explicit biseparable
  decomposition; a failed witness is insufficient. These are formal
  method extensions, not fresh open resistance questions for large
  cycles: Proposition 6 of the source already rules out ordinary
  m-resistance for n≥7 and 0≤m≤n−2. Transporting that published no-go
  through the strong-implies-ordinary implication would exclude strong
  resistance too; that uniform implication is not proved in this module.
- [open] A strong-resistance classification of the source's small-graph
  classes needs more than its ordinary-resistance Table I. Extending this
  C₅ proof to the entire local Clifford orbit requires a formal transport
  of GME, full separability and partial trace under local unitaries and
  relabelling. For six qubits the C₆ representative is excluded at m=2,
  but the other two ordinary-2-resistant representatives G_I and G_AME
  need their own GME certificates or biseparable loss witnesses, followed
  by the same transport. No conclusion about those two strong classes
  follows from the C₅ or C₆ certificates alone.
- [open] The second Discussion question, whether non-stabilizer pure
  states realize parameters forbidden to graph states, remains outside
  these settlements. The graph/stabilizer no-go domain must not become a
  no-go for all pure states; the Discussion itself cites seven-qubit
  4- and 5-resistant pure states as known examples. The remaining
  six-/seven-qubit parameters need a separately specified non-stabilizer
  construction and certificates for every required loss, or a no-go
  proof valid beyond stabilizers. The cycle Gram tables and Pauli-product
  certificates supply neither, and the cited known examples are not new
  open-problem targets.

## ASSUMED-UNVERIFIED

The Lean kernel verifies the formal statement and its standard axiom closure,
not the external publication, source quotations, or completeness of the
literature search. Fidelity of the finite-dimensional density-matrix encoding
to the published definitions is a semantic review obligation. Registration
status is governed by the current CLAUDE.md §3.9 pause.
