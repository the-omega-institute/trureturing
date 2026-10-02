---
slug: xu-2015-oblique-discord-mutual-information-refutation
bibkey: xu2015oblique
doi: 10.1142/S0217979216502568
url: https://arxiv.org/abs/1506.00404v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.result
---

# Xu's oblique-discord mutual-information conjecture

## Problem

Jianwei Xu, *Oblique discord*, arXiv:1506.00404v1, p. 3, Conjecture (22):

> Conjecture: I(ρ^{AB}) ≥ I(Φ_A ρ^{AB}) for any Φ_A and any ρ^{AB}, where I(ρ^{AB}) is the mutual information, Φ_A is defined in Eq.(13).

The normalized basis immediately before Eq. (13) consists of unit vectors
v_i and their biorthogonal duals w_i, with ⟨v_i,w_j⟩ = δ_ij. The operation is
T_b(ρ) = ∑_i (|v_i⟩⟨w_i| ⊗ 1) ρ (|w_i⟩⟨v_i| ⊗ 1),
N_b(ρ) = tr_B(∑_i ⟨w_i|ρ|w_i⟩), Φ_b(ρ) = T_b(ρ)/N_b(ρ).
The Lean normalizer uses partialTraceRight over B on the sum of rectangular
bra-vector sandwiches, extracting the scalar on the Unit factor. The unit
norms prove equality with Re(tr(T_b(ρ))) inside phi, and a local have in
result checks the same equality at the witness. Mutual information is
S(ρ_A) + S(ρ_B) − S(ρ). The conjecture quantifies over all finite dimensions,
all normalized bases and their duals, and all density states on the domain
of the normalized operation. Its Lean domain explicitly requires a
positive normalizing trace.

## Motivation

The frozen result negates this universal statement with an exact two-qubit
witness. The entropy and mutual-information objects are the existing
vonNeumannEntropy and quantumMutualInformation, with actual partial-trace
marginals. Natural logarithms multiply the source's bit-valued comparison
by the positive constant log(2).

## Gap

Issue #11784 preregisters the verbatim conjecture, its fully quantified
reading, Tier 1 classification, the Refuted settlement, and the literature
check before any Lean probe. Its checked scope consists of arXiv v1,
Crossref citation metadata, MathDB and repository searches. The reported
Crossref citation count is zero and no prior settlement was found in that
searched scope. This is not an exhaustive priority claim.

The journal full text is unverified. The formal statement concerns arXiv v1;
equivalence with the journal version is ASSUMED-UNVERIFIED.

## Route

Use dimensions n_A = n_B = 2, basis vectors (2,±1)/√5, dual vectors
(√5/4,±√5/2), and the pure input (8|00⟩+|11⟩)/√65. In order
00,01,10,11 the input matrix is
(1/65)[[64,0,0,8],[0,0,0,0],[0,0,0,0],[8,0,0,1]].
The output is
(1/85)[[64,0,0,8],[0,4,8,0],[0,8,16,0],[8,0,0,1]],
and the unnormalized trace is 17/26. Rational similarity certificates give
input eigenvalues 1,0,0,0 and output eigenvalues 13/17,4/17,0,0.
The input marginals are diag(64/65,1/65). The output marginals are
respectively diag(4/5,1/5) and diag(16/17,1/17).

With h = Real.binEntropy, the information gain is
h(1/5)+h(1/17)−h(4/17)−2h(1/65)
= (7648/1105)log(2)−log(5)−(21/17)log(13).
The inequalities 5³ < 2⁷ and 13¹⁷ < 2⁶³, logarithmic monotonicity and
algebraic normalization prove this gain strictly positive. The proof uses
the frozen entropy_eq_sum spectral bridge directly and no forwarding
entropy, mutual-information, binary-entropy or index-conversion definition.

The only authored public theorem is result : ¬ claim. Its proof_shape is
bind-only under CLAUDE.md §3.2 after inlining the fixed witness data and
local proof steps; escape_witness is none. Admission is
open-problem-resolution, not escape-witness. Utility is certified-instance
with a typed refutes edge to the closed claim.

## Falsifier

The refutation requires a normalized genuine basis and dual, a positive
trace-one input, a strictly positive normalizing trace, and a strict
increase in the existing mutual information. Violating any of these would
invalidate the witness. All these obligations are discharged in result;
the two dimensions are two, not an omitted universal hypothesis.

## Evidence

The Lean proof checks positivity, trace, basis duality, the normalized
operation, the spectra and the strict logarithmic comparison inside result.
Its axiom closure is propext, Classical.choice and Quot.sound. The Scribe
mirror displays every public definition and the exact negation of claim.
The resolution claim is Refuted, and its host is the frozen result.

Registration is paused under CLAUDE.md §3.9 (information-escape registration pause).

## Triage

Tier 1, external explicitly stated conjecture; settlement Refuted.
No digestion atom or coverage step applies to this external settlement.

### What the settlement shows

- **Proved by** `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.result`: Eq. (22) fails for the explicit normalized
  oblique basis and pure two-qubit input above. Neither singular density
  matrices nor state-dependent normalization are excluded from the source.
  The proof checks them through the existing density-state and entropy
  objects.
- **Computed:** the exact matrix, trace, marginal and spectral calculations
  occur inside `result` and are checked by
  `lake env lean D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.lean`.
  Python Decimal at precision 60 gives I(ρ) =
  0.15897400640607425773258 nats, I(Φρ) =
  0.17852592563483730549380 nats and gain
  0.01955191922876304776121 nats. The computation is
  `python3 -c 'from decimal import Decimal as D,getcontext; getcontext().prec=60; h=lambda p:-p*p.ln()-(1-p)*(1-p).ln(); a=2*h(D(1)/65); b=h(D(1)/5)+h(D(1)/17)-h(D(4)/17); print(a,b,b-a)'`;
  strict positivity is independently proved by Lean, not inferred from
  decimal rounding.
- **Computed failure mechanism:** ∑ K_i†K_i = diag(5/8,5/2), so this oblique
  operation is not trace preserving before normalization. The diagonal is
  computed from the displayed Kraus matrices by
  `python3 -c 'from fractions import Fraction as F; print(2*(F(1,4)+F(1,16)),2*(1+F(1,4)))'`. Dividing by a
  state-dependent trace is the operation tested by the conjecture.
- **Open in this module:** a theorem characterizing the bases for which
  the comparison holds for every bipartite input, and the comparison for
  restricted orthonormal bases. The latter is the usual channel
  data-processing setting; this module adds no theorem about that setting.
- **Open in this module:** the infimum in Definition (21) is not constructed
  here. This witness gives a negative value of its displayed objective,
  so Eq. (22) cannot justify its proposed universal nonnegativity. The
  geometric definitions and the zero-oblique-discord characterization
  are not negated by result; their separate proofs are not audited here.

## ASSUMED-UNVERIFIED

- Journal full-text agreement with arXiv v1 is not verified.
- Literature coverage is limited to the checked surfaces recorded in
  #11784; no worldwide novelty or priority is asserted.
- Carrier/model-family independence is not established by Lean.
