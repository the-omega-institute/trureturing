---
slug: vomende-2024-elementary-channel-divisibility
bibkey: vomende2024divisibility
doi: 10.1063/5.0231812
url: https://arxiv.org/html/2407.17103v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.result
---

# Exact classification of elementary channel divisibility

## Problem

Frederik vom Ende, *A Sufficient Criterion for Divisibility of Quantum Channels*,
arXiv:2407.17103v3, Section V, asks:

> An open question at this point is whether our sufficient condition is also necessary, and whether our necessary condition is also sufficient.

The source is [arXiv v3](https://arxiv.org/html/2407.17103v3), with publication
identifier [DOI 10.1063/5.0231812](https://doi.org/10.1063/5.0231812).
Definition 1 and Lemmas 2–3 specify the elementary channel and inverse;
Proposition 1 and Theorem 1 specify the necessary and sufficient conditions.
This dossier anchors the combined classification of the two reversals,
including their fixed-pair and existential-pair readings.

Let the complex dimension be any finite n ≥ 2, let Φ be an actual CPTP map,
and let (Kⱼ) be any finite Kraus representation of Φ. For an ordered pair of
orthogonal unit vectors (x,y), E(x,y) means that Φ composed on the right
with the inverse of the elementary channel Ψₜ(x,y) is completely positive
for some real 0 < t < 1. N(x,y) means
⟨y,Kⱼ*Gx⟩ = 0 for every index j and every complex matrix G in the
Hilbert–Schmidt orthogonal complement of the whole complex Kraus span.
S(x,y) means N(x,y) together with the additional diagonal tests
⟨x,Kⱼ*Gx⟩ = 0 over the same indices and complement.

The classification established by the designated result has four cells:

| Reading | Answer |
| --- | --- |
| Fixed ordered pair: N(x,y) iff E(x,y) | Proved for every map and representation in the stated scope. |
| Existential ordered pair: some N pair iff some E pair | Proved for the same map and representation. |
| Fixed ordered pair: E(x,y) implies S(x,y) | Refuted in every dimension n ≥ 2. |
| Existential ordered pair: some E pair implies some S pair | Refuted in every dimension n ≥ 2; the counterexample has no S pair in any finite Kraus representation. |

The Scribe claim's `Proved` kind refers to this combined classification,
whose statement includes the counterexample. It does not label either
E ⇒ S assertion as proved.

## Motivation

The necessary test and the stronger sufficient test offer different
Kraus-space descriptions of elementary right division. Identifying which
one is exact determines whether the diagonal tests are essential to
existence of a divisor. The formal anchor is
`D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.result`.

## Gap

The source supplies E ⇒ N and S ⇒ E. The converse N ⇒ E must cover
singular Choi matrices, and failure of E ⇒ S at one chosen pair does not
settle the existential reading. The classification therefore also requires
a channel with an E pair and no S pair at all, uniformly in dimension and
independently of its finite Kraus representation.

## Route

Use the source's input-first Choi convention and the complex
Hilbert–Schmidt complement. With A = C(Φ) and
Z = (|y⟩⟨x|)ᵀ ⊗ I, the necessary tests give the support inclusion
ker A ⊆ ker(ZA Z*). Finite-dimensional positive-semidefinite domination
then provides t > 0 with A − t ZA Z* positive semidefinite. The exact
inverse-filter congruence is the Choi matrix of the residual. Both inverse
identities and trace preservation give an actual residual CPTP right
factorization.

For distinct basis vectors eᵣ,eₛ, take Φ = Ψ₁₅⁄₁₆(eᵣ,eₛ) and
Q = Ψ₃⁄₄(eᵣ,eₛ). The identity Q composed with Q = Φ gives an E pair.
The diagonal Hilbert–Schmidt tests exclude every S pair. The intrinsic
kernel description transfers this obstruction to every finite Kraus
representation of Φ. Thus one dimension-uniform construction refutes
both readings of the stronger converse.

## Falsifier

A mismatch with the source's composition order, elementary channel,
complex Kraus span, complement or ordered-pair quantifiers would invalidate
the claimed interpretation. For the affirmative cells a counterexample
would be an actual CPTP map and Kraus representation with N but no E at
the same pair. For the negative cells an S pair in any finite representation
of the displayed Φ would invalidate the universal no-S-pair claim.
No conclusion about the separate rank-reduction assertion of Theorem 1
is included.

## Evidence

The kernel-checked theorem
`D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.result`
contains finite Kraus existence for every actual CPTP map, both N iff E
readings, the elementary inverse and residual-factorization facts, and the
counterexample with no S pair in every finite representation. Complete
positivity ranges over every finite ancillary amplification; trace
preservation ranges over every matrix. The Blueprint states the same
quantifiers and the Library note `vomende2024divisibility` binds the source
locators and quoted question.

The proof uses only the accepted standard axioms Classical.choice,
Quot.sound and propext. These mathematical statements establish no physical
gate implementation, local-operations protocol, resource cost, preparation
yield, NativeQ bridge, or AURIC/QFT realization.

## Triage

The combined classification is a theorem under the declared formal
interpretation. Admission uses the external open-problem-resolution
exception, with `proof_shape: bind-only` and no escape-witness claim.
The preregistration is
[issue 17562](https://github.com/the-omega-institute/trureturing/issues/17562#issuecomment-6379823896).
This classification answers the source question in the stated scope;
it makes no broader literature-priority or originality claim.

## ASSUMED-UNVERIFIED

The journal full text has not been checked against arXiv v3; the DOI
identifies the publication and does not assert journal/arXiv equivalence.
The literature check is bounded to the supplied source and prior independent
adjudication; no fresh exhaustive literature or priority search is claimed.
Source-to-formal-statement fidelity is a reviewed interpretation, rather
than a theorem about natural-language equivalence.

The escape-registration audit remains unfinished under the existing linked
issue exception, [issue 20941](https://github.com/the-omega-institute/trureturing/issues/20941).
No Reg source or `declared_validated` registration is supplied. The issue
is an unfinished-audit disclosure and supplies no registration evidence.
