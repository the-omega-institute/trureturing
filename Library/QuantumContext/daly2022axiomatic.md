---
bibkey: daly2022axiomatic
authors: P. C. Daly
year: 2022
title: Axiomatic Approach to Quantum Superchannels
doi: 10.48550/arXiv.2210.00370
url: https://arxiv.org/abs/2210.00370v1
claim: "Remark 4.1 asks whether superchannel extensions with minimum reduced Choi rank are extreme points of the extension set."
strata_touched:
  - D5/S3/QuantumChannels/DalySuperchannelMinimalExtension
license: citation-only
triage: anchor
---

# Quantum superchannel extensions and extremality

## Verified locator

DOI: 10.48550/arXiv.2210.00370

Source: https://arxiv.org/abs/2210.00370v1

## Source statements

Section 2, p. 3:

> Now any linear map is determined by its action on basis elements so for a linear L : M_d → M_r we get a vector space isomorphism from L(M_d, M_r) onto M_d(M_r) via L ↦ (L(E_{i,j})).

Remark 3.3, p. 4:

> A tensor product of linear maps gives a map on the tensor product of the spaces so there is an inclusion

Definition 3.1, p. 3:

> Given positive integers d, r ≥ 1 define SCPTP(d, r) := span{φ | φ : M_d → M_r is a CPTP map} ⊂ L(M_d, M_r). Also define S(d, r) ⊂ M_d(M_r) to be the set of block matrices (P_{i,j}) such that for all 1 ≤ i, j ≤ d, Tr(P_{i,i}) = Tr(P_{j,j}) and for i ≠ j Tr(P_{i,j}) = 0.

Definition 3.4, p. 5:

> Given two spaces of quantum channels SCPTP(d_i, r_i), i = 1, 2, a QSC is a linear map Γ : SCPTP(d_1, r_1) → SCPTP(d_2, r_2) which satisfies (1) if φ is CPTP then Γ(φ) is CPTP (2) given any other dimensions d_3, r_3 ∈ ℕ and the identity map id_{d_3,r_3} : SCPTP(d_3, r_3) → SCPTP(d_3, r_3) then Γ⊗id_{d_3,r_3} : SCPTP(d_1, r_1)⊗SCPTP(d_3, r_3) → SCPTP(d_2, r_2)⊗SCPTP(d_3, r_3) sends CP maps to CP maps.

After Definition 3.4, p. 5:

> If Γ is a QSC it induces a map Γ̃ : S(d_1, r_1) → S(d_2, r_2) via Γ̃ = R_2 ∘ Γ ∘ R_1^{−1}.

Remark 3.7, p. 6:

> a quantum superchannel is a linear map S : L(M_{d_1}, M_{r_1}) → L(M_{d_2}, M_{r_2}) which satisfies • CP preserving: S sends CP maps to CP maps • Completely CP preserving: For any d, r if id_{d,r} is the identity map acting on L(M_d, M_r) then S ⊗ id_{d,r} is CP preserving • TP preserving: S sends TP maps to TP maps

Theorem 3.8, p. 6:

> Every QSC extends to a quantum superchannel.

Section 4, p. 10:

> The dimension e can be chosen to be the rank of Tr_{r_1} Tr_{r_2} C_{Γ̃}

Remark 4.1, p. 11:

> The set of possible superchannel extensions of a QSC is a convex set. In the example given the extensions with minimal e are extreme points. A natural question to ask is whether it is generally true that the extensions which give minimal dimensions e are extreme points.

The Choi coordinates are input-first: the entry indexed by (i,k),(j,l)
is φ(Matrix.single i j 1) k l. All matrix indices start at zero in Fin n.
The extension set is considered over real scalars, and e is the rank after
tracing out both output factors, without replacing it by another memory measure.

## Scope

The two-qubit construction refutes the universal assertion that every minimizer
is extreme. It does not refute the existence of an extreme minimizer.
Literature completeness is ASSUMED-UNVERIFIED: the preprint was read, while the repeated question in Daly's thesis is reported by the preregistration; the published Lie–Jeong
article and Wilson's full thesis were not verified.
