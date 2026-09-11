---
bibkey: baumgratz2014coherence
authors: T. Baumgratz, M. Cramer, M. B. Plenio
year: 2014
title: Quantifying Coherence
doi: null
url: https://arxiv.org/abs/1311.0275v3
claim: Relative entropy of coherence is the entropy gain under diagonal pinching and vanishes exactly for diagonal states; coherent-copy correlation and unnormalized spectral-readout equality follow by the explicit reductions below.
strata_touched:
  - D5/S3/Quantum/Information/CoherentCopyCorrelationTax
  - D5/S3/Quantum/Divergence/SpectralReadoutEntropyEquality
license: citation-only
triage: anchor
---

# Coherence and equality under diagonal readout

## Verified locator

The exact upstream locator is:
https://arxiv.org/abs/1311.0275v3

The retrieved arXiv PDF identifies itself as arXiv:1311.0275v3 and gives the
title and authors above. Its printed and PDF page numbers agree. Page 2
defines incoherent states as the diagonal density matrices, equation (3),
and states condition (C1'): the measure is zero iff the state is incoherent.
Page 3, paragraph “Relative entropy of coherence,” explicitly says that the
relative entropy of coherence fulfils (C1'). Immediately before equation
(8) it displays, for diagonal delta,

    D(rho||delta) = S(rho_diag) - S(rho) + D(rho_diag||delta).

Equation (8) is C_rel.ent.(rho) = S(rho_diag) - S(rho). Thus setting
delta = rho_diag gives D(rho||rho_diag) = S(rho_diag) - S(rho).
These are interior readings of v3, not an attribution of equation (7).
Use one logarithm base consistently; conversion to nats scales both sides
by the same positive constant and preserves the equality criterion.

## Coherent-copy correlation

The standard construction R = V rho V*, V|i> = |i,i>, has both actual
marginals Delta(rho) and S(R) = S(rho). The entry, partial-trace and
isometric-invariance derivations are given in
`D5/L/Quantum/watrous2018entropicidentities`, using Watrous equations
(1.120)–(1.121), (2.34), (5.91) and Proposition 5.19. Consequently

    I(S:R) = 2 S(Delta(rho)) - S(rho)
           = S(Delta(rho)) + D(rho||Delta(rho)).

This proves the correspondence for `coherent_copy_correlation_tax` by direct
substitution. It is not a claim that the paper names a “correlation tax”
theorem. The joint state retains rho's coherences, so its entropy is S(rho).

For singular rho, positivity implies |rho_ij|^2 <= rho_ii rho_jj.
Thus a zero diagonal entry forces its row and column to vanish, and
supp(rho) is contained in supp(Delta(rho)). The finite relative-entropy
formula therefore agrees with the repository's zero-log convention on the
inputs used here; this does not identify that totalized definition with
infinite-valued relative entropy on arbitrary unsupported pairs.

## Spectral readout, including unnormalized inputs and repeated eigenvalues

Let x_j >= 0, A = U diag(x) U*, and Delta(A) its diagonal part. If
t = sum_j x_j = 0, every x_j is zero, so A = 0 and both entropies vanish.
If t > 0, rho = A/t is a density matrix. The verified (C1') and equation
(8) imply

    S(Delta(rho)) = S(rho) iff rho is diagonal.

Write p_i = A_ii. The spectral entropy formula and the scalar scaling
identity, valid also at zero, give

    S(A/t) = H(x)/t + ln t,
    S(Delta(A/t)) = H(p)/t + ln t.

Cancel ln t and multiply by t. Hence H(p) = H(x) iff A is diagonal,
which is `spectral_readout_entropy_eq_iff_isDiag` on its entire nonnegative,
unnormalized domain. The empty index type, also allowed by Lean, is the
zero-sum case. Neither positive definiteness nor distinct eigenvalues is used.

The Lean proof uses strict Jensen equality for f(s) = s ln s. With
M_ij = |U_ij|^2 it gives M_ij != 0 implies x_j = p_i. This means that a
row can mix equal eigenvalues. It does not force M to be a permutation
matrix. Instead U diag(x) = diag(p) U; multiplying by U* proves diagonality.
For example, x constant permits every unitary U, including a Hadamard
matrix. This is the precise equality condition used in the formal proof.

## What this note does and does not attest

Attested by this repository's own retrieval: the v3 PDF, pages 2–3,
condition (C1'), the paragraph explicitly applying it to relative entropy
of coherence, the decomposition before equation (8), and equation (8).
The coherent-copy substitution, support check and unnormalized scaling
argument above were checked here against the repository's actual domains.

Not attested here: the original references [22]–[29] cited by the paper,
their interior proofs, or a priority claim for these consequences. Those
underlying historical attributions remain `ASSUMED-UNVERIFIED` here.
The paper's explicit statement that its measure fulfils (C1') is a verified
reading of this paper, not a claim to have independently retrieved every
source used in its proof.
