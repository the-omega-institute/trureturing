---
bibkey: choijohnstonkribs2009multiplicative
authors: Man-Duen Choi and Nathaniel Johnston and David W. Kribs
year: 2009
title: The multiplicative domain in quantum error correction
doi: 10.1088/1751-8113/42/24/245303
arxiv: 0811.0947
strata_touched:
  - D5/S3/Quantum/Recovery/KrausLeftInverseNecessity
  - D5/S3/Quantum/Recovery/MatrixUnitDecoder
  - D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness
license: citation-only
triage: anchor
---

# Equality defects, multiplicative domains and exact correction

Primary source: https://arxiv.org/abs/0811.0947
Published article: https://doi.org/10.1088/1751-8113/42/24/245303
Journal of Physics A: Mathematical and Theoretical 42, 245303 (2009).
The arXiv preprint was submitted on 6 November 2008.

The authors connect multiplicative domains of completely positive maps with
quantum error correction and give a representation-theoretic description of
subsystem codes. The equivalence with unitarily correctable codes in the unital
case must retain that hypothesis; the nonunital situation is different.

The repository uses the following self-contained finite-matrix equality-defect
argument as a consumer. If Phi(X) = sum_b F_b X F_b* is the identity on every
matrix, then for every X,

    sum_b [F_b,X][F_b,X]*
      = Phi(XX*) - Phi(X)X* - X Phi(X*) + X Phi(I)X* = 0.

Positivity forces every commutator to vanish. Testing matrix units then makes
each F_b a scalar matrix. Applying this to an actual composition of two finite
Kraus families derives the necessity of the Knill-Laflamme scalar error-product
condition without taking Choi rank-one scalarity as an unproved premise.

This elementary identity is provided with its own proof. The paper is an
acknowledged conceptual and classical-literature anchor, not a claim that the
paper states this exact Lean API. A condition only on Phi(I) is insufficient.
No general multiplicative-domain classification is claimed by these modules.

The computed-recovery consumer takes any actual finite Kraus left inverse A
and constructs its observable map Y(X) = sum_b A_b* X A_b. Composite-Kraus
scalarity gives Y(X) E_a = E_a X. Consequently Q Y(X) = Y(X) Q = N(X),
and Mathlib's existing cfc commutation theorem implies that W commutes with
Y(X). The computed identity W Q W = P then proves the actual spectral
transpose candidate recovers X. This argument does not assume that Y is a
multiplicative representation on the whole physical algebra.
