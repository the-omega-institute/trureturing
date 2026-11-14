---
bibkey: chomicz2026minimalpresentations
authors: Kazimierz Chomicz
year: 2026
title: The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four
doi: 10.48550/arXiv.2609.04000
url: https://arxiv.org/abs/2609.04000v1
claim: "The question after Lemma 3.13 asks whether both b_22 d_2 and b_33 d_3 are Betti elements for ordered secondary numerical semigroups."
strata_touched:
  - D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti
license: citation-only
triage: anchor
---

# Chomicz: secondary boundary Betti degrees

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2609.04000

Source: https://arxiv.org/abs/2609.04000v1

Primary source: https://arxiv.org/src/2609.04000v1, `main.tex`, 133954 bytes, SHA-256 `72491fa23b6b1168a957e974a28c28411044e06ffa4cd78edcee7762f4492ec1`. The locators below refer to this version's source, not mutable line numbers in repository mathematical declarations.

## Definitions and ordering

Lines 178–190 define the least positive critical coefficients and the least positive coefficients admitting a relation with positive coordinate at the distinguished generator. The off-diagonal relation coefficients need not be unique. The formal definitions quantify over all such relation witnesses; unused diagonal positive-data slots are set to zero.

Lemma 2.2 yields two distinct critical degrees and an arrangement into two critical pairs. Line 230 explicitly adopts the full fibers
$\varphi^{-1}(a_{00}d_0)=\varphi^{-1}(a_{11}d_1)=\{(a_{00},0,0,0),(0,a_{11},0,0)\}$ and
$\varphi^{-1}(a_{22}d_2)=\varphi^{-1}(a_{33}d_3)=\{(0,0,a_{22},0),(0,0,0,a_{33})\}$.
This is the source ordering convention, not increasing numerical order. Line 228 defines primary by equality of critical and distinguished-positive coefficients at two distinct other indices; secondary means nonprimary. The convention persists into Section 3.2.

## Question after Lemma 3.13

Line 1050:

> However, we do not know whether $b_{22}d_2$ and $b_{33}d_3$ are Betti elements. This gap will not affect the results of Section \ref{section_type}, so we leave it unresolved.

The paper abbreviates $b_{0,ii}$ to $b_{ii}$. Both indices are part of this question. The paper does not assert the repository's stronger gcd classification or graph alternatives.

## Chain interpretation

Lines 469–470 print chains in ambient $\mathbb N^4$ before discussing classes of a fixed fiber. Unrestricted ambient chains connect any two nonzero vectors through their sum. The formalization instead uses chains inside the entire fixed factorization fiber. This reading is supported by the fixed-fiber minimal-presentation theorem at lines 477–480, the fixed-degree chains in Lemma 3.13 and the Betti assertions at line 1050. It is an explicit interpretation, not an equivalence with the unrestricted printed relation. The Reg mirror proves the fixed-fiber reachability bridge and separately the ambient-chain observation.

## Attribution and literature boundary

The ordinary classification argument is reused from public [issue #28454](https://github.com/the-omega-institute/trureturing/issues/28454), credited to producer `07b67e50-10a4-41b3-9622-660f37c654a5` and its research contributor. [Issue #29790](https://github.com/the-omega-institute/trureturing/issues/29790) registers an independent audit/formalization of that candidate. This is attributed formalization/reuse, not rediscovery.

The primary v1 text attests the definitions, ordering and open question. The preregistration reports a bounded source/ownership/Lean-supplier screen without an exact proved supplier in that scope. This note does not independently extend that screen or certify worldwide openness, priority or exhaustive literature coverage. The stronger classification is repository-derived from the attributed argument; no literature theorem asserting it is cited.

The [question dossier](../../Problems/chomicz-2026-secondary-boundary-betti.md) gives the complete registered scope, proof mechanism and unresolved certification boundaries. The source is cited rather than redistributed.
