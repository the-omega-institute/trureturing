---
bibkey: koprowski2026enumeration
authors: Brandon Koprowski, Joel Brewster Lewis
year: 2026
title: "Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices"
doi: 10.48550/arXiv.2602.22129
url: https://arxiv.org/abs/2602.22129v1
claim: "Section 4 supplies the orbit, Bruhat, triangular-invariance and augmented-cell count bridges; Section 5.1 identifies the actual eligible-permutation sum weighted by inv(sigma)+inv(pi)-h and asks for its general factorization."
strata_touched: []
license: citation-only
triage: anchor
---

# Nondegenerate hypermatrices and the published permutation-weight bridge

## Verified locator

DOI: 10.48550/arXiv.2602.22129

Immutable primary version: https://arxiv.org/abs/2602.22129v1.
Its mathematical text is also available at
https://arxiv.org/html/2602.22129v1.

The journal version is *Enumerative Combinatorics and Applications* 7:1,
Article S2R3, DOI 10.54550/ECA2027V7S1R3, available at
https://ecajournal.kms-ks.org/Volume2027/ECA2027_S2A3.pdf.
The article bears publication date August 21, 2026, although the volume is
labelled 2027. It is released under CC BY-ND 4.0. This note supplies citations
and mathematical scope, rather than a source-text or code port.

The following arXiv-version numbers are the numbers displayed in the primary
HTML text; the journal numbers are given separately because its theorem
environments use separate counters.

- Definition 4.4 (`wc`) gives $w=\sigma\bar\pi$ and
  $c=\bar\pi^{-1}(1\ 2\ \cdots\ k+1)\bar\pi$; hence
  $wc(i)=\sigma(\pi(i)+1)$ for $i\leq k$, and $wc(k+1)=\sigma(1)$.
- Theorem 3.3 (`thm:aitken`) supplies the free transitive action of the
  quotient by the scalar subgroup on nondegenerate tensors. The full matrix
  group consequently represents each such tensor $q-1$ times.
- Theorem 4.13 (`thm:bruhat`) and Remark 4.14
  (`rem:equivalent bruhat`) give the unique Bruhat decompositions used in the
  two factors. Their journal counterparts are Theorem 4.3 and Remark 4.2.
- Definition 4.16 (`def:augHM`) uses $A\in\sigma_*$ and
  $A'\in{}^*(\pi^{-1})$. The matrix multiplied on the right of each face is
  $(A')^{\mathrm T}\in{}^*\pi$. These transpose and inverse conventions are
  part of the supplier, not interchangeable choices of notation.
- Proposition 4.17 (`prop:pull off U`) gives the $q-1$ triangular/augmented
  representations of each nondegenerate tensor; Proposition 4.18
  (`prop:upper triangular`) states preservation of the two zero regions in
  both directions. Their journal counterparts are Propositions 4.2 and 4.3.
- Corollary 4.19 (`cor:count`; journal Corollary 4.2) relates the actual tensor
  count to the augmented-cell sum, with multiplier
  $q^{k^2}(q-1)^{2k}$. The two triangular group orders multiply to
  $q^{k^2}(q-1)^{2k+1}$, and the scalar fiber has size $q-1$.
- Propositions 4.24 and 4.25 (`prop:potentially bad entries in front face`
  and `prop:potentially bad entries in back face`; journal Propositions 4.5
  and 4.6) give the forbidden-entry criteria. The back criterion explicitly
  includes the distinguished target $j=k+1$; the front criterion excludes it.
- Proposition 4.28 (`prop:acyclic`) and Theorem 4.29 (`thm:power of q`;
  journal Proposition 4.7 and Theorem 4.4) supply the acyclic elimination of
  distinct coefficient-one final variables and the resulting cell counts.
- Section 5.1, “Proving the main conjecture,” displays the exact weighted
  sum over eligible pairs, with exponent
  $|\operatorname{Inv}(\sigma)|+|\operatorname{Inv}(\pi)|-h(\sigma,\pi;P)$.
  Here $h$ counts generically nonzero forbidden tensor entries, not nonzero
  values after a particular finite-field specialization.

## Hypotheses and use boundary

The objects in the tensor-count supplier are pairs of $(k+1)$-by-$k$ matrices
over a finite field, with both plane-partition zero regions, and Cayley's
second hyperdeterminant nonzero. Lemma 2.5 (`lem:faceSum`) states the
algebraic-closure criterion: every linear combination of the two faces with
coefficients in the algebraic closure, not both zero, has full column rank.
It is not a condition restricted to rational combinations over the base
finite field. The statement preceding that lemma restricts its
three-dimensional boundary formats to positive $k_1,k_2$; its direct
specialization with $k_1=1,k_2=k-1$ therefore requires $k\geq2$. The
$2\times2\times1$ case needs its own justification if this particular
lemma is used to connect a rank-defined count to a hyperdeterminant-defined
count. A size-zero permutation tail asserts no tensor-count statement.

The new [coupled low-row digit construction](../../docs/develop/theory/KOPROWSKI_LEWIS_COUPLED_DIGIT_BIJECTION.md)
uses the published row convention and forbidden-entry criteria to identify
$h=H_f+H_b$, then proves an explicit bijection and factors the actual weighted
permutation sum. The orbit, Bruhat, triangular-invariance and field-count
results above are the published suppliers connecting that sum to the original
tensor objects.

## Published general and special statements

Both the arXiv v1 text and the journal article's abstract and Section 5.1
retain the general factorization as a conjectural task; Section 5.1 says
that grouping the terms into the desired product had been unsuccessful.
Their proved special families and the unweighted hyperrook count are
published results, not new contributions of the digit construction.
