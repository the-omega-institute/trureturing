---
bibkey: cowtanburton2024csssurgery
authors: "Alexander Cowtan; Simon Burton"
year: 2024
title: "CSS code surgery as a universal construction"
doi: 10.22331/q-2024-05-14-1344
url: https://arxiv.org/abs/2301.13738v6
claim: "Appendix D, Conjecture D.1 asks whether pushouts of basis-preserving monic spans of LDPC CSS complexes remain LDPC."
strata_touched:
  - D5/S3/Quantum/Information/CssMonicPushoutLdpc
license: citation-only
triage: anchor
---

# CSS code surgery as a universal construction

Alexander Cowtan and Simon Burton, “CSS code surgery as a universal construction,”
*Quantum* 8 (2024), 1344, arXiv:2301.13738v6.

Definition 3.4 says that a chain map is basis-preserving when every matrix at
each component maps basis elements to basis elements. Definition 5.1 describes
the componentwise pushout and Lemma 5.4 gives a basis-preserving choice. Section
4.1 defines LDPC families by bounded row and column Hamming weights. Appendix D,
Conjecture D.1 asks whether a family of basis-preserving monic spans of
Z-type complexes of quantum LDPC codes has an LDPC pushout family.

Appendix D, Conjecture D.1 (Appendix D) states: “Let C• ←f• A• →g• D• be a basis-preserving monic span in Ch(MatF2), and let Q• be the pushout chain complex of this monic span. Further, let the monic span be a representative of a family of monic spans which are parameterised by some n ∈ ℕ, and let A•, C• and D• be the Z-type complexes of quantum LDPC codes. Then (Q•, Q•) is also LDPC.”

The formal statement uses length-two complexes over `ZMod 2`, basis functions on
`Fin` dimensions, the quotient basis from Lemma 5.4, and the row and column
weight definitions from Section 4.1. The source's parameterisation phrase is
read as an arbitrary natural-indexed family. The settlement proves the explicit
single-span row and column bounds and therefore the family conclusion. The
literature screen recorded in issue #19488 is incomplete; the thesis check and
full novelty status remain ASSUMED-UNVERIFIED.

## Verified locator

- DOI: 10.22331/q-2024-05-14-1344
- Source: https://arxiv.org/abs/2301.13738v6
