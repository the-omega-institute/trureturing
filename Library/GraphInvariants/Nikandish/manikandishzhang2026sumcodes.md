---
bibkey: manikandishzhang2026sumcodes
authors: Haobo Ma; Reza Nikandish; Wenlin Zhang
year: 2026
title: "Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences"
doi: 10.5281/zenodo.23375144
url: https://doi.org/10.5281/zenodo.23375144
claim: "Theorem 2.1 gives the complete two-case criterion for total perfect subgroup codes in a loopless Cayley sum graph."
strata_touched:
  - D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion
license: CC-BY-4.0 according to Zenodo metadata; the PDFs print no license statement
triage: anchor
---

# Corrected total perfect subgroup codes

Two distinct public versions were supplied. The original, DOI
`10.5281/zenodo.23360588`, has SHA256
`2b669404da5565a24f08c4a09a0335ec4f8895f03015ee5f20bf21c213ba61f5`.
The revision, DOI `10.5281/zenodo.23375144`, has SHA256
`5836035c7d1eb843b6ade0e8d0ecacc2c9c24540921ab95d47c66c0eb8d1dec3`.
Both are eight-page public preprints dated 14 October 2026. Their PDF byline is
Haobo Ma, Reza Nikandish, Wenlin Zhang, with Reza Nikandish corresponding author.
The deposited metadata orders the last two creators differently and contains
different affiliation spellings. These distinct identities are not silently
interchanged.

Theorem 2.1 and its proof in both versions concern finite groups, normal subsets
(unions of conjugacy classes), and the simple graph whose edges satisfy g!=h and
g*h in Y. The formal result independently proves both directions and both
branches for each fixed Y. It constructs the actual neighbor/coset bijection
with the square g*g erased, and derives the one-element nonsquare branch and the
two-element all-squares branch. It does not assume a target neighbor-count
package, an inverse-closed connection set or a normal subgroup H.

The antecedent [2] is Jun-Yang Zhang, *On subgroup perfect codes in Cayley sum
graphs*, Finite Fields and Their Applications 95 (2024), 102393,
DOI `10.1016/j.ffa.2024.102393`. The supplied body is arXiv:2210.03336v1
(7 October 2022), SHA256
`d99155eb80b283264c433d78cd6cd3e929508e7387fc12c6d03a6add16412532`;
identity with the final publisher PDF is unestablished. Jun-Yang Zhang is
distinct from coauthor Wenlin Zhang. The other antecedent [1] is Neda Ahanjideh,
Zeinab Akhlaghi and Bernardo G. Rodrigues, *On perfect codes and total perfect
codes in Cayley sum graph*, Journal of Algebraic Combinatorics 63 (2026),
Paper 52, DOI `10.1007/s10801-026-01523-w`, supplied publisher PDF SHA256
`b266b9b9f100111e84143ef2216a2722605d8ecaf687d4f3fca96ca17ceb45a8`.
The correction concerns necessity in the cited total-code criteria; their
surviving sufficiency is preserved. This module does not claim to formalize
their classification casework or reproduce their computational assertions.

The full received C1-C16 return also includes examples, normalization,
same-graph involution repair, centralizer/core results, regular classifications,
NLT inheritance and arbitrary-finite-group equivalence. This module does not
discharge those other outcomes. Source enumeration tables remain attributed
reports with the original missing reproduction evidence. Exhaustive
classification, unrestricted translation and connected-case boundaries remain
as received.

Both primary PDFs acknowledge Claude assistance with part of the computations
and checking, retaining author responsibility. Their public deposit does not
establish journal acceptance, replacement of FFA-26-615, an arXiv correction or
final approval by every author. No licensing, authorship, priority, submission
or publication decision is made here. The independently written Lean proof is
new; mathematical statements and attribution come from the cited sources.

## Attributed finite reports and reproduction boundary

O p5 computational paragraph/Table 1; R pp5-6 paragraph/Table 1: The authors report exhaustive enumeration of all subgroups and all normal connection sets of the 25 abelian groups of order at most 16, totaling 398350 connection sets. Adjacency was generated from distinct g,h with gh in Y; actual degrees decided regularity and every vertex's H-neighbor count decided TPC existence. Table 1 counts even-order subgroups admitting a TPC in some regular graph, with trivial subgroup excluded.

Stored finite enumeration report only. The caption 'Independent verification' is the authors' label; it is not this intake's independent execution, a universal proof, a kernel receipt, or historical acceptance. R removes O's separate claim that the paragraph verifies Z 5.3.

Retain the exact finite domain/count/table and provenance. Enumeration source, group encodings, raw outputs and reproducible receipts were not supplied/established; any future reproducibility claim needs those and an authorized fresh run or checked certificates. Universal C8 must be formalized independently of finite agreement.

O p6/R pp5,7 Remark 3.6: The authors report 133088 (G,Y,H) triples across all normal Y and all H for D2n with n in {3,4,6,8,10,12,14,16}, and AGL1(q) with q in {3,5,7}, including identity-containing, empty and full Y. Direct adjacency, neighbor counts and connected-component searches found that connected (b) examples all had |S(H)|=1 and came from adding 1 to an (a) connection set which could itself be disconnected; found |S(H)|=2 examples were disconnected.

A finite observation over the specified family models, with no inference that all finite groups behave this way and no deduplication claim for isomorphic groups appearing in both families. Core restrictions from C6 remain available. No enumeration was executed by this intake.

Retain report/domain/count separately from universal claims and obtain actual computation provenance before claiming reproducibility. Universal connected-(b) classification or a theorem that |S(H)|=2 forces disconnection is not proved here.

The exact transcribed abelian table follows. These entries are source reports; no enumeration or independent reproduction is claimed.

| Group | Order | Square-set size | Subgroups | Even subgroups with regular TPC |
|---|---:|---:|---:|---:|
| C1 | 1 | 1 | 1 | 0 |
| C2 | 2 | 1 | 2 | 1 |
| C3 | 3 | 3 | 2 | 0 |
| C4 | 4 | 2 | 3 | 2 |
| C2 x C2 | 4 | 1 | 5 | 4 |
| C5 | 5 | 5 | 2 | 0 |
| C6 | 6 | 3 | 4 | 2 |
| C7 | 7 | 7 | 2 | 0 |
| C8 | 8 | 4 | 4 | 1 |
| C4 x C2 | 8 | 2 | 8 | 7 |
| C2^3 | 8 | 1 | 16 | 15 |
| C9 | 9 | 9 | 3 | 0 |
| C3 x C3 | 9 | 9 | 6 | 0 |
| C10 | 10 | 5 | 4 | 2 |
| C11 | 11 | 11 | 2 | 0 |
| C12 | 12 | 6 | 6 | 2 |
| C6 x C2 | 12 | 3 | 10 | 8 |
| C13 | 13 | 13 | 2 | 0 |
| C14 | 14 | 7 | 4 | 2 |
| C15 | 15 | 15 | 4 | 0 |
| C16 | 16 | 8 | 5 | 1 |
| C8 x C2 | 16 | 4 | 11 | 8 |
| C4 x C4 | 16 | 4 | 15 | 10 |
| C4 x C2 x C2 | 16 | 2 | 27 | 26 |
| C2^4 | 16 | 1 | 67 | 66 |

Rendered superscripts/subscripts resolve the extraction artifacts C32 and C42 as C2^3 and C2^4. Values are transcribed source reports, not newly computed results.
