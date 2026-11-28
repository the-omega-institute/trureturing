---
bibkey: liuzhangyuzhangji2026optimalcpecc
authors: Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji
year: 2026
title: Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes
doi: null
url: https://arxiv.org/abs/2611.34386v1
claim: Theorem 3.3 gives the sharp edge threshold for the clique-free deletion problem used in the small-deletion CPECC regime. Section 5 asks for optimal codes with positive even t below w−3.
strata_touched:
  - D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph
  - D5/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound
  - D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows
  - D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking
  - D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound
  - D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign
license: citation-only
triage: anchor
---

# Optimal bounds for constant-power error-correcting cooling codes

Section 2 defines the constant-weight support model. At correction radius
(w-2), symmetric difference of size at least (2w-3) is equivalent to
intersection of size at most one for two supports of weight (w).
Lemma 3.1 uses the Erdős–Gallai bound on a critical vertex cover. Lemma 3.2
bounds the size of an induced colorable subgraph by averaging over vertex orders.
The second edge estimate of Theorem 3.3, proved in Appendix A, supplies (B(w,t))
for a (K_{w+t})-free graph of minimum degree at least (w-1) that retains a
(w)-clique after deletion of (t) vertices. Theorem 3.4 uses an ambient edge
budget to bound the number of information classes.

Section 5 asks for optimal codes in the positive even-(t) regime below
(w-3), without specifying a length progression. The finite leave estimate
for the lengths in issue #35006 uses a local incidence deficit to refine
the ambient budget. A supplied uniform group divisible design provides one
class per block. Theorem 2.2 cites J. Liu's asymptotic uniform design
existence theorem.

## Verified locator

https://arxiv.org/abs/2611.34386v1

In the versioned source, Section 2 gives the support conditions and the
design definition. Section 3 contains Lemmas 3.1–3.2 and Theorem 3.3, with
the latter's proof in Appendix A. Section 5 contains the even-(t) question.
