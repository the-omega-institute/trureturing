---
bibkey: chernfu2026signed
authors: Shane Chern, Shishuo Fu
year: 2026
title: "Signed counting of partition matrices"
doi: 10.48550/arXiv.2508.21318
url: https://arxiv.org/abs/2508.21318v2
claim: "Question 5.5 asks for a characterization of the fixed CDK image of improper partition matrices."
strata_touched:
  - D5/S3/Combinatorics/PartitionMatrix/ChernFuImage
license: citation-only
triage: anchor
---

# Chern and Fu, signed counting of partition matrices

The source is arXiv:2508.21318v2, Section 5, Question 5.5:

> Find a characterization (possibly in terms of pattern avoidance) of the inversion sequences produced by improper partition matrices under the action of the Claesson–Dukes–Kubitzke bijection.

Definition 1.1 specifies upper-triangular square set-entry matrices partitioning
[n], with each row and column nonempty and weakly increasing column indices as
labels increase. Following Theorem 1.2, the fixed map at label t sums the
cardinalities of columns strictly before row_P(t). Definition 2.1 calls a
same-column adjacent ascent or descent at i proper exactly when i has the
parity of the least label in its column. Equal rows form neither row order.

The whole-alphabet gap condition in ChernFuImage is a characterization of this
image. It uses A(e) = {e_1,...,e_n} and
b_e(i) = max({0} union {a in A(e) : a < i}). For every 1 <= i < n,
nonoccurrence of i and oddness of i - b_e(i) require e_i = e_(i+1).
The criterion is about all inversion sequences and all native dimensions.

Version v1 Question 5.5 is a different bijection problem, numbered Question 5.7
in v2. That separate problem is not the assertion here.

The source has the arXiv nonexclusive distribution license. It is cited as
mathematical literature; that license is not treated as a software license.
No third-party implementation is copied.

## Verified locator

DOI: 10.48550/arXiv.2508.21318; versioned source: https://arxiv.org/abs/2508.21318v2.
