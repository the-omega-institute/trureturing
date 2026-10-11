---
bibkey: carbone2012dynamical
authors: "Ingrid Carbone; Maria Rita Iacò; Aljoša Volčič"
year: 2012
title: "A dynamical system approach to the Kakutani-Fibonacci sequence"
doi: null
url: "https://arxiv.org/abs/1211.0708v1"
claim: "Definition 1 refines every longest interval at a fixed ratio; for the inverse golden ratio the partition lengths are consecutive powers and their counts satisfy the Fibonacci recurrence."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Kakutani–Fibonacci partition supplier

The primary version is arXiv:1211.0708v1. Definition 1 in §1, PDF p.2,
defines Kakutani's $\alpha$-refinement of a partition of $[0,1)$ by splitting
all intervals of maximal length into parts proportional to $\alpha$ and
$1-\alpha$. Shorter intervals are retained.

In §1, PDF p.4, the choice $\alpha=(\sqrt5-1)/2$ satisfies
$\alpha^2+\alpha=1$. The successive partitions have long intervals of
length $\alpha^n$ and short intervals of length $\alpha^{n+1}$; their long,
short and total counts satisfy the Fibonacci recurrence with the initial
values stated there. These facts are `literature-attested` ingredients.

[The single-lineage partition volume](../../docs/develop/theory/AURIC_FIB_SINGLE_LINEAGE_PARTITION_GEOMETRY.md)
consumes Definition 1 and the two-length relation in §§5.2–5.3. Its
identification with the labelled FIB process requires a single initial
$\beta$, the golden ratio, and the proof that precisely the $\beta$ intervals
are longest. An initial $\alpha$ adds a relabelling step before any split.

The paper also constructs an interval exchange and proves ergodic and
discrepancy results. Those results are not suppliers for the volume's fixed
read-point model: equality of partition lengths alone does not supply the
paper's point ordering or interval exchange. No such transfer is claimed.
