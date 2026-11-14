---
bibkey: creedcryan2013eulertours
authors: Paidi Creed; Mary Cryan
year: 2013
title: "The number of Euler tours of random directed graphs"
doi: 10.37236/2377
claim: "The classical BEST formula counts Euler tours modulo cyclic rotation in positive strongly connected Eulerian directed multigraphs, including loops and parallel arcs."
strata_touched:
  - D5/S3/Combinatorics/Graph/LinearForests/CompatibleCycleInventory
license: citation-only
triage: anchor
---

# Positive-inventory Euler tours

## Verified locator

DOI: 10.37236/2377

Electronic Journal of Combinatorics 20(3) (2013), P13. Theorem 1,
pages 2–3; the cyclic-rotation convention is defined on pages 1–2.
The discussion following Theorem 1 and footnote 1 on page 3 explicitly
extend the formula to loops and parallel arcs.

## Mathematical scope

Theorem 1 states the classical BEST formula: for an Eulerian directed
graph and any root v, the number of Euler tours modulo cyclic rotation
is the number of spanning in-arborescences rooted at v multiplied by
the product of (outdegree(u)-1)! over the vertices u. The paper credits
Smith and Tutte and de Bruijn and van Aardenne-Ehrenfest for BEST.
Its setting has positive outdegrees and strong connectivity.

For the positive crossing inventory in CompatibleCycleInventory, each
actual label x is an arc from s(x) to d(x) on the two Bool vertices.
There are m arcs in each direction, p loops at false and q loops at true.
When m is positive this graph is strongly connected. An in-arborescence
rooted at either vertex chooses one of the m arcs from the other vertex,
and the two outdegrees are m+p and m+q. BEST therefore gives
m(m+p-1)!(m+q-1)!. The permutation successor of each arc identifies a
cyclic ordering of these same labelled arcs, retaining loops and parallel
arcs as distinct labels.

This is provenance for the positive-inventory formula. The Lean proof
uses strong induction with exhaustive loop deletion/insertion and a
two-fiber first-return equivalence, without importing a general BEST
theorem. Its empty-carrier and disconnected zero-crossing clauses and
the complete raw-forest endpoint classification are local synthesis;
Theorem 1 is not cited as a verbatim source for those complete statements.
No literature priority is claimed. The ordinary contraction source and
its separate permission and license notices remain documented in
[the Tsaban note](tsaban2003permutation.md) and
[the Liu–Ye note](liuye2026cyclesupport.md).

## Use and license

This note cites and paraphrases the mathematical source. It imports no
source code and reproduces no article license or licensed proof text.
The licenses of the Lean suppliers remain in their own source notices.
