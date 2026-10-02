---
bibkey: kowshik2011functioncomputation
authors: Hemant Kowshik and P. R. Kumar
year: 2011
title: Optimal Function Computation in Directed and Undirected Graphs
doi: 10.48550/arXiv.1105.0240
url: https://arxiv.org/abs/1105.0240v2
claim: On a rooted directed tree, every feasible node encoder separates distinct completion responses, and response-class encoders simultaneously attain the minimum message alphabet at all nodes.
strata_touched:
  - D5/S3/Arith/FibonacciAtomic/TreeMessageRealization
license: arXiv.org perpetual non-exclusive license
triage: anchor
---

# Tree computation by completion responses

Section III-B, Lemma 1 and Theorem 4, concern a directed tree with a designated
collector. Each node reads its own coordinate and the complete messages of its
children, and transmits once toward its parent. Correctness is required on the
entire Cartesian product of coordinate alphabets.

Lemma 1 requires each node's encoder to distinguish two subtree assignments
whenever some common complementary assignment gives different task outputs.
The construction preceding Theorem 4 uses the distinct completion-response
functions themselves as the node's message alphabet. A parent chooses fixed
nominal representatives of its children's response classes and computes its own
completion response. Theorem 4 proves correctness by induction over the tree.
The paragraph following its proof identifies these alphabets as simultaneously
optimal at all nodes.

Leaf-only input is the specialization in which every internal node has a
singleton local alphabet. Counting the root output as its complete message
adds the task's output range to the node counts. The source does not assert
the four-message rigidity of the ordered five-window Boolean task.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1105.0240
- URL: https://arxiv.org/abs/1105.0240v2
- Original text: https://arxiv.org/pdf/1105.0240v2, Section III-B, Lemma 1,
  Theorem 4, and the optimal-alphabet paragraph following Theorem 4,
  printed pages 11--13.
