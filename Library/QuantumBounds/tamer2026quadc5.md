---
bibkey: tamer2026quadc5
authors: Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu
year: 2026
title: "The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices"
doi: null
url: https://arxiv.org/abs/2605.12828v3
claim: "An exhaustive search over the 11,117 connected eight-vertex graphs ranks exclusivity graphs by the gap between the Lovász number and the independence number. For the dimension-restricted value η_d (Eq. (13)) and the minimum dimension d* (Eq. (25)), the Wagner graph and the rank-5 graph show no three-dimensional violation in the numerical search; the paper states that d* = 4 for them is numerically indicated and that a rigorous three-dimensional upper bound is not established."
strata_touched:
  - D5/S3/Quantum/Contextuality/EightVertexQutritBound
license: citation-only
triage: anchor
---

# Tamer–Ünal–Dizdar–Gedik–Müstecaplıoğlu, the Quad-C₅ graph

U. Tamer, B. Ünal, A. Dizdar, Z. Gedik and Ö. E. Müstecaplıoğlu, *The Quad-C₅ Graph: Maximum Contextuality Gap on Eight Vertices*, arXiv:2605.12828v3 [quant-ph] (29 September 2026; v1 12 May 2026).

## Verified locator

Primary version read: https://arxiv.org/abs/2605.12828v3 (the latest arXiv version).
Source: https://arxiv.org/pdf/2605.12828v3 (text read from the PDF):
- §III, Eq. (11)–(13), the dimension-restricted value η_d, and Eq. (25), the minimum dimension d*;
- §IV, the paragraph on the Wagner graph;
- Appendix B, Table V(a) with its † footnote and Table VI, the edge lists.

## Source statements

Eq. (13): "η_d(G) = max over {|v_i⟩} ⊂ ℝ^d with ⟨v_i|v_i⟩ = 1 and ⟨v_i|v_j⟩ = 0 ∀(i,j) ∈ E of λ_max(Σ_{i=1}^n |v_i⟩⟨v_i|)."

Eq. (25): "d*(G) = min{d : η_d(G) > α(G)}."

§IV: "The Wagner graph shows a contrasting behavior. In all of our three-dimensional searches, the largest value found is equal to its noncontextual bound, η₃(W) = 3 to the numerical precision of the optimization, so that no qutrit contextuality violation is found. … Because the fixed-dimension optimization is non-convex, failure to find a three-dimensional violation does not constitute a rigorous proof that none exists. A formal demonstration that d*(W) = 4 would require an independent upper bound on η₃(W)."

Table V(a): the Wagner graph (rank 3) and the rank-5 graph are listed with η₃ = 3.00000 and d* = 4†; footnote: "†Numerically indicated; a rigorous three-dimensional upper bound is not established here."

Table VI, edge lists: rank 3 (Wagner W), (0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0),(0,4),(1,5),(2,6),(3,7); rank 5, (0,3),(0,5),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7),(3,6),(3,7),(4,7),(5,7).
