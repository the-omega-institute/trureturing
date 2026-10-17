---
slug: anholcer-hypergraph-alon-tarsi
bibkey: anholcer2026alontarsi
doi: 10.37236/15173
url: https://arxiv.org/html/2501.00157v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result
---

# The fixed-polynomial hypergraph Alon-Tarsi bound

Conjectures 4 and 28 of Anholcer et al., *Electronic Journal of Combinatorics*
33(3), P3.74 (arXiv:2501.00157v2), assert AT(p) ≤ 2 ceil(ed(H)) + 1 for every
hypergraph polynomial, respectively every fully unbalanced hypergraph polynomial.
The field is arbitrary; multiple edges are allowed. Each edge has at least two
vertices and every incident coefficient is nonzero. Full unbalance requires two
unequal incident coefficients on each edge. Density counts induced occurrences
over nonempty vertex subsets, and AT uses nonzero maximum-total-degree monomials.

Three full edges on three vertices over F3, each with coefficients (1,1,-1),
are jointly admissible. The polynomial equals x^3+y^3-z^3 by Frobenius, so its
AT number is four, while its density is one and the proposed bound is three.
The joint certificate and closed negation are in
`D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation`.

Both labels describe one related family. Characteristic-zero and simple-hypergraph
variants and the coefficient-permutation theorem are outside this refutation.
Prior publication and global priority are **ASSUMED-UNVERIFIED**; no claim of
priority is attached to the native proof.
