# A characteristic-three hypergraph Alon-Tarsi counterexample

## Abstract

One fully unbalanced F3 multihypergraph refutes the two printed fixed-polynomial AT bounds.

**Definition 1.1 (Three edge occurrences).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.edge`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.edge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

Each of the three distinct occurrence indices maps to the full set Fin 3. Equal vertex sets retain separate multiplicities.

**Definition 1.2 (Induced occurrence density).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.density`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.density` (`✓ std3`).

*Citation.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

For each nonempty vertex subset S, count occurrence indices e with H(e) contained in S and divide by the number of vertices of S; take the maximum. This is the source density, with no trace or simple-edge replacement.

**Definition 1.3 (The top-degree AT bound).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.ATAtMost`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.ATAtMost` (`✓ std3`).

*Citation.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

ATAtMost(p,k) means that some exponent vector has nonzero coefficient, exponent sum equal to the total degree of p, and every exponent strictly below k. For nonzero p in finitely many variables this is exactly AT(p) ≤ k under the source convention: maximum individual exponent plus one, minimized over nonzero monomials of maximum total degree. Formal polynomials are used throughout.

**Definition 1.4 (The occurrence-indexed edge product).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.edgePolynomial`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.edgePolynomial` (`✓ std3`).

*Citation.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

The product ranges over edge occurrences. Its factor at occurrence e is the sum of a(e,v) times X(v) over incident vertices. The coefficient array may depend on both e and v.

**Definition 1.5 (Printed Conjecture 4).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.Conjecture4`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.Conjecture4` (`✓ std3`).

*Citation.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

Anholcer et al., Conjecture 4, journal pp. 5 and 23, asserts AT(p) ≤ 2 ceil(ed(H)) + 1 for every hypergraph polynomial p. The predicate quantifies over arbitrary fields, all finite numbers of vertices and occurrences, all indexed edge sets with edge sizes at least two, and all nonzero incident coefficients. Fin n enumerates the finite vertex set; n is positive so the maximum over nonempty subsets is defined. The supplied polynomial is fixed, with no coefficient permutations.

**Definition 1.6 (Printed Conjecture 28).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.Conjecture28`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.Conjecture28` (`✓ std3`).

*Citation.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

Conjecture 28, journal p. 23, adds that every edge is unbalanced: there are two incident vertices with unequal coefficients. This means the coefficients are not all equal, and does not impose pairwise distinctness or a zero sum. The remaining parameters and bound are those of Conjecture 4.

**Definition 1.7 (The polynomial over F3).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.polynomial`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

Take p = (X(0) + X(1) − X(2))³ over the genuine field ZMod 3. The source vertices 1,2,3 correspond to indices 0,1,2.

**Theorem 1.8 (Agreement with the actual edge product).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.polynomial_from_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.polynomial_from_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

The polynomial is exactly the product of the three indexed linear factors, with coefficients (1,1,−1) on each occurrence. This identical assignment is a choice of witness; the universal predicates permit arbitrary occurrence-dependent coefficients.

**Theorem 1.9 (Characteristic-three cancellation).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.frobenius_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.frobenius_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

The characteristic-three Frobenius identities give p = X(0)³ + X(1)³ − X(2)³. The proof directly applies the pinned Mathlib characteristic-power identities.

**Theorem 1.10 (Exact density).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.density_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.density_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

Every proper vertex subset induces zero occurrences. The full set induces three edges on three vertices, so ed(H) = 1.

**Theorem 1.11 (Exact AT threshold).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.exact_AT_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.exact_AT_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

For every natural k, ATAtMost(p,k) holds if and only if 4 ≤ k. All coefficient vectors with every exponent at most two have zero coefficient, while X(0)³ has coefficient one and total degree three. Thus AT(p) = 4.

**Theorem 1.12 (One jointly admissible source witness).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.source_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.source_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

This closed certificate joins edge size at least two, nonzero coefficients, full unbalance, the actual occurrence-indexed product, density one, total degree three, the exact AT threshold for every k, and failure at the conjectured bound. The incident coefficients 1 and −1 differ in F3. Every premise belongs to the same witness.

**Definition 1.13 (The two source statements as one family).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

The claim is the disjunction Conjecture4 or Conjecture28. Negating it refutes both printed universal statements using the same fully unbalanced witness.

**Theorem 1.14 (Both universal statements are false).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/anholcer-hypergraph-alon-tarsi` (refuted) by `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"anholcer-hypergraph-alon-tarsi","declaration_gid":"D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając (2026). *Alon-Tarsi for Hypergraphs*. DOI: [10.37236/15173](https://doi.org/10.37236/15173). URL: <https://arxiv.org/html/2501.00157v2>.

*Commentary.*

The joint certificate specializes each universal statement to this same witness. Its AT number is four, exceeding 2 ceil(1) + 1 = 3. The source is Anholcer et al., Alon-Tarsi for Hypergraphs, arXiv:2501.00157v2; Electronic Journal of Combinatorics 33(3), P3.74, DOI 10.37236/15173. Conjectures 4 and 28 form one related family. Characteristic-zero and simple-hypergraph variants are outside this refutation, as is Theorem 1 allowing separate coefficient permutations. Prior publication and global priority remain ASSUMED-UNVERIFIED; no priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.ATAtMost`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.Conjecture28`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.Conjecture4`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.density`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.density_one`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.edge`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.edgePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.exact_AT_bound`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.frobenius_identity`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.polynomial`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.polynomial_from_edges`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.source_counterexample`
