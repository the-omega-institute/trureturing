# Actual zero divisors and coordinate supports

## Abstract

A finite product of integral domains represents zero divisors by their nonempty proper coordinate supports. The coordinate values remain part of each vertex, so support multiplicities are exact counts of ring elements.

The three-prime support structure and four-family counting argument are due to Bilal Ahmad Rather, Combinatorial and analytic aspects of independence polynomials of zero divisor graphs, arXiv:2606.04789v1, Theorem 4.1, printed pages 18-20 (https://arxiv.org/abs/2606.04789v1, CC BY 4.0). The graph definitions are on pages 1-2. Problem 1 on page 24 asks for log concavity and unimodality; the results here supply the underlying graph and subset classification, and do not settle that problem. The Lean proofs are independently authored.

**Definition 1.1 (Actual ring vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a commutative ring R, a vertex is an element x of R with x nonzero and a witness y in R such that y is nonzero and xy is zero. The zero element is excluded.

**Definition 1.2 (The actual zero divisor graph).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph is simple and undirected. Its vertices are the actual nonzero zero divisors of R. Two vertices u and v are adjacent exactly when u differs from v and their ring product is zero.

**Definition 1.3 (Nonzero coordinate support).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.support`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let the index type be finite and let e be a ring equivalence from R to the dependent product of commutative rings K(i). The support of x consists of exactly those indices i for which the i-th coordinate of e(x) is nonzero.

**Definition 1.4 (Support of a coordinate tuple).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.coordinateSupport`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.coordinateSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a tuple in the finite dependent product, select exactly the indices where its coordinate value differs from zero. The ring support is this same finite set evaluated after the ring equivalence.

**Definition 1.5 (Coordinate vertices with both endpoints removed).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.SupportedVertex`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.SupportedVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate model consists of complete tuples x in the product of K(i) whose support is nonempty and is different from the full index set. Every tuple retains its actual coordinate values; tuples with equal supports remain distinct vertices.

**Definition 1.6 (The actual vertex correspondence).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.vertexEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.vertexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assume each K(i) is nontrivial and has no zero divisors. The equivalence e restricts to a bijection from actual ring vertices to coordinate vertices with nonempty proper supports. A missing coordinate gives an explicit annihilator: put one in that coordinate and zero elsewhere, then pull this tuple back through e. Conversely a nonzero annihilator has a nonzero coordinate, and the corresponding coordinate of x must vanish.

**Definition 1.7 (Disjoint supports give the edges).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.supportGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.supportGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the complete coordinate vertices, adjacency means that the vertices differ and their nonzero coordinate supports are disjoint. Equality of support does not identify two coordinate vertices.

**Definition 1.8 (The exact graph isomorphism).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.actualSupportIso`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.actualSupportIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate bijection preserves and reflects adjacency. In each integral domain K(i), a coordinate product is zero exactly when at least one factor is zero. Thus the product in R vanishes exactly when the two coordinate supports are disjoint. The existing independent-configuration and partition relabeling theorems apply to this graph isomorphism and retain all independent subsets.

**Theorem 1.9 (The exact size of every genuine support cell).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.prime_support_fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.prime_support_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type, every family of natural-number primes p(i) that are pairwise coprime, and every nonempty index subset S different from the full index set, consider the actual nonzero zero divisors of ZMod of the product of all p(i). The number of those vertices with CRT support exactly S equals the product over i in S of (p(i) minus one). All cardinalities and subtraction are natural numbers, and there is no upper bound on the primes or the size of the finite index type.

More generally, for a ring equivalence from a commutative ring R to a finite product of finite nontrivial commutative rings K(i) without zero divisors, the same argument gives the product over i in S of (cardinality of K(i) minus one). The prime-modulus formula uses Mathlib's native Chinese remainder equivalence and the exact cardinality of ZMod(p(i)).

The bijection restricts the coordinates of a vertex to S. Its inverse chooses an arbitrary nonzero value at each index in S and sets every remaining coordinate to zero, then applies the inverse of e. Nonemptiness excludes the zero element. Properness constructs a nonzero annihilator in a missing coordinate. These maps are mutual inverses on actual elements, so the product counts neither maximal independent sets nor equivalence classes.

**Definition 1.10 (Chinese remainder coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.crt`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.crt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite pairwise coprime family of natural moduli p(i), Mathlib's ZMod.prodEquivPi gives the ring equivalence from ZMod of their product to the product of ZMod(p(i)). For distinct prime moduli, the coordinate rings are finite fields. With the three primes p, q and r, the singleton support sizes are p-1, q-1 and r-1, and the two-coordinate support sizes are (p-1)(q-1), (p-1)(r-1) and (q-1)(r-1). The prime two is included.

**Definition 1.11 (The family using only two-coordinate supports).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.pairFamily`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.pairFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite domain V of actual ring vertices, pairFamily consists of all subsets S of V for which every vertex has support cardinality two. It includes the empty subset.

**Definition 1.12 (A family meeting a specified singleton cell).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starFamily`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an index i and a finite domain V of actual ring vertices, starFamily consists of all subsets S of V such that at least one vertex of S has support exactly the singleton containing i, and the support of every vertex of S contains i. Empty subsets are excluded from these families.

**Theorem 1.13 (Four disjoint families of actual independent sets).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.configurations_four_families`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.configurations_four_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the finite index type has cardinality exactly three, R is a commutative ring, each K(i) is a nontrivial commutative ring without zero divisors, and e is a ring equivalence from R to the product of the K(i). For every finite subset V of the actual nonzero zero divisors of R, the canonical independent configurations of the actual ring graph on V equal pairFamily together with the union of starFamily(i) over all three indices. pairFamily is disjoint from every starFamily(i), and starFamily(i) and starFamily(j) are disjoint whenever i and j differ.

An actual vertex has nonempty proper support, so with three coordinates its support has size one or two. If an independent subset contains a singleton support at i, independence forces every other support to contain i. If no singleton support occurs, all supports have size two; any two such subsets of a three-element set intersect, so the corresponding vertices are independent. A singleton support in a star family identifies its index uniquely and precludes membership in the family of two-coordinate supports.

The identity uses the existing powerset-filter definition of independent configurations, so it partitions all independent subsets, including the empty set. It makes no assertion about maximality or domination, and the finite domain V may be the entire actual vertex set.

**Definition 1.14 (The actual two-coordinate vertex domain).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.pairDomain`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.pairDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite domain V of actual ring vertices, pairDomain is its subset of vertices whose support has cardinality two.

**Definition 1.15 (The actual domain containing a coordinate).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starDomain`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a coordinate i, starDomain is the subset of V whose supports contain i.

**Definition 1.16 (Removing the singleton cell).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starTailDomain`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starTailDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

starTailDomain removes from starDomain(i) precisely the vertices whose support equals the singleton containing i.

**Theorem 1.17 (The exact native family generating function).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independencePolynomial_four_families`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independencePolynomial_four_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type of cardinality three, commutative ring R, nontrivial commutative coordinate rings K(i) without zero divisors, ring equivalence e from R to their product, and finite domain V of actual vertices, the native independence polynomial equals (1+X) to the cardinality of pairDomain, plus the sum over i of the difference between (1+X) to the cardinality of starDomain(i) and (1+X) to the cardinality of starTailDomain(i). The equality is in Polynomial over the integers, so subtraction is integer polynomial subtraction.

The pair family is the full powerset of pairDomain. The star family is the powerset of starDomain with the powerset of starTailDomain removed. The proved disjoint configuration decomposition therefore evaluates using Mathlib's powerset product expansion. The empty configuration occurs once, in the pair family. This is the polynomial defined by the native independent-set sum, without an assumed counting formula.

**Theorem 1.18 (Every native coefficient is an independent-subset count).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.coefficient_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.coefficient_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring R, finite set V of its actual zero divisor vertices, and natural rank k, the integer coefficient at k of the native independence polynomial equals the cardinality of the independent configurations on V having exactly k vertices, cast to the integers. No product decomposition or coordinate assumptions are needed.

**Theorem 1.19 (Coefficients count all actual independent subsets).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independent_count_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independent_count_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same full hypotheses and for every natural k, the integer cast of the number of native configurations S contained in V with cardinality k is choose(card(pairDomain),k), plus the sum over the three coordinates i of choose(card(starDomain(i)),k) minus choose(card(starTailDomain(i)),k). The differences and sum are taken in the integers, not with truncated natural subtraction.

Each configuration contributes exactly X to the power of its cardinality in the native polynomial. Extracting coefficient k is therefore the cardinality of the filter by cardinality k. Mathlib's coefficient formula for (1+X) to a natural power then gives the displayed binomial expression, including k=0 and ranks above every family size.

**Theorem 1.20 (All six multiplicities in the full ring graph).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independencePolynomial_three_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independencePolynomial_three_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L(0), L(1), L(2) be arbitrary finite nontrivial commutative rings without zero divisors, let R be a finite commutative ring, and specify a ring equivalence from R to their product. Set a=card(L(0))-1, b=card(L(1))-1, c=card(L(2))-1 and y=1+X. On the entire actual vertex domain, the native polynomial is y^(ab+ac+bc) + (y^(a+ab+ac)-y^(ab+ac)) + (y^(b+ab+bc)-y^(ab+bc)) + (y^(c+ac+bc)-y^(ac+bc)).

The proof partitions each actual vertex domain by its nonempty proper support and uses the inverse coordinate-choice bijection to evaluate its fibers. The six supports on three coordinates give pair-domain size ab+ac+bc, and coordinate-i star sizes a+ab+ac, b+ab+bc, c+ac+bc with the corresponding singleton cells removed for the tail domains. This evaluates Rather's Theorem 4.1 formula on actual ring elements. For distinct primes p,q,r the native CRT gives a=p-1, b=q-1, c=r-1, including p=2; no prime upper bound is introduced.

The exact native polynomial and coefficient counts do not establish log concavity or unimodality. Identifying and attaining the actual independence number, proving positivity through that maximum and the zero tail, and proving uniform coefficient inequalities require further arguments.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.SupportedVertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.actualSupportIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.coefficient_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.configurations_four_families`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.coordinateSupport`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.crt`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independencePolynomial_four_families`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independencePolynomial_three_coordinates`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.independent_count_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.pairDomain`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.pairFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.prime_support_fiber_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starDomain`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.starTailDomain`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.support`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.supportGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/Support.vertexEquiv`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling](../../../StatisticalMechanics/HardCore/PartitionRelabeling.md)
