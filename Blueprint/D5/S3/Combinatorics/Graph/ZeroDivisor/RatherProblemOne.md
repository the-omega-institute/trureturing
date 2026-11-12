# Rather's three-prime graph

## Abstract

Actual zero-divisor supports, uniform binomial bounds and the complete native three-prime independence-polynomial result.

In every displayed formula, a map marked by the equivalence symbol between rings is a ring equivalence, preserving addition, multiplication, zero and one. All finite cardinalities, ranks and subtraction in binomial indices are natural numbers. B(n,k) denotes the natural binomial coefficient, zero for k greater than n. Every occurrence of H and every quotient in the binomial-curvature formulas is interpreted in the rationals: H(N,m,k)=B(m,k-1) B(N-m,2)/(B(N,k+1) B(k+1,2)). C(G,V) denotes the native finite family of all independent subsets of V, and P(G,V) its integer independence polynomial. The functions int and rat are the canonical casts. Iic and Ici are intervals in all natural indices, so weak monotonicity includes ties and the zero tail.

The three-prime support structure and four-family counting argument are due to Bilal Ahmad Rather, Combinatorial and analytic aspects of independence polynomials of zero divisor graphs, arXiv:2606.04789v1, Theorem 4.1, printed pages 18-20 (https://arxiv.org/abs/2606.04789v1, CC BY 4.0). The graph definitions are on pages 1-2. Problem 1 on page 24 asks for log concavity and unimodality; the underlying graph and subset classification enter the coefficient proof below. The Lean proofs are independently authored.

**Definition 1.1 (Actual ring vertices).**

$$\forall R : \operatorname{Type}, \operatorname{CommRing}(R) \to \operatorname{Vertex}(R) = \{x \in R : x \neq 0 \land \exists y \in R, y \neq 0 \land x\cdot y = 0\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a commutative ring R, a vertex is an element x of R with x nonzero and a witness y in R such that y is nonzero and xy is zero. The zero element is excluded.

**Definition 1.2 (The actual zero divisor graph).**

$$\forall R : \operatorname{Type}, \operatorname{CommRing}(R) \to \forall u v : \operatorname{Vertex}(R), \operatorname{Adj}(\operatorname{graph}(R),u,v) \iff (u \neq v \land \operatorname{val}(u)\cdot \operatorname{val}(v) = 0)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph is simple and undirected. Its vertices are the actual nonzero zero divisors of R. Two vertices u and v are adjacent exactly when u differs from v and their ring product is zero.

**Definition 1.3 (Nonzero coordinate support).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i))) \to \forall (e : R \equiv \prod i : I, K(i)) (x : R), \operatorname{support}(e,x) = \operatorname{coordinateSupport}(e(x))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let the index type be finite and let e be a ring equivalence from R to the dependent product of commutative rings K(i). The support of x consists of exactly those indices i for which the i-th coordinate of e(x) is nonzero. For nontrivial coordinate domains, the actual vertices have precisely nonempty proper supports: a missing coordinate supplies a nonzero annihilator. For a genuine support S, restriction to S is a bijection with independent nonzero coordinate choices; the inverse fills every other coordinate with zero and applies the inverse ring equivalence. Over finite coordinate domains the fiber therefore has cardinality the product over i in S of (card(K(i))-1). This live fiber count evaluates the full vertex domains below.

**Definition 1.4 (Support of a coordinate tuple).**

$$\forall (I : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land (\forall i : I, \operatorname{CommRing}(K(i))) \to \forall x : \prod i : I, K(i), \operatorname{coordinateSupport}(x) = \{i \in I : x(i) \neq 0\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.coordinateSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a tuple in the finite dependent product, select exactly the indices where its coordinate value differs from zero. The ring support is this same finite set evaluated after the ring equivalence.

**Definition 1.5 (Chinese remainder coordinates).**

$$\forall (I : \operatorname{Type}) (p : I \to \mathbb{N}), \operatorname{Fintype}(I) \to \forall h : \operatorname{PairwiseCoprime}(p), \operatorname{crt}(p,h) : \operatorname{ZMod}(\prod i \in I,p(i)) \equiv \prod i \in I,\operatorname{ZMod}(p(i))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.crt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite pairwise coprime family of natural moduli p(i), Mathlib's ZMod.prodEquivPi gives the ring equivalence from ZMod of their product to the product of ZMod(p(i)). For distinct prime moduli, the coordinate rings are finite fields. With the three primes p, q and r, the singleton support sizes are p-1, q-1 and r-1, and the two-coordinate support sizes are (p-1)(q-1), (p-1)(r-1) and (q-1)(r-1). The prime two is included.

**Definition 1.6 (The family using only two-coordinate supports).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i))) \to \forall (e : R \equiv \prod i : I,K(i)) (V : \operatorname{Finset}(\operatorname{Vertex}(R))), \operatorname{pairFamily}(e,V) = \{S \subseteq V : \forall x \in S, \operatorname{card}(\operatorname{support}(e,\operatorname{val}(x))) = 2\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.pairFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite domain V of actual ring vertices, pairFamily consists of all subsets S of V for which every vertex has support cardinality two. It includes the empty subset.

**Definition 1.7 (A family meeting a specified singleton cell).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i))) \to \forall (e : R \equiv \prod i : I,K(i)) (V : \operatorname{Finset}(\operatorname{Vertex}(R))) (i : I), \operatorname{starFamily}(e,V,i) = \{S \subseteq V : (\exists x \in S, \operatorname{support}(e,\operatorname{val}(x)) = \{i\}) \land \forall x \in S, i \in \operatorname{support}(e,\operatorname{val}(x))\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.starFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an index i and a finite domain V of actual ring vertices, starFamily consists of all subsets S of V such that at least one vertex of S has support exactly the singleton containing i, and the support of every vertex of S contains i. Empty subsets are excluded from these families.

**Theorem 1.8 (Four disjoint families of actual independent sets).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i)) \land \operatorname{NoZeroDivisors}(K(i)) \land \operatorname{Nontrivial}(K(i))) \to \operatorname{card}(I) = 3 \to \forall (e : R \equiv \prod i : I,K(i)) (V : \operatorname{Finset}(\operatorname{Vertex}(R))), (C(\operatorname{graph}(R),V) = \operatorname{pairFamily}(e,V) \cup \cup i \in I,\operatorname{starFamily}(e,V,i)) \land (\forall i \in I, \operatorname{Disjoint}(\operatorname{pairFamily}(e,V),\operatorname{starFamily}(e,V,i))) \land (\forall i j \in I, i \neq j \to \operatorname{Disjoint}(\operatorname{starFamily}(e,V,i),\operatorname{starFamily}(e,V,j)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.configurations_four_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the finite index type has cardinality exactly three, R is a commutative ring, each K(i) is a nontrivial commutative ring without zero divisors, and e is a ring equivalence from R to the product of the K(i). For every finite subset V of the actual nonzero zero divisors of R, the canonical independent configurations of the actual ring graph on V equal pairFamily together with the union of starFamily(i) over all three indices. pairFamily is disjoint from every starFamily(i), and starFamily(i) and starFamily(j) are disjoint whenever i and j differ.

An actual vertex has nonempty proper support, so with three coordinates its support has size one or two. If an independent subset contains a singleton support at i, independence forces every other support to contain i. If no singleton support occurs, all supports have size two; any two such subsets of a three-element set intersect, so the corresponding vertices are independent. A singleton support in a star family identifies its index uniquely and precludes membership in the family of two-coordinate supports.

The identity uses the existing powerset-filter definition of independent configurations, so it partitions all independent subsets, including the empty set. It makes no assertion about maximality or domination, and the finite domain V may be the entire actual vertex set.

**Definition 1.9 (The actual two-coordinate vertex domain).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i))) \to \forall (e : R \equiv \prod i : I,K(i)) (V : \operatorname{Finset}(\operatorname{Vertex}(R))), \operatorname{pairDomain}(e,V) = \{x \in V : \operatorname{card}(\operatorname{support}(e,\operatorname{val}(x))) = 2\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.pairDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite domain V of actual ring vertices, pairDomain is its subset of vertices whose support has cardinality two.

**Definition 1.10 (The actual domain containing a coordinate).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i))) \to \forall (e : R \equiv \prod i : I,K(i)) (V : \operatorname{Finset}(\operatorname{Vertex}(R))) (i : I), \operatorname{starDomain}(e,V,i) = \{x \in V : i \in \operatorname{support}(e,\operatorname{val}(x))\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.starDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a coordinate i, starDomain is the subset of V whose supports contain i.

**Definition 1.11 (Removing the singleton cell).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i))) \to \forall (e : R \equiv \prod i : I,K(i)) (V : \operatorname{Finset}(\operatorname{Vertex}(R))) (i : I), \operatorname{starTailDomain}(e,V,i) = \{x \in \operatorname{starDomain}(e,V,i) : \operatorname{support}(e,\operatorname{val}(x)) \neq \{i\}\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.starTailDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

starTailDomain removes from starDomain(i) precisely the vertices whose support equals the singleton containing i.

**Theorem 1.12 (The exact native family generating function).**

$$\forall (I : \operatorname{Type}) (R : \operatorname{Type}) (K : I \to \operatorname{Type}), \operatorname{Fintype}(I) \land \operatorname{CommRing}(R) \land (\forall i : I, \operatorname{CommRing}(K(i)) \land \operatorname{NoZeroDivisors}(K(i)) \land \operatorname{Nontrivial}(K(i))) \to \operatorname{card}(I) = 3 \to \forall (e : R \equiv \prod i : I,K(i)) (V : \operatorname{Finset}(\operatorname{Vertex}(R))), P(\operatorname{graph}(R),V) = (1+X)^{\operatorname{card}(\operatorname{pairDomain}(e,V))} + \sum i \in I,((1+X)^{\operatorname{card}(\operatorname{starDomain}(e,V,i))} - (1+X)^{\operatorname{card}(\operatorname{starTailDomain}(e,V,i))})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.independencePolynomial_four_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type of cardinality three, commutative ring R, nontrivial commutative coordinate rings K(i) without zero divisors, ring equivalence e from R to their product, and finite domain V of actual vertices, the native independence polynomial equals (1+X) to the cardinality of pairDomain, plus the sum over i of the difference between (1+X) to the cardinality of starDomain(i) and (1+X) to the cardinality of starTailDomain(i). The equality is in Polynomial over the integers, so subtraction is integer polynomial subtraction.

The pair family is the full powerset of pairDomain. The star family is the powerset of starDomain with the powerset of starTailDomain removed. The proved disjoint configuration decomposition therefore evaluates using Mathlib's powerset product expansion. The empty configuration occurs once, in the pair family. This is the polynomial defined by the native independent-set sum, without an assumed counting formula.

**Theorem 1.13 (Every native coefficient is an independent-subset count).**

$$\forall R : \operatorname{Type}, \operatorname{CommRing}(R) \to \forall (V : \operatorname{Finset}(\operatorname{Vertex}(R))) (k : \mathbb{N}), \operatorname{coeff}(P(\operatorname{graph}(R),V),k) = \operatorname{int}(\operatorname{card}(\{S \in C(\operatorname{graph}(R),V) : \operatorname{card}(S) = k\}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.coefficient_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring R, finite set V of its actual zero divisor vertices, and natural rank k, the integer coefficient at k of the native independence polynomial equals the cardinality of the independent configurations on V having exactly k vertices, cast to the integers. No product decomposition or coordinate assumptions are needed.

**Theorem 1.14 (All six multiplicities in the full ring graph).**

$$\forall (R : \operatorname{Type}) (L : \operatorname{Fin}(3) \to \operatorname{Type}), \operatorname{CommRing}(R) \land \operatorname{Fintype}(R) \land (\forall i : \operatorname{Fin}(3), \operatorname{CommRing}(L(i)) \land \operatorname{NoZeroDivisors}(L(i)) \land \operatorname{Nontrivial}(L(i)) \land \operatorname{Fintype}(L(i))) \to \forall e : R \equiv \prod i : \operatorname{Fin}(3),L(i), a=\operatorname{card}(L(0))-1; b=\operatorname{card}(L(1))-1; c=\operatorname{card}(L(2))-1; y=1+X; P(\operatorname{graph}(R),\operatorname{univ}) = y^{a\cdot b+a\cdot c+b\cdot c} + (y^{a+a\cdot b+a\cdot c}-y^{a\cdot b+a\cdot c}) + (y^{b+a\cdot b+b\cdot c}-y^{a\cdot b+b\cdot c}) + (y^{c+a\cdot c+b\cdot c}-y^{a\cdot c+b\cdot c})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.independencePolynomial_three_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L(0), L(1), L(2) be arbitrary finite nontrivial commutative rings without zero divisors, let R be a finite commutative ring, and specify a ring equivalence from R to their product. Set a=card(L(0))-1, b=card(L(1))-1, c=card(L(2))-1 and y=1+X. On the entire actual vertex domain, the native polynomial is y^(ab+ac+bc) + (y^(a+ab+ac)-y^(ab+ac)) + (y^(b+ab+bc)-y^(ab+bc)) + (y^(c+ac+bc)-y^(ac+bc)).

The proof partitions each actual vertex domain by its nonempty proper support and uses the inverse coordinate-choice bijection to evaluate its fibers. The six supports on three coordinates give pair-domain size ab+ac+bc, and coordinate-i star sizes a+ab+ac, b+ab+bc, c+ac+bc with the corresponding singleton cells removed for the tail domains. This evaluates Rather's Theorem 4.1 formula on actual ring elements. For distinct primes p,q,r the native CRT gives a=p-1, b=q-1, c=r-1, including p=2; no prime upper bound is introduced.

The support identity is used with the uniform coefficient inequalities below. Positivity and the zero tail identify and attain the actual independence number.

**Theorem 1.15 (Counting extensions of a selected prefix and pair).**

$$\forall m n k : \mathbb{N}, (3 \leq k \land k \leq 5) \to \sum j \in \operatorname{range}(10), B(m,j)\cdot B(n,9-j)\cdot B(j,k-1)\cdot B(9-j,2) = B(m,k-1)\cdot B(n,2)\cdot B(m+n-(k+1),9-(k+1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.nine_restriction_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural block sizes m and n and rank k between three and five, sum over j from zero through nine the product choose(m,j) choose(n,9-j) choose(j,k-1) choose(9-j,2). This equals choose(m,k-1) choose(n,2) choose(m+n-(k+1),9-(k+1)). All subtractions here are natural subtractions, and binomial coefficients vanish outside their natural support.

Only k-1 through seven can contribute. Shifting by k-1 and applying the composed-choice identity in each block leaves Vandermonde convolution on the remaining elements. If either block cannot supply its selected elements, both sides vanish. This counts extensions in arbitrary populations, rather than only a population of size nine.

**Theorem 1.16 (The exact restriction average).**

$$\forall N m k : \mathbb{N}, (9 \leq N \land m \leq N \land 3 \leq k \land k \leq 5) \to H(N,m,k) = \sum j \in \operatorname{range}(10), (B(m,j)\cdot B(N-m,9-j)/B(N,9))\cdot H(9,j,k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.nine_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N at least nine, m at most N and k from three through five, define H(N,m,k) as choose(m,k-1) choose(N-m,2) divided by choose(N,k+1) choose(k+1,2), with rational division. Then H(N,m,k) equals the sum over zero through nine of w(j) H(9,j,k), where w(j) is choose(m,j) choose(N-m,9-j) divided by choose(N,9).

Every denominator is positive: k+1 lies between four and six and is at most nine and N. The integer extension count and the composed-choice identity cancel the number of extensions of a selected (k+1)-subset to a nine-subset.

**Theorem 1.17 (Uniform small-rank bounds).**

$$\forall N m k : \mathbb{N}, (9 \leq N \land m \leq N \land 3 \leq k \land k \leq 5) \to H(N,m,k) \leq (\operatorname{if} k=3 \operatorname{then} 5/63 \operatorname{else} \operatorname{if} k=4 \operatorname{then} 1/21 \operatorname{else} 1/28)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.nine_restriction_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N at least nine and m at most N, the rational quantity H(N,m,k) is at most 5/63 for k=3, at most 1/21 for k=4, and at most 1/28 for k=5. The theorem states these three values as one rank-indexed bound.

The weights are nonnegative, and Vandermonde convolution shows that they sum to one. For j from zero through nine the numerators choose(j,k-1) choose(9-j,2) have respective maxima 60, 60 and 45. Their denominators are 756, 1260 and 1260. Applying these finite bounds inside the exact restriction average proves the stated bounds for all N. Three such nonnegative contributions are consequently bounded by 5/21, 1/7 and 3/28, respectively.

**Theorem 1.18 (Exact second difference).**

$$\forall N m k : \mathbb{N}, (m \leq N \land 1 \leq k \land k < N) \to B(m,k-1)/B(N,k-1) - 2\cdot B(m,k)/B(N,k) + B(m,k+1)/B(N,k+1) = H(N,m,k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.normalized_second_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N, m and k be natural numbers with m at most N and 1 at most k less than N. Write h(j)=choose(m,j)/choose(N,j), using rational division. Then h(k-1)-2h(k)+h(k+1) equals H(N,m,k)=choose(m,k-1) choose(N-m,2) divided by choose(N,k+1) choose(k+1,2). All binomial coefficients and their indices use natural numbers, so a coefficient with its lower index above its upper index is zero.

The adjacent-coefficient recurrence, interpreted over the rationals, remains valid even beyond the natural support because both coefficients vanish. Apply it twice in each row and use choose(a,2)=a(a-1)/2 over the rationals. The resulting numerator factors as choose(m,k-1)(N-m)(N-m-1). The denominators are positive on the stated interval. This includes k=N-1, m below k-1, m=N and N-m below two.

**Theorem 1.19 (Uniform bound at every rank from three onward).**

$$\forall N m k : \mathbb{N}, (9 \leq N \land m \leq N \land 3 \leq k \land k < N) \to B(m,k-1)/B(N,k-1) - 2\cdot B(m,k)/B(N,k) + B(m,k+1)/B(N,k+1) \leq 1/(3\cdot (k+1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.normalized_second_difference_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N at least nine, m at most N and rank k with 3 at most k less than N, the same rational second difference is at most 1/(3(k+1)). There is no upper bound on N or k.

For k at least six, choose(m,k-1) choose(N-m,2) is one nonnegative term of the Vandermonde sum for choose(N,k+1). Thus H is at most 1/choose(k+1,2), which is at most 1/(3(k+1)). For k=3,4,5 the nine-element restriction bounds give respectively 5/63, 1/21 and 1/28; these are at most 1/12, 1/15 and 1/18. The restriction theorem holds for every N at least nine, so the small-rank argument retains the full population range.

**Theorem 1.20 (Exact support and strict interior log concavity).**

$$\forall (R : \operatorname{Type}) (L : \operatorname{Fin}(3) \to \operatorname{Type}), \operatorname{CommRing}(R) \land \operatorname{Fintype}(R) \land (\forall i : \operatorname{Fin}(3), \operatorname{CommRing}(L(i)) \land \operatorname{NoZeroDivisors}(L(i)) \land \operatorname{Nontrivial}(L(i)) \land \operatorname{Fintype}(L(i))) \to \forall e : R \equiv \prod i : \operatorname{Fin}(3),L(i), (\operatorname{card}(L(0)) \leq \operatorname{card}(L(1)) \land \operatorname{card}(L(1)) \leq \operatorname{card}(L(2)) \land 3 \leq \operatorname{card}(L(1)) \land 5 \leq \operatorname{card}(L(2))) \to a=\operatorname{card}(L(0))-1; b=\operatorname{card}(L(1))-1; c=\operatorname{card}(L(2))-1; N=\operatorname{max}(a\cdot b+a\cdot c+b\cdot c,c+a\cdot c+b\cdot c); s(k)=\operatorname{rat}(\operatorname{coeff}(P(\operatorname{graph}(R),\operatorname{univ}),k)); 14 \leq N \land (\forall k : \mathbb{N},k \leq N \to 0 < s(k)) \land (\forall k : \mathbb{N},N < k \to s(k)=0) \land (\forall k : \mathbb{N},1 \leq k \land k < N \to s(k-1)\cdot s(k+1) < s(k)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.coefficients_three_domains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a finite commutative ring, let L be three finite nontrivial commutative rings without zero divisors, and let e identify R with their dependent product. Their cardinalities are nondecreasing, with the second at least three and the third at least five. Put a=card(L(0))-1, b=card(L(1))-1, c=card(L(2))-1, A=ab+ac+bc and N=max(A,c+ac+bc). For every natural k, let s(k) be the coefficient of the native independence polynomial of the actual zero divisor graph on its full vertex set, cast from the integers to the rationals. Then N is at least fourteen, s(k) is strictly positive for k at most N, s(k) vanishes for k greater than N, and s(k-1)s(k+1) is strictly smaller than s(k) squared whenever 1 is at most k less than N. There is no bound on the coordinate cardinalities or on k.

The seven-term formula is derived from the existing actual-vertex support correspondence. A maximal positive exponent equals N. Monotonicity of binomial coefficients makes the coefficient at every rank at most N at least choose(N,k), including when the singleton family exceeds A. The normalized coefficient s(k)/choose(N,k) is therefore at least one.

At ranks at least three, apply the exact normalized second difference to each subtracted term and the uniform curvature bound to the other three positive terms after removing a term with exponent N. The normalized curvature is at most 1/(k+1). Positivity pays for this error: the square of f(k), multiplied by k+1, is greater than k f(k-1)f(k+1). The adjacent binomial recurrence transfers this to strict log concavity of the actual coefficients.

At the first two ranks, v=A+a+b+c and E=A+3abc give s(0)=1, s(1)=v and s(2)=v(v-1)/2-E. The coefficient-count identity identifies v with the actual vertex count and bounds s(3) by choose(v,3). For integral a at least one, b at least two and c at least four, an expansion in a-1, b-2 and c-4 proves 11E at most v(v-1), hence s(2) at least nine elevenths of choose(v,2). Its square exceeds v choose(v,3), proving the second rank. The finite-ring and graph definitions are those of Rather's arXiv:2606.04789v1, Theorem 4.1 and Problem 1; this coefficient argument is a repository derivation.

**Theorem 1.21 (All primes, attained independence number and weak unimodality).**

$$\forall p q r : \mathbb{N}, (\operatorname{Prime}(p) \land \operatorname{Prime}(q) \land \operatorname{Prime}(r) \land p < q \land q < r) \to a=p-1; b=q-1; c=r-1; N=\operatorname{max}(a\cdot b+a\cdot c+b\cdot c,c+a\cdot c+b\cdot c); G=\operatorname{graph}(\operatorname{ZMod}(p\cdot q\cdot r)); s(k)=\operatorname{coeff}(P(G,\operatorname{univ}),k); 14 \leq N \land \operatorname{indepNum}(G)=N \land (\exists S : \operatorname{Finset}(\operatorname{Vertex}(\operatorname{ZMod}(p\cdot q\cdot r))), \operatorname{IsIndepSet}(G,S) \land \operatorname{card}(S)=N) \land (\forall k : \mathbb{N},k \leq N \to 0 < s(k)) \land (\forall k : \mathbb{N},N < k \to s(k)=0) \land (\forall k : \mathbb{N},1 \leq k \to s(k-1)\cdot s(k+1) \leq s(k)^{2}) \land (\exists m : \mathbb{N},m \leq N \land \operatorname{MonotoneOn}(s,\operatorname{Iic}(m)) \land \operatorname{AntitoneOn}(s,\operatorname{Ici}(m)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.rather_problem_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bilal Ahmad Rather (2026). *Combinatorial and analytic aspects of independence polynomials of zero divisor graphs*. DOI: [10.48550/arXiv.2606.04789](https://doi.org/10.48550/arXiv.2606.04789). URL: <https://arxiv.org/abs/2606.04789v1>.

*Commentary.*

For every three natural-number primes p<q<r, including p=2, let G be the actual zero divisor graph of ZMod(p*q*r). Its vertices are nonzero elements with a nonzero annihilator, and two distinct vertices are adjacent precisely when their product is zero. Let s(k) be the integer coefficient at natural rank k of the native independence polynomial on the full actual vertex set. Set a=p-1, b=q-1, c=r-1 and N=max(ab+ac+bc,c+ac+bc). Then N is at least fourteen and equals the graph's independence number. There exists an actual independent finite vertex set of cardinality N. Every coefficient through N is strictly positive and every coefficient after N is zero. For every k at least one, s(k-1)s(k+1) is at most s(k) squared. There is a peak m at most N such that s is weakly increasing on all natural indices at most m and weakly decreasing on all natural indices at least m, including the zero tail.

Distinct primes give Mathlib's native Chinese remainder equivalence. Its three finite fields satisfy the ordered-cardinality hypotheses of the general native coefficient theorem. Coefficient positivity at N supplies a nonempty family of actual independent N-subsets. Conversely, an independent set above N would give a positive coefficient in the zero tail. A maximum independent set therefore has cardinality exactly N.

Cast the positive coefficients to the reals and choose a maximum on the finite interval from zero through N. The existing strict log-concavity peak lemmas give strict adjacent steps away from the two immediate boundaries of this selected peak; maximality gives the weak inequalities at those boundaries. Chaining adjacent steps gives weak monotonicity on each side. At every log-concavity center at least N, the right neighboring coefficient vanishes, so the endpoint and the whole zero tail satisfy the same inequality.

The statement is Problem 1 of arXiv:2606.04789v1 on printed page 24. The native support formula is Theorem 4.1 on printed pages 18–20. This consumer and its coefficient argument are repository derivations; no assumed coefficient formula, finite prime bound or exclusion of the prime two is used.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.coefficient_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.coefficients_three_domains`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.configurations_four_families`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.coordinateSupport`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.crt`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.independencePolynomial_four_families`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.independencePolynomial_three_coordinates`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.nine_restriction`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.nine_restriction_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.nine_restriction_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.normalized_second_difference`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.normalized_second_difference_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.pairDomain`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.pairFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.rather_problem_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.starDomain`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.starFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.starTailDomain`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.support`
- Dependency: [D5/S3/Combinatorics/RealRootedPermutations/LogConcave](../../RealRootedPermutations/LogConcave.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](../../../StatisticalMechanics/HardCore/IndependentPartitionDeletion.md)
