# Secondary Boundary Betti Degrees

## Abstract

Critical pairs control the full factorization graphs at the secondary boundary degrees.

The definitions follow Kazimierz Chomicz, The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four, arXiv:2609.04000v1, Sections 2 and 3. The question after Lemma 3.13 asks whether both b_22*d_2 and b_33*d_3 are Betti elements. The arithmetic argument is reused, with attribution to producer 07b67e50-10a4-41b3-9622-660f37c654a5 and its research contributor; no new discovery is attributed here.

The printed chain definition at main.tex:469 places intermediates in ambient N^4. Here chains remain in the fixed factorization fiber. Unrestricted ambient chains connect any two nonzero vectors through their sum and therefore cannot describe the intended classes. The source immediately discusses classes of a fixed fiber, invokes the minimal-presentation theorem at lines 476-480, constructs fixed-degree chains in Lemma 3.13, and calls positive critical degrees Betti at line 1050. These uses justify the explicit fiber-local interpretation; they do not establish equivalence with the unrestricted printed relation.

The statement retains positivity, minimal generation, gcd one, all four exact critical fibers, and every choice of least data and relation witnesses. It imposes no generator, degree, or fiber bound. The gcd criterion and complete component alternatives strengthen the two literal boundary questions.

In the formulas, I = Fin 4, N denotes the natural numbers, Generators = Factorization = CriticalCoefficients = (I -> N), and PositiveCriticalCoefficients = (I -> I -> N). Free variables in definitions have these types: d is a generator tuple, a is critical data, b is positive critical data, z and w are factorization vectors, indices lie in I, and n, k, A, B are natural numbers. Graph vertices and the arguments of RRelated belong to the fixed fiber Factorizations(d,n); their underlying vectors are used in coordinate expressions. Definition formulas are universally quantified over these free variables. closure means additive submonoid closure; range and image have their set meanings; coordinate(v,j) means v(j). ConnectedComponent, supp, Reachable and Connected refer to the displayed simple graph. Division is natural-number division. Threshold(d,x,y,c) abbreviates gcd(d(x),d(y))/gcd(gcd(d(x),d(y)),d(c)); it imposes no representation hypothesis.

Source provenance is literature-attested for the translated source definitions and the literal critical-pair ordering in main.tex:230, derived there from Lemma 2.2. The graph encoding, source-domain packaging, stronger classification and its proof are repository formalization/reuse of the attributed public argument, not theorems asserted by the paper. The source note is Library/Semigroups/chomicz2026minimalpresentations.md; the full question, clause map and result boundaries are in Problems/chomicz-2026-secondary-boundary-betti.md. No exhaustive literature or priority certification is claimed.

The compiled Reg mirror supplies additive-closure, excluded-generator, set-gcd, cofiniteness, distinctness and fixed-fiber-chain bridges. Its source_domain_nonempty theorem uses d=(145,203,74,111), a=(7,5,3,2), with complete critical fibers at 1015 and 222 and existing least-data existence. This witnesses the original domain, not a universal permutation-transport theorem. All five public four-slot audits remain unfinished, with zero declared_validated; issue https://github.com/the-omega-institute/trureturing/issues/29825 names the missing variation, sensitivity, dependence, source-selection and lawful-enrollment evidence. The conditional compiled Reg mirrors do not discharge those audits.

**Definition 1.1 (The generated additive submonoid).**

$$\operatorname{semigroup}\left(d\right) = \operatorname{closure}\left(\operatorname{range}\left(d\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.semigroup` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

Finite nonnegative combinations of the four displayed generators.

**Definition 1.2 (The factorization morphism).**

$$\operatorname{eval}\left(d, z\right) = \sum_{i \in I} z\left(i\right) \cdot d\left(i\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.eval` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

The source map from four nonnegative coordinates to their weighted sum.

**Definition 1.3 (The full factorization fiber).**

$$\operatorname{factorizations}\left(d, n\right) = \{z \in Factorization \mid \operatorname{eval}\left(d, z\right) = n\}$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.factorizations` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

Every vector with the displayed degree is included.

**Definition 1.4 (Support).**

$$\operatorname{support}\left(z\right) = \{i \in I \mid 0 < z\left(i\right)\}$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.support` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

A coordinate belongs to the support exactly when it is positive.

**Definition 1.5 (The fiber graph).**

$$\forall z \in \operatorname{Factorizations}\left(d, n\right), w \in \operatorname{Factorizations}\left(d, n\right),\; \operatorname{Adj}\left(\operatorname{factorizationGraph}\left(d, n\right), z, w\right) \Leftrightarrow \left(z \ne w \land \left(\exists i \in I,\; 0 < z\left(i\right) \land 0 < w\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.factorizationGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertices are factorizations in one fixed fiber. Distinct vertices are adjacent when their supports intersect.

**Definition 1.6 (Fiber-local support chains).**

$$\operatorname{RRelated}\left(d, n, z, w\right) \Leftrightarrow \operatorname{Reachable}\left(\operatorname{factorizationGraph}\left(d, n\right), z, w\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.RRelated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reachability includes chains of length zero and permits removal of consecutive repeated vertices.

**Definition 1.7 (Betti elements).**

$$n \in \operatorname{Betti}\left(d\right) \Leftrightarrow \left(n \in \operatorname{semigroup}\left(d\right) \land \left(\exists z \in \operatorname{Factorizations}\left(d, n\right), w \in \operatorname{Factorizations}\left(d, n\right),\; \neg \operatorname{RRelated}\left(d, n, z, w\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.Betti` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A degree is in the generated semigroup and has two vertices not joined by a fiber-local support chain.

**Definition 1.8 (The source domain).**

$$\operatorname{IsNumericalGeneratingTuple}\left(d\right) \Leftrightarrow \left(\left(\left(\forall j \in I,\; 0 < d\left(j\right)\right) \land \operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), \operatorname{gcd}\left(d\left(2\right), d\left(3\right)\right)\right) = 1\right) \land \left(\forall i \in I,\; \neg d\left(i\right) \in \operatorname{closure}\left(\operatorname{image}\left(d, \{j \in I \mid j \ne i\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsNumericalGeneratingTuple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generators are positive, their nested gcd is one, and each generator is excluded from the submonoid generated by the other three.

**Definition 1.9 (Least critical coefficient).**

$$\operatorname{IsCriticalCoefficient}\left(d, i, k\right) \Leftrightarrow \operatorname{IsLeast}\left(\{n \in \mathbb{N} \mid 0 < n \land \left(\exists z \in Factorization,\; z\left(i\right) = 0 \land \operatorname{eval}\left(d, z\right) = n \cdot d\left(i\right)\right)\}, k\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsCriticalCoefficient` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

The least positive coefficient admits an i-free relation. The other three coordinates retain every allowed relation choice.

**Definition 1.10 (All critical coefficients).**

$$\operatorname{IsCriticalData}\left(d, a\right) \Leftrightarrow \left(\forall i \in I,\; \operatorname{IsCriticalCoefficient}\left(d, i, a\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsCriticalData` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

There is one least coefficient for each of the four indices.

**Definition 1.11 (Least positive critical coefficient).**

$$\operatorname{IsPositiveCriticalCoefficient}\left(d, m, i, k\right) \Leftrightarrow \operatorname{IsLeast}\left(\{n \in \mathbb{N} \mid 0 < n \land \left(\exists z \in Factorization,\; \left(z\left(i\right) = 0 \land 0 < z\left(m\right)\right) \land \operatorname{eval}\left(d, z\right) = n \cdot d\left(i\right)\right)\}, k\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPositiveCriticalCoefficient` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

The relation is i-free and has a positive coordinate at m. The indices m and i are distinct in source use.

**Definition 1.12 (All positive critical coefficients).**

$$\operatorname{IsPositiveCriticalData}\left(d, b\right) \Leftrightarrow \left(\left(\forall m \in I,\; b\left(m, m\right) = 0\right) \land \left(\forall m \in I, i \in I,\; i \ne m \Rightarrow \operatorname{IsPositiveCriticalCoefficient}\left(d, m, i, b\left(m, i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPositiveCriticalData` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

Every off-diagonal entry is a least positive coefficient; unused diagonal entries are zero.

**Definition 1.13 (Minimal relation witnesses).**

$$\operatorname{IsMinimalRelation}\left(d, i, k, z\right) \Leftrightarrow \left(\left(\operatorname{IsCriticalCoefficient}\left(d, i, k\right) \land z\left(i\right) = 0\right) \land \operatorname{eval}\left(d, z\right) = k \cdot d\left(i\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsMinimalRelation` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

The coefficient is least and the vector is any allowed i-free factorization.

**Definition 1.14 (Positive minimal relation witnesses).**

$$\operatorname{IsPositiveMinimalRelation}\left(d, m, i, k, z\right) \Leftrightarrow \left(\left(\left(\left(i \ne m \land \operatorname{IsPositiveCriticalCoefficient}\left(d, m, i, k\right)\right) \land z\left(i\right) = 0\right) \land 0 < z\left(m\right)\right) \land \operatorname{eval}\left(d, z\right) = k \cdot d\left(i\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPositiveMinimalRelation` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

The vector is any allowed i-free factorization with positive coordinate m.

**Definition 1.15 (Boundary abbreviation).**

$$\operatorname{boundaryCoefficient}\left(b, i\right) = b\left(0, i\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.boundaryCoefficient` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

This is b_(0,ii), abbreviated b_ii in the source.

**Definition 1.16 (Primary tuples).**

$$\operatorname{IsPrimary}\left(a, b\right) \Leftrightarrow \left(\exists m \in I, i \in I, j \in I,\; \left(\left(\left(i \ne m \land j \ne m\right) \land i \ne j\right) \land a\left(i\right) = b\left(m, i\right)\right) \land a\left(j\right) = b\left(m, j\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPrimary` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

For some m, the critical and positive critical coefficients agree at two distinct other indices.

**Definition 1.17 (Pure factorizations).**

$$\forall j \in I,\; \left(j = i \Rightarrow \operatorname{coordinate}\left(\operatorname{pure}\left(i, k\right), j\right) = k\right) \land \left(j \ne i \Rightarrow \operatorname{coordinate}\left(\operatorname{pure}\left(i, k\right), j\right) = 0\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.pure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All coordinates except the indicated one are zero.

**Definition 1.18 (Ordering by critical pairs).**

$$\operatorname{HasSecondaryOrdering}\left(d, a\right) \Leftrightarrow \left(\left(\left(\left(a\left(0\right) \cdot d\left(0\right) \ne a\left(2\right) \cdot d\left(2\right) \land \operatorname{factorizations}\left(d, a\left(0\right) \cdot d\left(0\right)\right) = \left\{\operatorname{pure}\left(0, a\left(0\right)\right), \operatorname{pure}\left(1, a\left(1\right)\right)\right\}\right) \land \operatorname{factorizations}\left(d, a\left(1\right) \cdot d\left(1\right)\right) = \left\{\operatorname{pure}\left(0, a\left(0\right)\right), \operatorname{pure}\left(1, a\left(1\right)\right)\right\}\right) \land \operatorname{factorizations}\left(d, a\left(2\right) \cdot d\left(2\right)\right) = \left\{\operatorname{pure}\left(2, a\left(2\right)\right), \operatorname{pure}\left(3, a\left(3\right)\right)\right\}\right) \land \operatorname{factorizations}\left(d, a\left(3\right) \cdot d\left(3\right)\right) = \left\{\operatorname{pure}\left(2, a\left(2\right)\right), \operatorname{pure}\left(3, a\left(3\right)\right)\right\}\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.HasSecondaryOrdering` (`✓ std3`).

*Citation.* Kazimierz Chomicz (2026). *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*. DOI: [10.48550/arXiv.2609.04000](https://doi.org/10.48550/arXiv.2609.04000). URL: <https://arxiv.org/abs/2609.04000v1>.

*Commentary.*

The two critical degrees are distinct. Each of the four full critical fibers is exactly the displayed two-point set. This is an ordering by pairs, with no assumption of increasing generator size.

**Definition 1.19 (Ordered secondary data).**

$$\operatorname{IsOrderedSecondary}\left(d, a, b\right) \Leftrightarrow \left(\left(\left(\left(\operatorname{IsNumericalGeneratingTuple}\left(d\right) \land \operatorname{IsCriticalData}\left(d, a\right)\right) \land \operatorname{IsPositiveCriticalData}\left(d, b\right)\right) \land \left(\neg \operatorname{IsPrimary}\left(a, b\right)\right)\right) \land \operatorname{HasSecondaryOrdering}\left(d, a\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsOrderedSecondary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full positive minimal gcd-one domain, all coefficient data, non-primary condition, and four exact fibers are retained.

**Definition 1.20 (Left-pair factorizations).**

$$\operatorname{leftPair}\left(d, n\right) = \{z \in \operatorname{Factorizations}\left(d, n\right) \mid z\left(2\right) = 0 \land z\left(3\right) = 0\}$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.leftPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates 2 and 3 vanish.

**Definition 1.21 (Right-pair factorizations).**

$$\operatorname{rightPair}\left(d, n\right) = \{z \in \operatorname{Factorizations}\left(d, n\right) \mid z\left(0\right) = 0 \land z\left(1\right) = 0\}$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.rightPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates 0 and 1 vanish.

**Definition 1.22 (Exactly two pair components).**

$$\operatorname{HasExactlyPairComponents}\left(d, n\right) \Leftrightarrow \left(\exists c0 \in \operatorname{ConnectedComponent}\left(\operatorname{factorizationGraph}\left(d, n\right)\right), c1 \in \operatorname{ConnectedComponent}\left(\operatorname{factorizationGraph}\left(d, n\right)\right),\; \left(\left(c0 \ne c1 \land \operatorname{supp}\left(c0\right) = \operatorname{leftPair}\left(d, n\right)\right) \land \operatorname{supp}\left(c1\right) = \operatorname{rightPair}\left(d, n\right)\right) \land \left(\forall c \in \operatorname{ConnectedComponent}\left(\operatorname{factorizationGraph}\left(d, n\right)\right),\; c = c0 \lor c = c1\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.HasExactlyPairComponents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two distinct actual connected components have precisely the left and right pair supports, and every component equals one of them. Component supports are nonempty.

**Definition 1.23 (The full boundary assertion).**

$$claim \Leftrightarrow \left(\left(\forall d \in Generators,\; \operatorname{IsNumericalGeneratingTuple}\left(d\right) \Rightarrow \left(\exists a \in CriticalCoefficients, b \in PositiveCriticalCoefficients,\; \operatorname{IsCriticalData}\left(d, a\right) \land \operatorname{IsPositiveCriticalData}\left(d, b\right)\right)\right) \land \left(\forall d \in Generators, a \in CriticalCoefficients, b \in PositiveCriticalCoefficients,\; \operatorname{IsOrderedSecondary}\left(d, a, b\right) \Rightarrow \left(\forall i \in I,\; \left(i = 2 \lor i = 3\right) \Rightarrow \left(\left(\left(b\left(0, i\right) \cdot d\left(i\right) \in \operatorname{Betti}\left(d\right) \Leftrightarrow b\left(0, i\right) = \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right)\right) \land \left(b\left(0, i\right) = \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right) \Rightarrow \operatorname{HasExactlyPairComponents}\left(d, b\left(0, i\right) \cdot d\left(i\right)\right)\right)\right) \land \left(b\left(0, i\right) \ne \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right) \Rightarrow \operatorname{Connected}\left(\operatorname{factorizationGraph}\left(d, b\left(0, i\right) \cdot d\left(i\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion includes global coefficient existence and quantifies over every allowed coefficient datum, and both indices 2 and 3. The criterion is b_(0,ii) = gcd(d_0,d_1)/gcd(gcd(d_0,d_1),d_i). Equality gives exactly the two pair components; inequality gives connectivity of the entire graph.

**Theorem 1.24 (Deleting a forbidden coordinate).**

$$\forall d \in Generators, m \in I, i \in I, k \in \mathbb{N}, z \in Factorization,\; \left(\left(\left(\left(\left(\forall j \in I,\; 0 < d\left(j\right)\right) \land i \ne m\right) \land \operatorname{IsPositiveCriticalCoefficient}\left(d, m, i, k\right)\right) \land \operatorname{eval}\left(d, z\right) = k \cdot d\left(i\right)\right) \land 0 < z\left(m\right)\right) \Rightarrow z\left(i\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.positive_minimum_excludes_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every factorization of the positive minimal degree with positive coordinate m, the i coordinate vanishes. Subtracting all i copies would otherwise yield a strictly smaller positive coefficient. Positivity supplies both subtraction guards.

**Theorem 1.25 (Positive representation forced by a critical pair).**

$$\forall d \in Generators, x \in I, y \in I, c \in I, A \in \mathbb{N}, B \in \mathbb{N},\; \left(\left(\left(\left(\left(\left(\forall j \in I,\; 0 < d\left(j\right)\right) \land x \ne y\right) \land c \ne x\right) \land c \ne y\right) \land \operatorname{IsCriticalCoefficient}\left(d, x, A\right)\right) \land \operatorname{factorizations}\left(d, A \cdot d\left(x\right)\right) = \left\{\operatorname{pure}\left(x, A\right), \operatorname{pure}\left(y, B\right)\right\}\right) \Rightarrow \left(\exists u \in \mathbb{N}, v \in \mathbb{N},\; \left(0 < u \land 0 < v\right) \land \operatorname{gcd}\left(d\left(x\right), d\left(y\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(x\right), d\left(y\right)\right), d\left(c\right)\right) \cdot d\left(c\right) = u \cdot d\left(x\right) + v \cdot d\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.critical_pair_positive_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalize the pair by its gcd and choose a positive residue representative alpha. If the remaining coefficient were nonpositive, a nonnegative vector using the external generator would belong to the entire two-point critical fiber, a contradiction. Thus both coefficients in the threshold representation are positive.

**Theorem 1.26 (Strict critical and threshold bounds).**

$$\forall d \in Generators, a \in CriticalCoefficients, b \in PositiveCriticalCoefficients, i \in I,\; \left(\operatorname{IsOrderedSecondary}\left(d, a, b\right) \land \left(i = 2 \lor i = 3\right)\right) \Rightarrow \left(a\left(i\right) < b\left(0, i\right) \land b\left(0, i\right) \le \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.secondary_boundary_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive boundary relation cannot belong to its right critical fiber, giving a strict lower bound. The positive left-pair representation gives the upper threshold bound. Both right indices are quantified.

**Theorem 1.27 (No mixed-support factorization at equality).**

$$\forall d \in Generators, a \in CriticalCoefficients, b \in PositiveCriticalCoefficients, i \in I, z \in Factorization,\; \left(\left(\left(\operatorname{IsOrderedSecondary}\left(d, a, b\right) \land \left(i = 2 \lor i = 3\right)\right) \land b\left(0, i\right) = \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right)\right) \land \operatorname{eval}\left(d, z\right) = b\left(0, i\right) \cdot d\left(i\right)\right) \Rightarrow \left(\left(z\left(0\right) = 0 \land z\left(1\right) = 0\right) \lor \left(z\left(2\right) = 0 \land z\left(3\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.equality_excludes_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Move a positive left contribution to coordinate 0, preserving both right coordinates. The positive minimum excludes coordinate i. Divisibility forces enough copies of the other right generator to exchange its critical relation, contradicting the same minimum.

**Theorem 1.28 (The full boundary criterion and graph alternatives).**

$$\left(\forall d \in Generators,\; \operatorname{IsNumericalGeneratingTuple}\left(d\right) \Rightarrow \left(\exists a \in CriticalCoefficients, b \in PositiveCriticalCoefficients,\; \operatorname{IsCriticalData}\left(d, a\right) \land \operatorname{IsPositiveCriticalData}\left(d, b\right)\right)\right) \land \left(\forall d \in Generators, a \in CriticalCoefficients, b \in PositiveCriticalCoefficients,\; \operatorname{IsOrderedSecondary}\left(d, a, b\right) \Rightarrow \left(\forall i \in I,\; \left(i = 2 \lor i = 3\right) \Rightarrow \left(\left(\left(b\left(0, i\right) \cdot d\left(i\right) \in \operatorname{Betti}\left(d\right) \Leftrightarrow b\left(0, i\right) = \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right)\right) \land \left(b\left(0, i\right) = \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right) \Rightarrow \operatorname{HasExactlyPairComponents}\left(d, b\left(0, i\right) \cdot d\left(i\right)\right)\right)\right) \land \left(b\left(0, i\right) \ne \operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right)/\operatorname{gcd}\left(\operatorname{gcd}\left(d\left(0\right), d\left(1\right)\right), d\left(i\right)\right) \Rightarrow \operatorname{Connected}\left(\operatorname{factorizationGraph}\left(d, b\left(0, i\right) \cdot d\left(i\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A right hub has both right coordinates positive. At equality a left hub has both left coordinates positive, and the exclusion of mixed support partitions the entire fiber into exactly their two components. Below the threshold, divisibility excludes every pure-left vertex; every vertex reaches the right hub. Coefficient existence follows by well-ordering from the pure relation d_m*d_i = d_i*d_m.

## References

- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.Betti`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.HasExactlyPairComponents`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.HasSecondaryOrdering`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsCriticalCoefficient`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsCriticalData`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsMinimalRelation`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsNumericalGeneratingTuple`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsOrderedSecondary`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPositiveCriticalCoefficient`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPositiveCriticalData`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPositiveMinimalRelation`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.IsPrimary`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.RRelated`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.boundaryCoefficient`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.claim`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.critical_pair_positive_representation`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.equality_excludes_mixed`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.eval`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.factorizationGraph`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.factorizations`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.leftPair`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.positive_minimum_excludes_coordinate`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.pure`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.result`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.rightPair`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.secondary_boundary_bounds`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.semigroup`
- Truth anchor: `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.support`
