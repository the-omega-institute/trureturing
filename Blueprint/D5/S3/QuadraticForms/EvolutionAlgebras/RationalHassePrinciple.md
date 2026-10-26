# Rational evolution algebras and scalar extension

## Abstract

Rational evolution products, actual tensor scalar extension, and two-way monomial coefficient comparisons for full algebra isomorphisms.

Multiplication is bilinear and may be nonassociative and nonunital. A natural basis is defined over the stated ground field. All finite dimensions, including zero, and disconnected support graphs are allowed. The Hasse existence proposition below is Conjecture 7 of Kaygorodov, Martin Gonzalez and Viruel, arXiv:2610.22248v1, https://arxiv.org/html/2610.22248v1#Thmconjecture7. Monomiality is an algebraic reduction; it does not supply the local-to-global implication.

**Definition 1.1 (Bilinear multiplication).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)] \forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \operatorname{Product}\left(K, V\right) = \operatorname{LinearMap}\left(K, V, \operatorname{LinearMap}\left(K, V, V\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Product(K,V) is the type of K-bilinear maps from V times V to V. It imposes neither associativity nor a unit.

**Definition 1.2 (Perfection).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)] \forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall mu \in \operatorname{Product}\left(K, V\right),\; \operatorname{Perfect}\left(mu\right) \Leftrightarrow \operatorname{SpanOfAllPairProducts}\left(K, mu\right) = Top$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Perfect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Perfect(mu) means span_K {mu(x,y) : x,y in V}=V. The span contains all pair products.

**Definition 1.3 (A natural basis).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)] \forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(K, V\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, V\right),\; \operatorname{Natural}\left(mu, b\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; i \ne j \Rightarrow \operatorname{Apply}\left(mu, \operatorname{b}\left(i\right), \operatorname{b}\left(j\right)\right) = 0\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Natural` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural(mu,b) requires mu(b(i),b(j))=0 for every unequal pair of indices. The supplied b is already an ordinary basis.

**Definition 1.4 (The full algebra isomorphism relation).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)] \forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall W \in Type,\; [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(K, W\right)] \forall mu \in \operatorname{Product}\left(K, V\right),\; \forall nu \in \operatorname{Product}\left(K, W\right),\; \operatorname{Isomorphic}\left(mu, nu\right) \Leftrightarrow \left(\exists f \in \operatorname{LinearEquiv}\left(K, V, W\right),\; \forall x \in V,\; \forall y \in V,\; \operatorname{f}\left(\operatorname{Apply}\left(mu, x, y\right)\right) = \operatorname{Apply}\left(nu, \operatorname{f}\left(x\right), \operatorname{f}\left(y\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Isomorphic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An isomorphism is any K-linear equivalence f satisfying f(mu(x,y))=nu(f(x),f(y)) for every x,y. No prescribed permutation, graph, or basis preservation is required.

**Definition 1.5 (Finite rational evolution algebras).**

$$\operatorname{RationalEvolutionAlgebra}\left(\right) = \operatorname{FiniteDimensionalRationalVectorSpacesWithBilinearProductAndNaturalBasis}\left(\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.RationalEvolutionAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is an arbitrary type with an additive commutative group and rational module structure, together with finite dimensionality, a bilinear multiplication, and existence of n and a natural rational basis indexed by Fin(n). Perfection is a separate predicate, not part of this bundle.

**Definition 1.6 (Actual scalar extension).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Algebra}\left(\operatorname{Rational}\left(\right), F\right)] \forall A \in \operatorname{RationalEvolutionAlgebra}\left(\right),\; \forall B \in \operatorname{RationalEvolutionAlgebra}\left(\right),\; \operatorname{IsomorphicOver}\left(F, A, B\right) \Leftrightarrow \operatorname{Isomorphic}\left(\operatorname{BilinearBaseChange}\left(F, \operatorname{multiplication}\left(A\right)\right), \operatorname{BilinearBaseChange}\left(F, \operatorname{multiplication}\left(B\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.IsomorphicOver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two carriers are F tensor_Q A and F tensor_Q B. Their multiplications are Mathlib LinearMap.BilinMap.baseChange: (a tensor x)(b tensor y)=ab tensor mu(x,y), extended bilinearly to every tensor. IsomorphicOver uses arbitrary F-linear multiplication-preserving equivalences.

**Definition 1.7 (The full Hasse failure existence proposition).**

$$\exists A \in \operatorname{RationalEvolutionAlgebra}\left(\right),\; \exists B \in \operatorname{RationalEvolutionAlgebra}\left(\right),\; \operatorname{Perfect}\left(\operatorname{multiplication}\left(A\right)\right) \land \left(\operatorname{Perfect}\left(\operatorname{multiplication}\left(B\right)\right) \land \left(\operatorname{IsomorphicOver}\left(\operatorname{Real}\left(\right), A, B\right) \land \left(\left(\forall p \in \operatorname{NaturalNumbers}\left(\right),\; \operatorname{Prime}\left(p\right) \Rightarrow \operatorname{IsomorphicOver}\left(\operatorname{Padic}\left(p\right), A, B\right)\right) \land \neg (\operatorname{Isomorphic}\left(\operatorname{multiplication}\left(A\right), \operatorname{multiplication}\left(B\right)\right))\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exist finite-dimensional perfect rational evolution algebras A and B isomorphic after extension to the real numbers and to Q_p for every rational prime p, yet not rationally isomorphic. The quantifier ranges over every prime; no finite list or dimension bound is substituted. This node states the conjecture and asserts no proof or refutation.

**Theorem 1.8 (Isomorphisms are forced to be monomial).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)] \forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall W \in Type,\; [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(K, W\right)] \forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(K, V\right),\; \forall nu \in \operatorname{Product}\left(K, W\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, V\right),\; \forall c \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, W\right),\; \operatorname{Natural}\left(mu, b\right) \Rightarrow \left(\operatorname{Natural}\left(nu, c\right) \Rightarrow \left(\operatorname{Perfect}\left(nu\right) \Rightarrow \left(\forall f \in \operatorname{LinearEquiv}\left(K, V, W\right),\; \left(\forall x \in V,\; \forall y \in V,\; \operatorname{f}\left(\operatorname{Apply}\left(mu, x, y\right)\right) = \operatorname{Apply}\left(nu, \operatorname{f}\left(x\right), \operatorname{f}\left(y\right)\right)\right) \Rightarrow \left(\exists sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \exists t \in \operatorname{Fin}\left(n\right) \to K,\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{t}\left(i\right) \ne 0\right) \land \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{Coordinate}\left(c, \operatorname{f}\left(\operatorname{b}\left(j\right)\right), i\right) = \operatorname{IfThenElse}\left(\operatorname{sigma}\left(i\right) = j, \operatorname{t}\left(i\right), 0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphism_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any field K and two natural bases of equal finite size, perfection of the target forces the matrix of a multiplication isomorphism to have at most one nonzero entry in each row. Surjectivity makes every row nonzero; injectivity makes every column nonzero. A finite permutation and nonzero row scalars result. Source perfection is unnecessary. The two products and bases may be different. The proof uses all pair products to show injectivity of the target structure map, then constructs the permutation from the unique nonzero entry in each row. It covers the zero-dimensional case without an extra hypothesis.

**Definition 1.9 (Square structure coefficients).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)] \forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(K, V\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, V\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{structureCoefficient}\left(mu, b, i, j\right) = \operatorname{Coordinate}\left(b, \operatorname{Apply}\left(mu, \operatorname{b}\left(i\right), \operatorname{b}\left(i\right)\right), j\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.structureCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient a(mu,b,i,j) is the j-th coordinate of mu(b(i),b(i)) in b. The first index selects the squared basis vector and the second its output coordinate.

**Theorem 1.10 (Full isomorphisms and monomial equations).**

$$\forall K \in Type,\; [\operatorname{Field}\left(K\right)] \forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall W \in Type,\; [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(K, W\right)] \forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall m \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(K, V\right),\; \forall nu \in \operatorname{Product}\left(K, W\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, V\right),\; \forall c \in \operatorname{Basis}\left(\operatorname{Fin}\left(m\right), K, W\right),\; \operatorname{Natural}\left(mu, b\right) \Rightarrow \left(\operatorname{Natural}\left(nu, c\right) \Rightarrow \left(\operatorname{Perfect}\left(nu\right) \Rightarrow \left(\operatorname{Isomorphic}\left(mu, nu\right) \Leftrightarrow \left(\exists e \in \operatorname{Equiv}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \exists d \in \operatorname{Fin}\left(n\right) \to \operatorname{Units}\left(K\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{structureCoefficient}\left(mu, b, i, j\right) \cdot \operatorname{Value}\left(\operatorname{d}\left(j\right)\right) = \operatorname{Value}\left(\operatorname{d}\left(i\right)\right) \cdot \operatorname{Value}\left(\operatorname{d}\left(i\right)\right) \cdot \operatorname{structureCoefficient}\left(nu, c, \operatorname{e}\left(i\right), \operatorname{e}\left(j\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_iff_monomial_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let b and c be natural bases indexed independently by Fin(n) and Fin(m) over any field K, with perfect target multiplication nu. An arbitrary multiplicative linear equivalence exists exactly when there are a bijection e:Fin(n) to Fin(m) and units d(i) such that a(mu,b,i,j)d(j)=d(i)^2 a(nu,c,e(i),e(j)) for every i,j. The corresponding map sends b(i) to d(i)c(e(i)). A given linear equivalence forces n=m by preservation of finrank; monomiality then gives e as the inverse of its target-row permutation. Comparing the image of each square in coordinate e(j) gives the displayed orientation. Conversely, reindexing and scaling c by units constructs a linear bijection. The equations prove square preservation, and naturality proves preservation of every mixed basis product. Bilinear extensionality extends this to all vectors. No source perfection, positive dimension, connected support, or prescribed permutation is required.

**Theorem 1.11 (The comparison on tensor scalar extensions).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Algebra}\left(\operatorname{Rational}\left(\right), F\right)] \forall A \in \operatorname{RationalEvolutionAlgebra}\left(\right),\; \forall B \in \operatorname{RationalEvolutionAlgebra}\left(\right),\; \forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall m \in \operatorname{NaturalNumbers}\left(\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), \operatorname{Rational}\left(\right), \operatorname{Carrier}\left(A\right)\right),\; \forall c \in \operatorname{Basis}\left(\operatorname{Fin}\left(m\right), \operatorname{Rational}\left(\right), \operatorname{Carrier}\left(B\right)\right),\; \operatorname{Natural}\left(\operatorname{multiplication}\left(A\right), b\right) \Rightarrow \left(\operatorname{Natural}\left(\operatorname{multiplication}\left(B\right), c\right) \Rightarrow \left(\operatorname{Perfect}\left(\operatorname{multiplication}\left(B\right)\right) \Rightarrow \left(\operatorname{IsomorphicOver}\left(F, A, B\right) \Leftrightarrow \left(\exists e \in \operatorname{Equiv}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \exists d \in \operatorname{Fin}\left(n\right) \to \operatorname{Units}\left(F\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{algebraMap}\left(\operatorname{Rational}\left(\right), F, \operatorname{structureCoefficient}\left(\operatorname{multiplication}\left(A\right), b, i, j\right)\right) \cdot \operatorname{Value}\left(\operatorname{d}\left(j\right)\right) = \operatorname{Value}\left(\operatorname{d}\left(i\right)\right) \cdot \operatorname{Value}\left(\operatorname{d}\left(i\right)\right) \cdot \operatorname{algebraMap}\left(\operatorname{Rational}\left(\right), F, \operatorname{structureCoefficient}\left(\operatorname{multiplication}\left(B\right), c, \operatorname{e}\left(i\right), \operatorname{e}\left(j\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_over_iff_monomial_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any field F with a rational algebra structure, take rational natural bases b,c of A,B with independent finite sizes and perfect rational target B. The actual relation IsomorphicOver(F,A,B) is equivalent to the same monomial equations with every rational structure coefficient mapped to F. The bases are b.baseChange(F), c.baseChange(F), whose vectors are 1 tensor b(i) and 1 tensor c(j). Their products use precisely LinearMap.BilinMap.baseChange, so their square coefficients are the scalar images of the rational coefficients. Perfection ascends because tensors of rational pair products are pair products after extension and their F-span is the whole tensor space. Local perfection is therefore a consequence, rather than an additional assumption. This applies to the real field and to Q_p for every prime, including zero-dimensional algebras and disconnected supports. These equivalences do not establish the arithmetic local-to-global implication or settle Conjecture 7.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Isomorphic`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.IsomorphicOver`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Natural`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Perfect`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Product`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.RationalEvolutionAlgebra`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_iff_monomial_equations`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_over_iff_monomial_equations`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphism_monomial`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.structureCoefficient`
