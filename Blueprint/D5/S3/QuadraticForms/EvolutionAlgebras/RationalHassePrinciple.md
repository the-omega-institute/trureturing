# Rational evolution algebras, components, and scalar extension

## Abstract

Rational evolution products, perfect weak component ideals, and tensor-compatible reconstruction of unrestricted algebra isomorphisms.

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

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For any field K and two natural bases of equal finite size, perfection of the target forces the matrix of a multiplication isomorphism to have at most one nonzero entry in each row. Surjectivity makes every row nonzero; injectivity makes every column nonzero. A finite permutation and nonzero row scalars result. Source perfection is unnecessary. The two products and bases may be different. The proof uses all pair products to show injectivity of the target structure map, then constructs the permutation from the unique nonzero entry in each row. It covers the zero-dimensional case without an extra hypothesis. This monomiality is Theorem 4 of Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1, credited there to Elduque–Labra. Apply that result to the target product nu with natural bases c and b.map f: multiplication preservation makes b.map f natural, and the permutation and nonzero scalars give the stated row formula up to inverse indexing.

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

**Definition 1.12 (Weak support components).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.WeakComponent`

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.WeakComponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a product mu on a vector space V over any field K and a finite basis b, WeakComponent(mu,b) is the quotient of the basis indices by the equivalence relation generated by a(mu,b,i,j) being nonzero. Thus arrow orientation is forgotten when forming components. Isolated vertices remain components, and an empty basis gives an empty component type.

**Definition 1.13 (The component of a basis vector).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentIndex`

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

componentIndex(mu,b,i) is the equivalence class of i in WeakComponent(mu,b). A nonzero square coefficient from i to j makes these two classes equal.

**Definition 1.14 (Coordinate submodules of a partition).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.coordinateSpace`

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.coordinateSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let b be a finite basis over any field K, pi any function from its indices to a type Q, and q an element of Q. coordinateSpace(b,pi,q) is the actual K-submodule of vectors whose coordinates outside the fibre pi(i)=q vanish. No nonemptiness or surjectivity of pi is required.

**Definition 1.15 (Restriction to a left ideal).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.restrictedProduct`

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.restrictedProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a K-bilinear multiplication mu and an actual submodule S, suppose mu(x,y) belongs to S for every x in S and y in V. restrictedProduct(mu,S) is the bilinear multiplication on the subtype S whose underlying value at x,y is mu(x,y). The closure proof supplies the subtype membership, and imposes no associativity or unit law.

**Definition 1.16 (The actual component submodule).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentSpace`

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

componentSpace(mu,b,q) is coordinateSpace(b,componentIndex(mu,b),q), an actual submodule of the original carrier V. The component ideal theorem identifies it with the span of the basis vectors whose indices belong to q.

**Definition 1.17 (Multiplication on a component ideal).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentProduct`

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any field K and a natural finite basis b of mu, componentProduct(mu,b,q) restricts the original multiplication to componentSpace(mu,b,q). Its value at two component vectors is their product in the ambient algebra, with the proved component membership. Naturality suffices for closure; perfection is a separate premise of the component perfection theorem.

**Theorem 1.18 (Perfect mutually orthogonal component ideals).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.component_ideals_perfect`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.component_ideals_perfect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be any field, b a basis indexed by Fin(n), and mu a bilinear product. Assume Natural(mu,b) and Perfect(mu). For every weak component q, its actual submodule is precisely the span of the b(i) with componentIndex(i)=q. For x in that submodule and arbitrary y in V, both mu(x,y) and mu(y,x) belong to it. Its restricted product is perfect. Products between vectors in any two distinct component submodules vanish. The proof projects onto one coordinate fibre. Support stability makes the projection multiplicative, and its surjectivity transports the full pair-product span onto the component pair-product span. Empty dimensions and disconnected support are included.

**Theorem 1.19 (Reconstruction from matched component ideals).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_of_component_matching`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_of_component_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any field K, take two bilinear products mu and nu on arbitrary carriers, with natural bases b and c indexed independently by Fin(n) and Fin(m). Suppose e is any bijection between their weak component types and each component q of mu has an unrestricted multiplicative K-linear equivalence to component e(q) of nu. Then mu and nu are isomorphic by an unrestricted multiplicative K-linear equivalence. No perfection assumption is needed in this direction. Coordinate projection identifies each whole space with the product of its component submodules; summation is the inverse. The given component maps and e then assemble the whole equivalence. The construction allows empty families, arbitrary component permutations, and repeated isomorphic components without choosing a canonical ordering.

**Theorem 1.20 (Every isomorphism matches the actual component ideals).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphism_matches_components`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphism_matches_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any field K, let b,c be natural bases of mu,nu with independent finite sizes, and assume Perfect(nu). For every given K-linear equivalence f preserving multiplication on all vectors, there is a bijection E of weak components such that the image of componentSpace(mu,b,q) under f is exactly componentSpace(nu,c,E(q)). Restricting that same f gives an unrestricted isomorphism of the component products. Source perfection is unnecessary. Monomiality is derived from target perfection. Its coefficient equations show that the basis-index bijection preserves and reflects every nonzero square coefficient, because all scaling factors are units. It therefore induces E on weak components, and the basis-span images give the equality of actual submodules. No basis-preserving or graph-preserving premise is added.

**Definition 1.21 (Component multiplication inside the tensor extension).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.baseChangedComponentProduct`

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.baseChangedComponentProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fields K,F with a K-algebra structure on F, take mu with a natural finite basis b. Extend mu using LinearMap.BilinMap.baseChange on F tensor_K V and use the actual basis b.baseChange(F). For a weak component of this extended product, baseChangedComponentProduct is its restricted component multiplication on the actual component submodule. Naturality after extension follows from the pure-tensor multiplication law.

**Theorem 1.22 (Tensor-compatible component reconstruction).**

Lean statement: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.scalar_extension_component_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.scalar_extension_component_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be any field equipped with an algebra structure over the rationals. Let A,B be rational evolution algebras with rational natural bases b,c of independent finite sizes, and assume both rational products are perfect. There are bijections EA,EB from their rational weak components to the components of the actual tensor-extended products. These bijections send the rational component of each basis index to the extended component of that same index. For each rational component, its submodule base change is exactly the corresponding component submodule in the extended carrier. The tensor extension of its rational restricted multiplication is isomorphic to the restricted multiplication there by an unrestricted F-linear multiplicative equivalence. Every such extended component is perfect. Moreover, IsomorphicOver(F,A,B) holds exactly when there is a bijection e between the rational component types and unrestricted component isomorphisms from the component EA(q) of the first extended product to the component EB(e(q)) of the second, for every q. The actual square coefficients are the algebraMap images of the rational coefficients; injectivity preserves their zero pattern. The tensor inclusion of each component is injective by flatness over a field and has the required component image. Its multiplication law follows first on pure tensors and then by bilinearity. In the forward direction, the scalar coefficient comparison constructs a monomial linear equivalence and its component matching. The reverse direction uses whole-product reconstruction. The theorem includes zero dimension, disconnected support, arbitrary permutations, and repeated components. It proves no arithmetic descent from all completions and does not settle Conjecture 7.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Isomorphic`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.IsomorphicOver`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Natural`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Perfect`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.Product`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.RationalEvolutionAlgebra`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.WeakComponent`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.baseChangedComponentProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentIndex`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.componentSpace`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.component_ideals_perfect`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.coordinateSpace`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_iff_monomial_equations`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_of_component_matching`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphic_over_iff_monomial_equations`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphism_matches_components`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.isomorphism_monomial`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.restrictedProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.scalar_extension_component_reconstruction`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple.structureCoefficient`
