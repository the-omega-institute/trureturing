# Rank of a character kernel

## Abstract

Over an algebraically closed field, a sum with nonzero weights of the characters of finitely many pairwise inequivalent finite-dimensional irreducible representations of a group gives a kernel whose rank is the sum of the squared dimensions.

**Theorem 1.1 (The operators of a family of irreducible representations span).**

$$\forall k \in \operatorname{Type}*,\; \forall G \in \operatorname{Type}*,\; [\operatorname{Field}\left(k\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall \iota \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(\iota\right)], \forall W \in \iota \to \operatorname{Type}*,\; [\forall i \in \iota,\; \operatorname{AddCommGroup}\left(W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{Module}\left(k, W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{FiniteDimensional}\left(k, W\left(i\right)\right)], \forall \rho \in (\forall i \in \iota,\; \operatorname{Representation}\left(k, G, W\left(i\right)\right)),\; [\forall i \in \iota,\; \operatorname{IsIrreducible}\left(\rho\left(i\right)\right)], (\forall i \in \iota, j \in \iota,\; i \ne j \Rightarrow \operatorname{IsEmpty}\left(\operatorname{Equiv}\left(\rho\left(i\right), \rho\left(j\right)\right)\right)) \Rightarrow \operatorname{span}\left(k, \operatorname{range}\left(g \mapsto (i \mapsto \rho\left(i\right)\left(g\right))\right)\right) = \prod_{i \in \iota} \operatorname{End}\left(k, W\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.span_range_pi_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Burnside (1905). *On the Condition of Reducibility of any Group of Linear Substitutions*. DOI: [10.1112/plms/s2-3.1.430](https://doi.org/10.1112/plms/s2-3.1.430).

*Commentary.*

Let k be an algebraically closed field, G a group and iota a finite index type, and for each i let rho(i) be an irreducible representation of G on a finite-dimensional k-vector space W(i), with rho(i) and rho(j) admitting no equivalence of representations when i and j are distinct. Then the families (rho(i)(g))_i, as g ranges over G, span the whole product over i of the endomorphism algebras End(W(i)). This is Burnside's theorem for a finite family. The product of the W(i) is a semisimple module over the group algebra k[G]; by Schur's lemma, with algebraic closedness and pairwise inequivalence, every k[G]-endomorphism of it acts on each factor W(i) by a scalar. The Jacobson density theorem for this semisimple module then shows that every family of endomorphisms is the action of an element of k[G], that is, a linear combination of the families (rho(i)(g))_i.

**Definition 1.2 (The weighted trace pairing).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.tracePairing`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.tracePairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a field k, a finite index type iota, finite-dimensional k-vector spaces W(i) and weights c(i) in k, the weighted trace pairing is the bilinear form on the product over i of End(W(i)) that pairs the families B and A to the sum over i of c(i) times the trace of the composite B(i) A(i). It is linear in each argument because the trace and composition are.

**Lemma 1.3 (The weighted trace pairing is nondegenerate).**

$$\forall k \in \operatorname{Type}*,\; [\operatorname{Field}\left(k\right)], \forall \iota \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(\iota\right)], \forall W \in \iota \to \operatorname{Type}*,\; [\forall i \in \iota,\; \operatorname{AddCommGroup}\left(W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{Module}\left(k, W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{FiniteDimensional}\left(k, W\left(i\right)\right)], \forall c \in \iota \to k,\; (\forall i \in \iota,\; c\left(i\right) \ne 0) \Rightarrow \left(\forall A \in \prod_{i \in \iota} \operatorname{End}\left(k, W\left(i\right)\right),\; (\forall B \in \prod_{i \in \iota} \operatorname{End}\left(k, W\left(i\right)\right),\; \operatorname{tracePairing}\left(c, B, A\right) = 0) \Rightarrow A = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.eq_zero_of_tracePairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let every weight c(i) be nonzero. If a family A of endomorphisms pairs to zero with every family B under the weighted trace pairing, then A is zero. No algebraic closedness is needed. Suppose A(j) is nonzero for some j; choose a vector v of W(j) and a linear functional f on W(j) with f(A(j) v) nonzero. Let B be the family that is the rank-one map w maps to f(w) v in position j and zero elsewhere. The pairing of B with A is c(j) times the trace of w maps to f(A(j) w) v, which is c(j) f(A(j) v), and it is nonzero.

**Theorem 1.4 (The rank of a weighted character kernel).**

$$\forall k \in \operatorname{Type}*,\; \forall G \in \operatorname{Type}*,\; [\operatorname{Field}\left(k\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall \iota \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(\iota\right)], \forall W \in \iota \to \operatorname{Type}*,\; [\forall i \in \iota,\; \operatorname{AddCommGroup}\left(W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{Module}\left(k, W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{FiniteDimensional}\left(k, W\left(i\right)\right)], \forall \rho \in (\forall i \in \iota,\; \operatorname{Representation}\left(k, G, W\left(i\right)\right)),\; [\forall i \in \iota,\; \operatorname{IsIrreducible}\left(\rho\left(i\right)\right)], (\forall i \in \iota, j \in \iota,\; i \ne j \Rightarrow \operatorname{IsEmpty}\left(\operatorname{Equiv}\left(\rho\left(i\right), \rho\left(j\right)\right)\right)) \Rightarrow \left(\forall c \in \iota \to k,\; (\forall i \in \iota,\; c\left(i\right) \ne 0) \Rightarrow \operatorname{finrank}\left(k, \operatorname{span}\left(k, \operatorname{range}\left(y \mapsto (x \mapsto \sum_{i \in \iota} c\left(i\right) \cdot \operatorname{character}\left(\rho\left(i\right), x \cdot y^{-1}\right))\right)\right)\right) = \sum_{i \in \iota} \operatorname{finrank}\left(k, W\left(i\right)\right)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.finrank_span_sum_character_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Burnside (1905). *On the Condition of Reducibility of any Group of Linear Substitutions*. DOI: [10.1112/plms/s2-3.1.430](https://doi.org/10.1112/plms/s2-3.1.430).

*Commentary.*

Let k be an algebraically closed field, G an arbitrary group and iota a finite index type. For each index i, rho(i) is a representation of G on a finite-dimensional k-vector space W(i); every rho(i) is irreducible, and rho(i) and rho(j) admit no equivalence of representations when i and j are distinct. Let c(i) be nonzero scalars. For y in G, the section of the kernel at y is the function on G sending x to the sum over i of c(i) times the character of rho(i) at x * y^-1. The statement is that these sections, as y ranges over G, span a subspace of the space of functions from G to k whose dimension is the sum over i of dim W(i)^2. In the displayed formula the arguments in square brackets are the instance hypotheses of the statement. Nothing beyond the group axioms is assumed about G: it may be infinite, and no topology or measure enters.

The sections are images of one linear map. Send a family A of endomorphisms, A(i) in End(W(i)), to the function on G whose value at x is the sum over i of c(i) times the trace of rho(i)(x) composed with A(i). Since the character of rho(i) at x * y^-1 is the trace of rho(i)(x) composed with rho(i)(y^-1), the section at y is the image of the family (rho(i)(y^-1))_i. Inversion is a bijection of G, so the span of the sections is the image of the span of the families (rho(i)(g))_i for g in G.

That span is the whole product of the endomorphism algebras End(W(i)). This is Burnside's theorem for a finite family: the product of the W(i) is a semisimple module over the group algebra k[G] whose simple summands are pairwise non-isomorphic, so by Schur's lemma every k[G]-endomorphism of the product acts on each factor by a scalar, and the Jacobson density theorem then shows that the group algebra maps onto the product of the endomorphism algebras. For a single irreducible representation this surjectivity is the theorem `D5/S3/FiniteGroups/FiniteCharacterAlgebra.asAlgebraHom_surjective_of_isIrreducible`; the family version is proved here from the density theorem on the product module rather than from that statement.

The linear map is injective because the weighted trace pairing, which pairs families B and A to the sum over i of c(i) times the trace of B(i) composed with A(i), is nondegenerate when every c(i) is nonzero: for A(j) nonzero, choose a vector v and a linear functional f with f(A(j) v) nonzero, and pair A with the family that is the rank-one map w maps to f(w) v in position j and zero elsewhere. Hence the span of the sections has the dimension of the product of the End(W(i)), which is the sum of dim W(i)^2.

Algebraic closedness enters only through Schur's lemma: the same argument applies whenever every k[G]-endomorphism of each W(i) is a scalar. It cannot simply be dropped. Over the real numbers, the rotation representation of the circle group on the plane is irreducible of dimension two, but its character at the rotation by t is 2 cos t, and the sections of c times 2 cos(s - t) are spanned by cos and sin, so the rank is two rather than four. Irreducibility cannot be dropped: the trivial action of any group on k^2 has the constant character 2, so its kernel has rank at most one rather than four. Pairwise inequivalence cannot be dropped: two copies of the trivial representation on k with weights c(1) and c(2) give the constant kernel c(1) + c(2), of rank at most one rather than two; the rank is zero for the weights 1 and -1 in every characteristic, and for the weights 1 and 1 in characteristic two.

For one representation the statement is Burnside's theorem read through the nondegenerate trace pairing; for several it is the same reading for a semisimple module with pairwise non-isomorphic simple summands.

## References

- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.asAlgebraHom_surjective_of_isIrreducible`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.eq_zero_of_tracePairing`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.finrank_span_sum_character_kernel`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.span_range_pi_eq_top`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.tracePairing`
