# The maximum number of strongly complementary permutation matrices

## Abstract

The maximum size of a strongly complementary permutation family is the largest power of two dividing its positive dimension.

**Definition 1.1 (Complementarity of matrix entries).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(p: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{N}\right)\right), \left(\forall \left(q: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{N}\right)\right), \left(\left(\operatorname{StronglyComplementaryPermutationMaximum.IsComplementary}\left(p, q\right)\right) \Leftrightarrow \left(\forall \left(i: \alpha\right), \left(\forall \left(j: \alpha\right), \left(\forall \left(h: \alpha\right), \left(\forall \left(k: \alpha\right), \left(\left(p\left(i, j\right) = 1\right) \Rightarrow \left(\left(p\left(h, k\right) = 1\right) \Rightarrow \left(\left(q\left(i, k\right) = 1\right) \Rightarrow \left(q\left(h, j\right) = 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.IsComplementary` (`✓ std3`).

*Citation.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

Complementarity is the four-index condition of Definition 4.1 in arXiv:1804.10715v2, unisto9.tex, lines 606–611. If p has ones at (i,j) and (h,k), and q has a one at (i,k), then q must have a one at (h,j). The predicate is defined for all natural-valued square matrices on an arbitrary index type α; being a permutation matrix is a separate condition.

**Definition 1.2 (Complementarity with disjoint support).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(p: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{N}\right)\right), \left(\forall \left(q: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{N}\right)\right), \left(\left(\operatorname{StronglyComplementaryPermutationMaximum.IsStronglyComplementary}\left(p, q\right)\right) \Leftrightarrow \left(\left(\operatorname{StronglyComplementaryPermutationMaximum.IsComplementary}\left(p, q\right)\right) \land \left(\forall \left(i: \alpha\right), \left(\forall \left(j: \alpha\right), \left(\left(p\left(i, j\right) = 1\right) \Rightarrow \left(q\left(i, j\right) = 0\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.IsStronglyComplementary` (`✓ std3`).

*Citation.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

Strong complementarity adds the requirement that every entry equal to one in p is zero in q. This is Definition 4.3 in unisto9.tex, lines 623–626; for permutation matrices it says that their supports are disjoint. As with complementarity, the predicate itself does not assume that its matrices are permutations.

**Definition 1.3 (Matrices of permutations).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left([\operatorname{DecidableEq}\left(\alpha\right)], \left(\forall \left(p: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{N}\right)\right), \left(\left(\operatorname{StronglyComplementaryPermutationMaximum.IsPermutationMatrix}\left(p\right)\right) \Leftrightarrow \left(\exists \left(\sigma: \operatorname{Equiv.Perm}\left(\alpha\right)\right), \left(p = \operatorname{Equiv.Perm.permMatrix}\left(\mathbb{N}, \sigma\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.IsPermutationMatrix` (`✓ std3`).

*Citation.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

A permutation matrix is the matrix of a bijection σ of its index type. The convention is σ.permMatrix ℕ i j = 1 exactly when σ i = j. This makes explicit the permutation matrices used in Definition 4.1 at unisto9.tex, lines 606–611. The definition allows an arbitrary index type with decidable equality, including an infinite one.

**Definition 1.4 (The supremum of the attained family sizes).**

$$\forall \left(n: \mathbb{N}\right), \left(\operatorname{StronglyComplementaryPermutationMaximum.maxStronglyComplementary}\left(n\right) = \operatorname{sSup}\left(\{\left(k: \mathbb{N}\right) \mid \exists \left(s: \operatorname{Finset}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{N}\right)\right)\right), \left(\left(\forall \left(p: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{N}\right)\right), \left(\left(p \in s\right) \Rightarrow \left(\operatorname{StronglyComplementaryPermutationMaximum.IsPermutationMatrix}\left(p\right)\right)\right)\right) \land \left(\left(\operatorname{Set.Pairwise}\left(\left(\operatorname{SetLike.coe}\left(s\right): \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{N}\right)\right)\right), \operatorname{StronglyComplementaryPermutationMaximum.IsStronglyComplementary}\right)\right) \land \left(\operatorname{Finset.card}\left(s\right) = k\right)\right)\right)\}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.maxStronglyComplementary` (`✓ std3`).

*Citation.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

For each natural n, take the supremum in ℕ of the cardinalities of finite sets of n by n permutation matrices whose distinct members are pairwise strongly complementary. SetLike.coe explicitly includes the finite set s into the set of matrices before Pairwise is applied. All matrix entries, cardinalities, and supremum values are natural numbers. This is the maximal number in unisto9.tex, lines 678–690, expressed as a supremum; the function also extends to n = 0.

**Definition 1.5 (The maximum-cardinality identity in every positive dimension).**

$$\operatorname{StronglyComplementaryPermutationMaximum.claim} = \left(\forall \left(n: \mathbb{N}\right), \left(\left(1 \le n\right) \Rightarrow \left(\operatorname{StronglyComplementaryPermutationMaximum.maxStronglyComplementary}\left(n\right) = 2^{\operatorname{padicValNat}\left(2, n\right)}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

For every natural n at least one, the maximum is 2 raised to padicValNat 2 n, the exponent of two in n. This answers the cardinality part of the question at unisto9.tex, lines 678–690. The question there about unistochasticity of the interior of the polytope is separate from this identity.

**Theorem 1.6 (The sharp bound and a family attaining it).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(1 \le n\right) \Rightarrow \left(\operatorname{StronglyComplementaryPermutationMaximum.maxStronglyComplementary}\left(n\right) = 2^{\operatorname{padicValNat}\left(2, n\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/rajchel-gasiorowski-zyczkowski-2018-strongly-complementary-permutations` (proved) by `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rajchel-gasiorowski-zyczkowski-2018-strongly-complementary-permutations","declaration_gid":"D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

For a permutation σ, the (i,j) entry of its matrix is one exactly when σ i = j and is zero exactly when σ i ≠ j. The map taking σ to its matrix is injective. Complementarity of the matrices of σ and τ is equivalent to the relative permutation σ⁻¹τ being an involution: in the forward direction apply the four-index condition with i = x, j = σ x, h = σ⁻¹(τ x), and k = τ x; in the reverse direction the three entries equal to one give σ⁻¹(τ i) = h, and applying the involution at i gives τ h = σ i = j. Disjoint support is equivalent to the absence of fixed points of σ⁻¹τ. Thus strong complementarity means precisely a fixed-point-free involution.

Replacing every σ by σρ⁻¹ conjugates each relative permutation by ρ, preserving this condition. A finite matrix family s lifts to the finite set of all permutations whose matrices belong to s; the matrix map takes that set onto s and preserves cardinality. For a nonempty permutation family choose a member ρ. The replacement σ ↦ σρ⁻¹ is injective, preserves cardinality and strong complementarity, and produces a family t containing the identity.

Every member of t squares to the identity, by comparison with the identity. For distinct σ and τ in t, their relative product is also an involution. Since σ and τ are their own inverses, inverting that product gives στ = τσ. Hence the generators commute. Every element of the subgroup they generate squares to the identity: this property holds for the generators and the identity, is preserved under inverses, and is preserved under products of commuting elements.

For any point x, evaluation σ ↦ σ x embeds a pairwise strongly complementary family into its generated subgroup's orbit of x. Indeed σ x = τ x for distinct members would make σ⁻¹τ fix x. For a 2-group acting on Fin n with n at least one, every orbit has size 2 raised to a natural exponent. Choose the smallest such exponent a. Its orbit size 2^a divides every other orbit size, so it divides their sum n.

The subgroup generated by t is a 2-group because each element squares to the identity. Evaluating t in an orbit of least size therefore gives |t| ≤ 2^a, with 2^a dividing n. Thus a ≤ padicValNat 2 n and |t| ≤ 2^(padicValNat 2 n). Cardinality preservation gives the bound for the original permutation family; the empty family satisfies it as well. Lifting matrix families to permutations then gives the same upper bound for matrices.

For the matching family, write n = 2^a m with a = padicValNat 2 n and m = n.divMaxPow 2. Here m is positive because n is positive, and m is odd because no further factor of two divides it. Choose a bijection e from Fin n to (Fin a → ZMod 2) × Fin m. For each vector v in Fin a → ZMod 2, transport the translation (w,z) ↦ (v+w,z) back along e to a permutation of Fin n.

These permutations are distinct: evaluating at the point corresponding to (0,0) recovers v, using m > 0. The relative permutation for vectors u and v translates by v−u. It is an involution since every coordinate has characteristic two. A fixed point forces v−u = 0, hence u = v. Distinct vectors therefore give strongly complementary matrices. There are 2^a vectors, and injectivity of the matrix map preserves that cardinality when passing to the matrix family.

The set of attained cardinalities thus contains 2^(padicValNat 2 n), and every attained cardinality is at most this number. Its supremum is at most this bound and at least the attained value, proving the identity for every n ≥ 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.IsComplementary`
- Truth anchor: `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.IsPermutationMatrix`
- Truth anchor: `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.IsStronglyComplementary`
- Truth anchor: `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.maxStronglyComplementary`
- Truth anchor: `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.result`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundOutcome](../Games/DivisorNimBoundOutcome.md)
