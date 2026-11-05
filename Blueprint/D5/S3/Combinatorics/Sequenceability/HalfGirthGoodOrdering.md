# Original-label Good orders above half girth

## Abstract

Original-label Good orders above half girth

**Theorem 1.1 (Original-label Good orders above half girth).**

$$\forall X \in \mathrm{FiniteType},\; \forall G \in \mathrm{AddCommGroup},\; \forall a \in \mathrm{Map}\left(X, G\right),\; \forall k \in \mathrm{Nat},\; ((\mathrm{Injective}\left(a\right)) \land ((\forall x \in X,\; \neg \mathrm{a}\left(x\right) = 0) \land ((\mathrm{Le}\left(2, k\right)) \land ((\mathrm{Le}\left(k, \mathrm{card}\left(X\right)\right)) \land ((\mathrm{Lt}\left(\mathrm{card}\left(X\right), \mathrm{mul}\left(2, k\right)\right)) \land (\forall T \in \mathrm{Finset}\left(X\right),\; ((\mathrm{Nonempty}\left(T\right)) \land ((\neg T = \mathrm{univ}) \land (\mathrm{sum}\left(T, a\right) = 0))) \Rightarrow (\mathrm{Le}\left(k, \mathrm{card}\left(T\right)\right)))))))) \Rightarrow (\exists w \in \mathrm{List}\left(X\right),\; (\mathrm{Perm}\left(w, \mathrm{univToList}\left(X\right)\right)) \land (\mathrm{Good}\left(\mathrm{map}\left(a, w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/HalfGirthGoodOrdering.exists_good_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X is finite, m is its cardinality, G is any additive commutative group, and a maps the original indices injectively to nonzero labels. The integer k satisfies 2 ≤ k ≤ m and m < 2k. Every nonempty proper original-index subset with sum zero has cardinality at least k. The resulting list is a permutation of all original indices. Good has its existing meaning: every nonempty proper consecutive subword of the mapped list has nonzero original-group sum.

If the complete proper-zero family is empty, any enumeration works. Otherwise choose a minimum member S of cardinality K, and fix any order C of its complement, of length l < K. For nonempty proper A ⊂ S and B ⊆ C with equal sums, the original-index set (S \ A) ∪ B is a nonempty proper zero subset. Minimality gives |A| ≤ |B|. This rank constraint is derived from the complete zero family.

Build a list r of S greedily. After d chosen entries, a suffix of C can forbid the next entry only if its length is at least d+1, by the replacement rank constraint. Each such suffix sum excludes at most one remaining label, by injectivity. The remaining set has K-d entries and at most max(l-d,0) forbidden values, so an entry exists. The final entry needs no avoidance condition. Thus every nonempty proper prefix of r has sum distinct from every nonempty suffix of C.

In C followed by reverse(r), intervals internal to either block are shorter than K, except the whole zero block S. For a crossing interval, its S prefix has sum equal to the negative of the complementary r prefix. Greedy avoidance excludes zero; when the whole S block is used, the nonempty C suffix has length below K. Hence S is the sole proper zero interval. Equivalently the only collision between distinct prefix sums is at the start and end of S. The proof uses the existing prefix-sum criterion in SeparatedPrefixReflection.good_iff.

Swap the last complement index c with the first reversed-S index s. Only the prefix value at this boundary changes. On its left, every resulting interval has length at most l < K. On its right, an interval starting at c has length at most K. A zero one must use all of S except s and therefore has sum a(c)-a(s), which is nonzero. This excludes all collisions and proves Good for the literal swapped enumeration. No auxiliary labels, zero-total premise, torsion restriction, or fixed bound on m is used. The empty-family branch includes k=m.

For the integral application, let H cover every permutation by a nonempty proper interval, and let M be the exact integer span of its Boolean rows in the free integer module on X. The quotient labels are e_i+M. Submodule.Quotient.mk_eq_zero and Submodule.ker_mkQ identify their zero sums with literal membership in M. Absence of original units and differences makes these labels nonzero and injective. If M contained no nonempty Boolean row of size at most floor(m/2), the complete quotient zero family would satisfy the theorem with k=floor(m/2)+1. Its Good enumeration contradicts coverage by H. Thus an actual short Boolean row lies in M, with integer coefficients on the original H rows, as expressed by Submodule.mem_span_image_iff_exists_fun. This is an application of exact quotient suppliers, with no rational saturation. The short row need not be a row of H or a unit or difference. The unrestricted Good and primitive-blocker problems remain open when the complete zero family has minimum size at most m/2. No claim of novelty, consensus, or resolution of those unrestricted problems is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/HalfGirthGoodOrdering.exists_good_order`
- Dependency: [D5/S1/Words/Sequenceability/SeparatedPrefixReflection](../../../S1/Words/Sequenceability/SeparatedPrefixReflection.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum](PairedZeroSubsetSpectrum.md)
