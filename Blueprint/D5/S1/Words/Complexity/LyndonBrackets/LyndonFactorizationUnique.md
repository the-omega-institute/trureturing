# Uniqueness of Lyndon factorization

## Abstract

A nonincreasing factorization into Lyndon words is unique over any linearly ordered alphabet.

The alphabet A is any linearly ordered type, with no finiteness assumption. Words are finite lists, ordered lexicographically. IsLyndon is the existing rotation predicate: a word is nonempty and strictly smaller than each rotation arising from a split into two nonempty words. Flatten concatenates a list of words. LyndonFactors means that every member is Lyndon, and Nonincreasing means Pairwise (fun u v => v <= u), so repeated identical factors are permitted. Suffix includes the whole word. The uniqueness statement is classical. The cited paper states Chen-Fox-Lyndon factorization in Lemma 4.4 for nonempty words on a finite ordered alphabet, using the rotation definition in Definition 4.1. Its Section 2 assumes a finite alphabet; it does not state an infinite-alphabet theorem.

The arbitrary-alphabet scope follows by finite support. Given two factorizations with common concatenation w, every letter of every factor belongs to the finite set B of letters occurring in w. Give B the order inherited from A and relabel its elements by increasing rank in a finite chain. This injective order-preserving relabeling preserves and reflects word equality and lexicographic comparison, including the proper-prefix case. It commutes with concatenation and rotation, so it preserves and reflects the Lyndon predicate and the nonincrease condition. Lemma 4.4 identifies the relabeled factor lists, and injectivity recovers the original lists. One may enlarge the finite chain by unused letters if an alphabet of at least two symbols is required. If w is empty, nonemptiness of Lyndon factors forces both lists to be empty. This transfers the classical uniqueness assertion; the Lean proof below works directly in A and does not assume finite support as an additional hypothesis or claim mathematical novelty.

**Theorem 1.1 (The final factor is the minimum nonempty suffix).**

$$\forall A \in Type,\; [\operatorname{LinearOrder}\left(A\right)] \forall fs \in \operatorname{List}\left(\operatorname{List}\left(A\right)\right),\; \forall m \in \operatorname{List}\left(A\right),\; \operatorname{LyndonFactors}\left(\operatorname{append}\left(fs, \operatorname{singleton}\left(m\right)\right)\right)\land \operatorname{Nonincreasing}\left(\operatorname{append}\left(fs, \operatorname{singleton}\left(m\right)\right)\right)\Rightarrow m\neq \operatorname{nil}\left(\right)\land \operatorname{Suffix}\left(m, \operatorname{flatten}\left(\operatorname{append}\left(fs, \operatorname{singleton}\left(m\right)\right)\right)\right)\land \forall s \in \operatorname{List}\left(A\right),\; s\neq \operatorname{nil}\left(\right)\land \operatorname{Suffix}\left(s, \operatorname{flatten}\left(\operatorname{append}\left(fs, \operatorname{singleton}\left(m\right)\right)\right)\right)\Rightarrow m\leq s$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique.last_factor_is_min_nonempty_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If fs followed by the final factor m is a nonincreasing list of Lyndon words, then m is nonempty, is a suffix of the concatenation, and is no greater than every nonempty suffix of that concatenation. This is the expanded meaning of IsLeast in the Lean statement. Induct on fs. A suffix contained in the remaining concatenation satisfies the induction hypothesis. Any longer suffix has the form t followed by that remaining concatenation, with t a suffix of the first factor u. If t is empty, apply the same induction hypothesis. Otherwise the Lyndon suffix characterization gives u <= t, nonincrease gives m <= u, and extending the prefix t cannot decrease it in lexicographic order.

**Theorem 1.2 (Equal concatenations have equal factor lists).**

$$\forall A \in Type,\; [\operatorname{LinearOrder}\left(A\right)] \forall fs \in \operatorname{List}\left(\operatorname{List}\left(A\right)\right),\; \forall gs \in \operatorname{List}\left(\operatorname{List}\left(A\right)\right),\; \operatorname{LyndonFactors}\left(fs\right)\land \operatorname{Nonincreasing}\left(fs\right)\land \operatorname{LyndonFactors}\left(gs\right)\land \operatorname{Nonincreasing}\left(gs\right)\land \operatorname{flatten}\left(fs\right) = \operatorname{flatten}\left(gs\right)\Rightarrow fs = gs$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique.nonincreasing_lyndon_factorization_unique` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For any two finite lists fs and gs, if every factor in each list is Lyndon, each list is nonincreasing, and their concatenations agree, then fs = gs. There is no assumption on the factor counts or factor lengths. For nonempty factorizations the minimum-suffix theorem makes both final factors the least element of the same set, so antisymmetry identifies them. Cancel this common final word and apply induction to the remaining lists. An empty concatenation has no nonempty Lyndon factors, which supplies the empty-list cases. The result includes singleton words, repeated factors, and finite words on infinite alphabets. It asserts uniqueness, independently of any procedure constructing a factorization.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique.last_factor_is_min_nonempty_suffix`
- Truth anchor: `D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique.nonincreasing_lyndon_factorization_unique`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder](LyndonOrder.md)
