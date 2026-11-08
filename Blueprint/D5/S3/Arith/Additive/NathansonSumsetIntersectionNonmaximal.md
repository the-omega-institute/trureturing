# A nonmaximal nonbasis obstructing sumset intersections

## Abstract

Removing 2 from the even integers gives a negative answer to Nathanson's Problem 2.

**Definition 1.1 (Finite sumsets).**

$$\forall (S : \operatorname{Type}), [\operatorname{AddCommSemigroup}\left(S\right)] \forall (A : \operatorname{Set}\left(S\right)), (\operatorname{sumset}\left(A, 0\right) = \emptyset) \land ((\operatorname{sumset}\left(A, 1\right) = A) \land (\forall (h : \mathbb{N}), \operatorname{sumset}\left(A, h + 2\right) = \operatorname{sumset}\left(A, h + 1\right) + A))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.sumset` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Intersections of sumsets in additive number theory*. DOI: [10.1017/S0004972726101270](https://doi.org/10.1017/S0004972726101270). URL: <https://arxiv.org/abs/2512.23574v3>.

*Commentary.*

Section 1 (p. 1) states: “For every positive integer h, the h-fold sumset of A is the set of all sums of h not necessarily distinct elements of A, that is, hA = {a₁ + ⋯ + a_h : aᵢ ∈ A for all i = 1, …, h}.” The recursion uses pointwise set addition. The auxiliary value at h = 0 is the empty set; only positive orders occur in the question.

**Definition 1.2 (Bases of a fixed order).**

$$\forall (S : \operatorname{Type}), [\operatorname{AddCommSemigroup}\left(S\right)] \forall (h : \mathbb{N}), \forall (A : \operatorname{Set}\left(S\right)), \operatorname{IsBasis}\left(h, A\right) = (\operatorname{sumset}\left(A, h\right) = \operatorname{Set}.\operatorname{univ})$$

*Formalization.* `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.IsBasis` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Intersections of sumsets in additive number theory*. DOI: [10.1017/S0004972726101270](https://doi.org/10.1017/S0004972726101270). URL: <https://arxiv.org/abs/2512.23574v3>.

*Commentary.*

Section 1 (p. 1) states: “The subset A is a basis of order h for S if hA = S, or, equivalently, if rA,h(x) ≥ 1 for all x ∈ S.” The ambient semigroup is represented by its universal set, and nonbasis means the negation of this equality.

**Definition 1.3 (Asymptotically strict decrease).**

$$\forall (S : \operatorname{Type}), \forall (A : \mathbb{N} \to \operatorname{Set}\left(S\right)), \operatorname{AsymptoticallyStrictlyDecreasing}\left(A\right) = ((\forall (q : \mathbb{N}), A\left(q + 1\right) \subseteq A\left(q\right)) \land (\forall (N : \mathbb{N}), \exists (q : \mathbb{N}), (N \le q) \land (A\left(q\right) \ne A\left(q + 1\right))))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.AsymptoticallyStrictlyDecreasing` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Intersections of sumsets in additive number theory*. DOI: [10.1017/S0004972726101270](https://doi.org/10.1017/S0004972726101270). URL: <https://arxiv.org/abs/2512.23574v3>.

*Commentary.*

Section 1 (p. 1) states: “The sequence of sets (A_q)_{q=1}^∞ is decreasing if A_q ⊇ A_{q+1} for all q ∈ ℕ.” It continues: “The decreasing sequence (A_q)_{q=1}^∞ is strictly decreasing if A_q ≠ A_{q+1} for all q ∈ ℕ and asymptotically strictly decreasing if A_q ≠ A_{q+1} for infinitely many q.” The Lean sequence starts at 0; infinitely many unequal steps are expressed by an unequal step beyond every natural bound.

**Definition 1.4 (The universal assertion in Problem 2).**

$$\operatorname{claim} = (\forall (S : \operatorname{Type}), [\operatorname{AddCommSemigroup}\left(S\right)] [\operatorname{Infinite}\left(S\right)] \forall (h : \mathbb{N}), \forall (A : \operatorname{Set}\left(S\right)), (1 \le h) \Rightarrow ((\neg (\operatorname{IsBasis}\left(h, A\right))) \Rightarrow ((\neg ((\neg (\operatorname{IsBasis}\left(h, A\right))) \land (\forall (B : \operatorname{Set}\left(S\right)), (A \subset B) \Rightarrow (\operatorname{IsBasis}\left(h, B\right))))) \Rightarrow (\exists (Aq : \mathbb{N} \to \operatorname{Set}\left(S\right)), (\operatorname{AsymptoticallyStrictlyDecreasing}\left(Aq\right)) \land ((\operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}) \mapsto Aq\left(q\right)\right) = A) \land (\operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}) \mapsto \operatorname{sumset}\left(Aq\left(q\right), h\right)\right) = \operatorname{sumset}\left(A, h\right)))))))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.claim` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Intersections of sumsets in additive number theory*. DOI: [10.1017/S0004972726101270](https://doi.org/10.1017/S0004972726101270). URL: <https://arxiv.org/abs/2512.23574v3>.

*Commentary.*

Problem 2 (arXiv:2512.23574v3, p. 6) asks: “Let A be a subset of the infinite abelian semigroup S such that A is a nonbasis of order h but not a maximal nonbasis of order h for S. Does there exist an asymptotically strictly decreasing sequence (A_q)_{q=1}^∞ of subsets of S such that A = ⋂_{q=1}^∞ A_q and hA = ⋂_{q=1}^∞ hA_q? In particular, consider this problem for S = ℤ.” Section 2 (p. 5) states: “A subset A of S is a maximal nonbasis of order h for S if A is not a basis of order h for S but every proper superset of A is a basis of order h for S.” This condition is inlined in the assertion; the private proof uses Mathlib Maximal through Set.maximal_iff_forall_ssuperset. S ranges over infinite additive commutative semigroups, h over natural numbers with 1 ≤ h, and A over all subsets. Both intersections range over every nonnegative integer q. The sumset equality is written with the intersection on the left.

**Theorem 1.5 (A negative answer).**

$$\neg (\forall (S : \operatorname{Type}), [\operatorname{AddCommSemigroup}\left(S\right)] [\operatorname{Infinite}\left(S\right)] \forall (h : \mathbb{N}), \forall (A : \operatorname{Set}\left(S\right)), (1 \le h) \Rightarrow ((\neg (\operatorname{IsBasis}\left(h, A\right))) \Rightarrow ((\neg ((\neg (\operatorname{IsBasis}\left(h, A\right))) \land (\forall (B : \operatorname{Set}\left(S\right)), (A \subset B) \Rightarrow (\operatorname{IsBasis}\left(h, B\right))))) \Rightarrow (\exists (Aq : \mathbb{N} \to \operatorname{Set}\left(S\right)), (\operatorname{AsymptoticallyStrictlyDecreasing}\left(Aq\right)) \land ((\operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}) \mapsto Aq\left(q\right)\right) = A) \land (\operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}) \mapsto \operatorname{sumset}\left(Aq\left(q\right), h\right)\right) = \operatorname{sumset}\left(A, h\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.result` (`✓ std3`). ∎

*Resolves.* `Problems/nathanson-2025-sumset-intersection-nonmaximal` (refuted) by `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nathanson-2025-sumset-intersection-nonmaximal","declaration_gid":"D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Intersections of sumsets in additive number theory*. DOI: [10.1017/S0004972726101270](https://doi.org/10.1017/S0004972726101270). URL: <https://arxiv.org/abs/2512.23574v3>.

*Commentary.*

Take S = ℤ, h = 2 and A = {n : ℤ | Even n ∧ n ≠ 2}. This is a nonbasis, and its proper superset of all even integers remains a nonbasis. In a decreasing family with this intersection and arbitrarily late unequal steps, every stage has infinitely many elements outside A. Removing the possible element 2 leaves infinitely many odd elements. For an odd integer n, choose such an odd element b different from n − 2; then n − b belongs to A and n = (n − b) + b belongs to the two-fold sumset of that stage. Thus 1 belongs to every stage's two-fold sumset and does not belong to A + A. This single instance refutes the universal assertion; no assertion about all finite punctures or all orders h ≥ 2 is needed.

## References

- Truth anchor: `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.AsymptoticallyStrictlyDecreasing`
- Truth anchor: `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.IsBasis`
- Truth anchor: `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.claim`
- Truth anchor: `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.result`
- Truth anchor: `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.sumset`
