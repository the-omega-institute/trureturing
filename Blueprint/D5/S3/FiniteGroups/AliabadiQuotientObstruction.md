# Abelianization does not characterize right quotient multisets

## Abstract

Every finite nonabelian group has a multiset satisfying the abelianization obstruction which is not a multiset of right quotients of two bijective enumerations.

**Theorem 1.1 (A nonidentity element of the commutator subgroup suffices).**

$$\forall G \in Typeu,\; \forall group \in \operatorname{Group}\left(G\right),\; \forall finite \in \operatorname{Fintype}\left(G\right),\; \forall hna \in \left(\neg \operatorname{IsMulCommutative}\left(G\right)\right),\; \exists A \in \operatorname{Multiset}\left(G\right),\; \operatorname{MultisetCard}\left(A\right) = \operatorname{FintypeCard}\left(G\right) \land \left(\operatorname{MultisetProd}\left(\operatorname{MultisetMap}\left(\operatorname{AbelianizationOf}\left(G\right), A\right)\right) = 1 \land \left(\neg \left(\exists b \in \operatorname{Fin}\left(\operatorname{FintypeCard}\left(G\right)\right) \to G,\; \exists c \in \operatorname{Fin}\left(\operatorname{FintypeCard}\left(G\right)\right) \to G,\; \operatorname{Bijective}\left(b\right) \land \left(\operatorname{Bijective}\left(c\right) \land A = \operatorname{RightQuotientMultiset}\left(b, c\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AliabadiQuotientObstruction.exists_obstructed_multiset` (`✓ std3`). ∎

*Resolves.* `Problems/aliabadi-2605-16478v2-problem-7-6` (proved) by `D5/S3/FiniteGroups/AliabadiQuotientObstruction.exists_obstructed_multiset`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"aliabadi-2605-16478v2-problem-7-6","declaration_gid":"D5/S3/FiniteGroups/AliabadiQuotientObstruction.exists_obstructed_multiset","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohsen Aliabadi (2026). *A nonabelian twist on differences of bijections*. DOI: [10.61091/um128-18](https://doi.org/10.61091/um128-18). URL: <https://arxiv.org/html/2605.16478v2>.

*Commentary.*

Let G be any finite group with noncommutative multiplication, and put n=|G|. The canonical map pi is Abelianization.of from G to G/[G,G]. There exists a genuine multiset A of cardinality n, counted with multiplicity, for which the product of the pi-images is one, while no two bijective functions b,c from Fin n to G have A equal to the multiset of b(i) times the inverse of c(i). In the formula, RightQuotientMultiset(b,c) denotes the map of the univ multiset of Fin n under i mapped to b(i) times the inverse of c(i); MultisetMap and MultisetProd preserve all multiplicities. AbelianizationOf denotes exactly the canonical Abelianization.of. Fin n consists of 0 through n-1; adding one identifies this index set with 1 through n. A Fintype structure presents an arbitrary finite group and adds no group-theoretic assumption.

The commutator subgroup is nontrivial, since commutator_eq_bot_iff identifies its triviality with commutativity. Subgroup.nontrivial_iff_exists_ne_one supplies a nonidentity element a in it. Abelianization.ker_of proves pi(a)=1. Take A to contain a once and the identity n-1 times. A group is nonempty, so n is positive and the multiset has cardinality n. All entries have pi-image one, so their multiplicity-counted product in the abelian quotient is one.

Suppose b and c realize A. Regard both bijections as equivalences and form the permutation tau=c inverse composed with b on Fin n. Then tau(i) differs from i exactly when b(i) times the inverse of c(i) differs from one. Filter the asserted multiset equality by being different from the identity. The left side has cardinality one. Multiset.filter_map and Multiset.card_map identify the right side with the cardinality of tau.support. Equiv.Perm.card_support_ne_one rules out this value. The permutation and multiset bridge is proved within the argument, with no additional realization assumption.

Repeated identity entries are allowed. The construction imposes no solvability, parity, group-family or identity-free condition. Every ordering of A in G has product a, which differs from one; the product used in the theorem is exclusively in the abelianization. Thus the statement answers the literal Problem 7.6 and leaves the stronger product-one-ordering variant separate. The argument applies existing general results about commutators, multiset operations and permutation support; it does not assert a new general method or literature priority.

## References

- Truth anchor: `D5/S3/FiniteGroups/AliabadiQuotientObstruction.exists_obstructed_multiset`
