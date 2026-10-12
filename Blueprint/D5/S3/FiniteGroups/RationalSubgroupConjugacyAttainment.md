# Rational Attainment of Subgroup Conjugacy Ratios

## Abstract

Every rational strictly between zero and one is the subgroup-conjugacy ratio of an actual finite group.

**Theorem 1.1 (The universal attainment theorem).**

$$\forall a \in Integers,\; \forall b \in Integers,\; 1\le a \to \left(a<b \to \left(\exists W \in FiniteGroup\left(\right),\; b*integerCast\left(classCount\left(Carrier\left(W\right)\right)\right)=a*integerCast\left(latticeCount\left(Carrier\left(W\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment.rational_attainment` (`✓ std3`). ∎

*Resolves.* `Problems/lazorec-tarnauceanu-2025-rational-subgroup-conjugacy-attainment` (proved) by `D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment.rational_attainment`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lazorec-tarnauceanu-2025-rational-subgroup-conjugacy-attainment","declaration_gid":"D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment.rational_attainment","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mihai-Silviu Lazorec and Marius Tărnăuceanu (2025). *On the number of conjugacy classes of subgroups of a finite group*. DOI: [10.48550/arXiv.2508.14267](https://doi.org/10.48550/arXiv.2508.14267). URL: <https://arxiv.org/html/2508.14267v2>.

*Commentary.*

The statement answers Problem 4.1 of Lazorec and Tărnăuceanu, https://arxiv.org/html/2508.14267v2#S4, affirmatively. Here latticeCount G is the cardinality of the whole subgroup lattice Subgroup G, and classCount G is the cardinality of its quotient by inner conjugation. FiniteGroup supplies an actual carrier, group structure, and finiteness proof. For every integer pair 1 ≤ a < b the witness satisfies b classCount = a latticeCount. Both counts are positive: the lattice contains the trivial subgroup and its conjugacy quotient contains that subgroup's orbit. Thus the equation is equivalent to the exact rational equality in the question. No nilpotence, supersolvability, supplied action, subgroup-count formula, coprime family, or literature theorem is an assumption of the conclusion.

For a positive natural t and an already constructed finite group W, choose primes q and p with max(4,card W) < q < p and q dividing p−1. The prime supplier uses the infinitude of primes and the pinned theorem Nat.exists_prime_gt_modEq_one. Since p is odd, define n = t((p−1)/2) and s = n−1. The inequalities p > 4 and t > 0 give n ≥ 2 and s > 0. Construct the actual semidirect product V = Cyclic p semidirect Cyclic (q^s), with generator action of exact order q.

CyclicPrimePowerAction.split_counts gives classCount V = 2s+2 = 2n and latticeCount V = 2s+p+1 = 2n+p−1. The integer identity 2n = t(p−1) therefore gives ratio V = t/(t+1). SemidirectProduct.equivProd gives card V = p q^s. Both primes exceed card W, so neither divides that positive cardinality; hence card W and card V are coprime. The coprime-product theorem applies to the actual direct product W × V, including its whole subgroup lattice and its inner-conjugacy quotient.

Induct on m to construct an actual finite group with positive latticeCount and ratio a/(a+m), for every positive natural a. At m=0 take the trivial group, whose lattice and quotient each have one element. For the step put t=a+m, construct the fresh factor V above, and multiply the ratios: (a/t)(t/(t+1)) = a/(t+1). Choosing each factor above the order of the accumulated product establishes the required coprimality at every step, without a presupposed prime family.

For the original integers use their nonnegative natural representatives and m=b−a. The induction yields ratio a/b with positive latticeCount. Cross-multiplication in the rationals and exact integer casting give the displayed equation. The full classification and count proofs are kernel dependencies of this construction. Proposition 2.2(ii) already states the factor counts, and Section 1 already states coprime ratio multiplicativity. The additional construction supplies consecutive-ratio factors with orders coprime to any accumulated finite group, completing the sufficient route proposed in Problem 4.1. The conclusion concerns that universal question; it makes no claim about the paper's other open problems or mathematical priority.

## References

- Truth anchor: `D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment.rational_attainment`
- Dependency: [D5/S3/FiniteGroups/CyclicPrimePowerAction](CyclicPrimePowerAction.md)
