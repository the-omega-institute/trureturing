# Maximal-Index Multiplicity in Prime-Power Group Coset Partitions

## Abstract

Prime-power group coset partitions have p-divisible maximal-index multiplicity.

**Definition 1.1 (The largest subgroup index in a finite indexed family).**

$$\forall G \in Type,\; \operatorname{Group}\left(G\right) \Rightarrow \left(\forall r \in \mathbb{N}, H \in (\operatorname{Fin}\left(r\right) \to \operatorname{Subgroup}\left(G\right)),\; \operatorname{maximalIndex}\left(H\right) = \operatorname{Finset.univ.sup}\left(i \mapsto [G:H\left(i\right)]\right)\right)$$

*Formalization.* `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.maximalIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With {G : Type*} and [Group G], the Lean type is {r : Nat} -> (Fin r -> Subgroup G) -> Nat. It is defined exactly as maximalIndex H = Finset.univ.sup (fun i => (H i).index). When r is zero, Finset.univ is empty, so its natural-number supremum and maximalIndex H are zero.

**Definition 1.2 (The positions attaining the largest subgroup index).**

$$\forall G \in Type,\; \operatorname{Group}\left(G\right) \Rightarrow \left(\forall r \in \mathbb{N}, H \in (\operatorname{Fin}\left(r\right) \to \operatorname{Subgroup}\left(G\right)),\; \operatorname{maximalIndexPositions}\left(H\right) = \operatorname{Finset.univ.filter}\left(i \mapsto [G:H\left(i\right)] = \operatorname{maximalIndex}\left(H\right)\right)\right)$$

*Formalization.* `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.maximalIndexPositions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With {G : Type*} and [Group G], the Lean type is {r : Nat} -> (Fin r -> Subgroup G) -> Finset (Fin r). It is defined exactly as maximalIndexPositions H = Finset.univ.filter (fun i => (H i).index = maximalIndex H). When r is zero, Finset.univ is empty, so the filtered finset is empty.

**Theorem 1.3 (The maximal-index multiplicity is divisible by the underlying prime).**

$$\forall G \in Type,\; \left(\operatorname{Group}\left(G\right) \land \operatorname{Finite}\left(G\right)\right) \Rightarrow \left(\forall r \in \mathbb{N}, p \in \mathbb{N}, N \in \mathbb{N}, H \in (\operatorname{Fin}\left(r\right) \to \operatorname{Subgroup}\left(G\right)), g \in (\operatorname{Fin}\left(r\right) \to G),\; \left(2 \le r \land \left(\operatorname{Prime}\left(p\right) \land \left(\operatorname{NatCard}\left(G\right) = p^{N} \land \left(\left(\forall i \in \operatorname{Fin}\left(r\right), j \in \operatorname{Fin}\left(r\right),\; i \ne j \Rightarrow \operatorname{Disjoint}\left(\operatorname{leftCosetSet}\left(g\left(i\right), \operatorname{carrier}\left(H\left(i\right)\right)\right), \operatorname{leftCosetSet}\left(g\left(j\right), \operatorname{carrier}\left(H\left(j\right)\right)\right)\right)\right) \land \operatorname{iUnionLeftCosetSets}\left(g, H\right) = \operatorname{univ}\left(G\right)\right)\right)\right)\right) \Rightarrow p \mid \operatorname{card}\left(\{i \in \operatorname{Fin}\left(r\right) \mid [G:H\left(i\right)] = \max_{j \in \operatorname{Fin}\left(r\right)} [G:H\left(j\right)]\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.prime_dvd_card_maximalIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marc A. Berger; Alexander Felzenbaum; Aviezri Fraenkel (1986). *The Herzog-Schonheim Conjecture for Finite Nilpotent Groups*. DOI: [10.4153/CMB-1986-050-0](https://doi.org/10.4153/CMB-1986-050-0).

*Commentary.*

Let G be a finite group of order p^N, where p is prime, and let the r left-coset sets g_i H_i be pairwise disjoint and cover G, with r at least two. Here [G:H_i] is the subgroup index, d is literally the maximum of these indices, and the displayed set contains exactly the positions where [G:H_i] equals d. Then p divides the cardinality of that set.

The proof first counts the arbitrary disjoint left-coset cover as |G| = sum_i |H_i|. Because all subgroup indices divide the same prime power, each index divides d; cancelling |G|/d gives the natural-number identity d = sum_i d/[G:H_i]. Reduction modulo p makes a maximal ratio equal to one and every nonmaximal ratio equal to zero. A nontrivial partition forces p to divide d, so p divides the surviving maximal-position count. Every slash in this description denotes natural-number Euclidean division, not a field fraction.

Berger, Felzenbaum, and Fraenkel prove the qualitative repeated-index Herzog-Schonheim conclusion for finite nilpotent groups. The p-divisibility refinement asserted here is independently derived in this repository, so the paper is acknowledged rather than used as attestation for this stronger statement.

**Theorem 1.4 (At least p maximal positions yield two equal subgroup indices).**

$$\forall G \in Type,\; \left(\operatorname{Group}\left(G\right) \land \operatorname{Finite}\left(G\right)\right) \Rightarrow \left(\forall r \in \mathbb{N}, p \in \mathbb{N}, N \in \mathbb{N}, H \in (\operatorname{Fin}\left(r\right) \to \operatorname{Subgroup}\left(G\right)), g \in (\operatorname{Fin}\left(r\right) \to G),\; \left(2 \le r \land \left(\operatorname{Prime}\left(p\right) \land \left(\operatorname{NatCard}\left(G\right) = p^{N} \land \left(\left(\forall i \in \operatorname{Fin}\left(r\right), j \in \operatorname{Fin}\left(r\right),\; i \ne j \Rightarrow \operatorname{Disjoint}\left(\operatorname{leftCosetSet}\left(g\left(i\right), \operatorname{carrier}\left(H\left(i\right)\right)\right), \operatorname{leftCosetSet}\left(g\left(j\right), \operatorname{carrier}\left(H\left(j\right)\right)\right)\right)\right) \land \operatorname{iUnionLeftCosetSets}\left(g, H\right) = \operatorname{univ}\left(G\right)\right)\right)\right)\right) \Rightarrow \left(p \le \operatorname{card}\left(\{i \in \operatorname{Fin}\left(r\right) \mid [G:H\left(i\right)] = \max_{j \in \operatorname{Fin}\left(r\right)} [G:H\left(j\right)]\}\right) \land \left(\exists i \in \operatorname{Fin}\left(r\right), j \in \operatorname{Fin}\left(r\right),\; i \ne j \land [G:H\left(i\right)] = [G:H\left(j\right)]\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.prime_le_card_maximalIndex` (`✓ std3`). ∎

*Citation.* Marc A. Berger; Alexander Felzenbaum; Aviezri Fraenkel (1986). *The Herzog-Schonheim Conjecture for Finite Nilpotent Groups*. DOI: [10.4153/CMB-1986-050-0](https://doi.org/10.4153/CMB-1986-050-0).

*Commentary.*

Under exactly the same hypotheses and with exactly the same literal maximum d, the maximal-index position set has cardinality at least p, and there are distinct positions i and j whose subgroup indices are equal. Both clauses form one public theorem, matching the whole companion statement.

This declaration is bind-only: divisibility from the preceding theorem and positivity of the maximal-position set give the lower bound; primality gives p at least two, and the finite-cardinality witness then supplies distinct positions. Its dependency direction is the consumer edge 9.20 to prerequisite 9.19.

The cited paper proves the Herzog-Schonheim repeated-index conclusion for all finite nilpotent groups. The displayed lower bound is the quantitative p-group form obtained here from the stronger preceding divisibility theorem.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.maximalIndex`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.maximalIndexPositions`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.prime_dvd_card_maximalIndex`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.prime_le_card_maximalIndex`
