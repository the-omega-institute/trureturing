# Polyploid Allele Complementarity

## Abstract

Mixed polyploid genotypes obstruct Boolean allele complementarity.

**Theorem 1.1 (Allele events overlap exactly beyond haploidy).**

$$\begin{gathered}(\forall p: Nat, 2 \leq p \Rightarrow \operatorname{Nonempty}\left(\operatorname{intersection}\left(\{g: \operatorname{Fin}\left(p\right) \to Bool \mid \exists i: \operatorname{Fin}\left(p\right), \operatorname{apply}\left(g, i\right) = false\}, \{g: \operatorname{Fin}\left(p\right) \to Bool \mid \exists i: \operatorname{Fin}\left(p\right), \operatorname{apply}\left(g, i\right) = true\}\right)\right)) \land\\{}(\forall p: Nat, 1 \leq p \Rightarrow (\{g: \operatorname{Fin}\left(p\right) \to Bool \mid \exists i: \operatorname{Fin}\left(p\right), \operatorname{apply}\left(g, i\right) = true\} = \operatorname{complement}\left(\{g: \operatorname{Fin}\left(p\right) \to Bool \mid \exists i: \operatorname{Fin}\left(p\right), \operatorname{apply}\left(g, i\right) = false\}\right) \iff p = 1)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/PolyploidAlleleComplementarity.polyploid_allele_events_overlap_and_haploid_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A biallelic p-copy genotype is a function from Fin(p) to Bool. For p at least two, an explicit mixed genotype has one false locus and one true locus, so both allele-presence events occur.

For every nonempty genotype carrier, the true-allele event is the set complement of the false-allele event exactly when p equals one. At higher ploidy the same mixed genotype prevents equality.

The predicates and their carrier are displayed directly; no genotype event is defined in terms of the claimed intersection or complement relation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/PolyploidAlleleComplementarity.polyploid_allele_events_overlap_and_haploid_complement`
