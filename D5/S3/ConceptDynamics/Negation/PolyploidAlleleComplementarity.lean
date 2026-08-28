/- GID: D5/S3/ConceptDynamics/Negation/PolyploidAlleleComplementarity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Negation/PolyploidAlleleComplementarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mixed polyploid genotypes obstruct Boolean allele complementarity. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Negation.PolyploidAlleleComplementarity

/-- In a biallelic `p`-copy genotype, the two allele-presence events overlap
once `p >= 2`. For nonempty genotypes, those events are Boolean complements
exactly at haploidy. -/
theorem polyploid_allele_events_overlap_and_haploid_complement :
    (∀ p : Nat, 2 ≤ p →
      ({genotype : Fin p → Bool | ∃ locus, genotype locus = false} ∩
          {genotype : Fin p → Bool | ∃ locus, genotype locus = true}).Nonempty) ∧
      (∀ p : Nat, 1 ≤ p →
        ({genotype : Fin p → Bool | ∃ locus, genotype locus = true} =
            ({genotype : Fin p → Bool |
              ∃ locus, genotype locus = false})ᶜ ↔
          p = 1)) := by
  constructor
  · intro p twoLe
    let left : Fin p := ⟨0, by omega⟩
    let right : Fin p := ⟨1, by omega⟩
    let genotype : Fin p → Bool := fun locus => decide (locus = right)
    refine ⟨genotype, ⟨?_, ?_⟩⟩
    · refine ⟨left, ?_⟩
      simp [genotype, left, right]
    · exact ⟨right, by simp [genotype]⟩
  · intro p oneLe
    constructor
    · intro complementarity
      by_contra notHaploid
      have twoLe : 2 ≤ p := by omega
      let left : Fin p := ⟨0, by omega⟩
      let right : Fin p := ⟨1, by omega⟩
      let genotype : Fin p → Bool := fun locus => decide (locus = right)
      have alleleA : genotype ∈
          {candidate : Fin p → Bool | ∃ locus, candidate locus = false} := by
        exact ⟨left, by simp [genotype, left, right]⟩
      have alleleB : genotype ∈
          {candidate : Fin p → Bool | ∃ locus, candidate locus = true} := by
        exact ⟨right, by simp [genotype]⟩
      rw [complementarity] at alleleB
      exact alleleB alleleA
    · intro haploid
      subst p
      apply Set.ext
      intro genotype
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · rintro ⟨left, leftTrue⟩ ⟨right, rightFalse⟩
        have sameLocus : left = right := Subsingleton.elim _ _
        subst right
        simp [leftTrue] at rightFalse
      · intro noFalse
        refine ⟨0, ?_⟩
        cases value : genotype 0 with
        | false => exact False.elim (noFalse ⟨0, value⟩)
        | true => rfl

#print axioms polyploid_allele_events_overlap_and_haploid_complement

end D5.S3.ConceptDynamics.Negation.PolyploidAlleleComplementarity
