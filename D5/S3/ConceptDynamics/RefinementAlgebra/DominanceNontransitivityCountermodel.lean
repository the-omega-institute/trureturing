/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/DominanceNontransitivityCountermodel
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/DominanceNontransitivityCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three unordered diploid genotypes witness cyclic, nontransitive dominance. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2

/- Library-search audit trail (2026-08-27):
   * The source defines diploid genotypes as unordered multisets. Pinned
     Mathlib's `Sym2` is the exact canonical carrier and is used directly.
   * Exact current-tree searches found the canonical `Concept` readout type,
     but no genotype phenotype table or nontransitive dominance theorem.
   * Pinned-Mathlib searches found `Sym2.lift` and `Sym2.lift_mk`, which
     construct and compute the symmetric phenotype without a quotient fork.
   * No new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.DominanceNontransitivityCountermodel

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open scoped Sym2

/-- On three alleles, the source phenotype table gives complete-dominance
edges a-to-b and b-to-d but no a-to-d edge. The same table has the d-to-a
edge, so its dominance graph contains a directed cycle. -/
theorem complete_dominance_not_transitive :
    ∃ a b d : Fin 3,
      ∃ phenotype : Concept (Sym2 (Fin 3)) Real,
        a ≠ b ∧ b ≠ d ∧ a ≠ d ∧
        phenotype s(a, a) = 0 ∧ phenotype s(a, b) = 0 ∧
        phenotype s(b, b) = 1 ∧ phenotype s(b, d) = 1 ∧
        phenotype s(d, d) = 2 ∧ phenotype s(a, d) = 2 ∧
        (Setoid.ker phenotype s(a, a) s(a, b) ∧
          ¬ Setoid.ker phenotype s(a, b) s(b, b)) ∧
        (Setoid.ker phenotype s(b, b) s(b, d) ∧
          ¬ Setoid.ker phenotype s(b, d) s(d, d)) ∧
        ¬ (Setoid.ker phenotype s(a, a) s(a, d) ∧
          ¬ Setoid.ker phenotype s(a, d) s(d, d)) ∧
        (Setoid.ker phenotype s(d, d) s(d, a) ∧
          ¬ Setoid.ker phenotype s(d, a) s(a, a)) := by
  let label : Sym2 (Fin 3) → Nat :=
    Sym2.lift ⟨fun i j =>
      if i.val + j.val = 2 ∧ i ≠ j then 2 else Nat.min i.val j.val, by
        intro i j
        change (if i.val + j.val = 2 ∧ i ≠ j then 2 else Nat.min i.val j.val) =
          (if j.val + i.val = 2 ∧ j ≠ i then 2 else Nat.min j.val i.val)
        simp only [Nat.add_comm, ne_comm, Nat.min_comm]⟩
  let phenotype : Concept (Sym2 (Fin 3)) Real := fun genotype => label genotype
  refine ⟨0, 1, 2, phenotype, by decide, by decide, by decide, ?_⟩
  norm_num [phenotype, label, Setoid.ker]
  constructor <;> decide

#print axioms complete_dominance_not_transitive

end D5.S3.ConceptDynamics.RefinementAlgebra.DominanceNontransitivityCountermodel
