/- GID: D5/S0/Certificates/LRATUnsatisfiable
   generality: G
   mirror-B: D5/B/S0/Certificates/LRATUnsatisfiable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mathlib LRAT empty-clause proofs are exactly propositional unsatisfiability certificates. -/

import Mathlib.Tactic.Sat.FromLRAT

/- Library-search audit trail (2026-09-01):
   * Pinned Mathlib supplies the `lrat_proof` command and the kernel-level
     `Sat.Fmla.proof` semantics used by its generated proof terms.
   * Repository searches found no public bridge naming the empty-clause result
     as formula unsatisfiability.
   * This file introduces no second LRAT checker. It exposes the exact logical
     contract of the upstream checker for later certificate-carrying searches. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.LRATUnsatisfiable

/-- A propositional CNF formula is unsatisfiable when no valuation satisfies all
of its clauses. -/
def Unsatisfiable (formula : Sat.Fmla) : Prop :=
  forall valuation : Sat.Valuation,
    ¬Sat.Valuation.satisfies_fmla valuation formula

/-- Derivability of the empty clause, which is what Mathlib's LRAT checker
produces internally, is definitionally equivalent to unsatisfiability. -/
theorem empty_clause_proof_iff_unsatisfiable (formula : Sat.Fmla) :
    formula.proof [] <-> Unsatisfiable formula := by
  rfl

/-- A reusable wrapper for a kernel-checked LRAT refutation. -/
structure Refutation (formula : Sat.Fmla) : Prop where
  emptyClause : formula.proof []

/-- Every wrapped LRAT refutation excludes all satisfying valuations. -/
theorem Refutation.sound {formula : Sat.Fmla}
    (refutation : Refutation formula) :
    Unsatisfiable formula :=
  (empty_clause_proof_iff_unsatisfiable formula).mp refutation.emptyClause

/-- Unsatisfiability can be repackaged as the exact empty-clause interface
expected from an LRAT proof. -/
theorem refutation_iff_unsatisfiable (formula : Sat.Fmla) :
    Refutation formula <-> Unsatisfiable formula := by
  constructor
  · exact Refutation.sound
  · intro unsatisfiable
    exact ⟨(empty_clause_proof_iff_unsatisfiable formula).mpr unsatisfiable⟩

#print axioms empty_clause_proof_iff_unsatisfiable
#print axioms Refutation.sound

end D5.S0.Certificates.LRATUnsatisfiable
