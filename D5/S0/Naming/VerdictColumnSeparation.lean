/- GID: D5/S0/Naming/VerdictColumnSeparation
   generality: G
   mirror-B: D5/B/S0/Naming/VerdictColumnSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A population extension can separate previously equal verdict columns. -/

import Mathlib

namespace D5.S0.Naming.VerdictColumnSeparation

/-- Two distinct tests whose verdict columns agree on the current implementation
population can be separated after adjoining one implementation. -/
theorem verdict_columns_can_split
    {Implementation Test Verdict : Type*} [Nontrivial Verdict]
    (r : Implementation -> Test -> Verdict) {t1 t2 : Test} (ht : Not (t1 = t2))
    (_same_column : forall implementation, r implementation t1 = r implementation t2) :
    Exists fun extended : Option Implementation -> Test -> Verdict =>
      (forall implementation, extended (some implementation) = r implementation) /\
        Not (extended none t1 = extended none t2) := by
  classical
  obtain ⟨pass, fail, hne⟩ := exists_pair_ne Verdict
  let extended : Option Implementation -> Test -> Verdict := fun implementation test =>
    match implementation with
    | some old => r old test
    | none => if test = t1 then pass else fail
  refine ⟨extended, ?_, ?_⟩
  · intro implementation
    rfl
  · have ht' : Not (t2 = t1) := fun h => ht h.symm
    simp [extended, ht', hne]

end D5.S0.Naming.VerdictColumnSeparation
