/- GID: D5/S3/ConceptDynamics/Epistemic/EpistemicChangeTrichotomy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/EpistemicChangeTrichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-world conclusion changes expose an admission, evidence, or inference change. -/

/- Library-search audit trail (2026-08-22):
   * Repository searches found no theorem over exactly the source triple of an
     admission predicate, evidence concept, and inference rule.
   * `CompleteInputDeterminism` is adjacent but uses an eight-component structure,
     so applying it would change the source carrier instead of giving a thin wrapper.
   * Pinned Mathlib provides `Relator.RightUnique` for relational determinism, but
     the source constructs conclusions by a function and needs no relational layer.
   * Core equality substitution supplies the proof. Loogle and LeanSearch executables
     were absent from PATH, and no packaged exact trichotomy was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.EpistemicChangeTrichotomy

/-- When the world is fixed and conclusions are evaluated deterministically from
the source primitives, unequal conclusions expose a change in the admission
predicate, evidence concept, or inference rule. These three public alternatives
are respectively the admissible-world, evidence-distinction, and rule audit. -/
theorem changed_conclusion_exposes_epistemic_component
    {X Evidence EpistemicInput Belief Conclusion : Type _}
    (leftWorld rightWorld : X)
    (leftAdmission rightAdmission : X -> Prop)
    (leftEvidence rightEvidence : X -> Evidence)
    (leftInference rightInference : EpistemicInput -> Belief)
    (conclude :
      (X -> Prop) -> (X -> Evidence) ->
        (EpistemicInput -> Belief) -> X -> Conclusion)
    (worldUnchanged : leftWorld = rightWorld)
    (conclusionChanged :
      conclude leftAdmission leftEvidence leftInference leftWorld ≠
        conclude rightAdmission rightEvidence rightInference rightWorld) :
    leftAdmission ≠ rightAdmission ∨
      leftEvidence ≠ rightEvidence ∨
      leftInference ≠ rightInference := by
  classical
  by_cases admissionChanged : leftAdmission ≠ rightAdmission
  · exact Or.inl admissionChanged
  · by_cases evidenceChanged : leftEvidence ≠ rightEvidence
    · exact Or.inr (Or.inl evidenceChanged)
    · by_cases inferenceChanged : leftInference ≠ rightInference
      · exact Or.inr (Or.inr inferenceChanged)
      · have admissionUnchanged : leftAdmission = rightAdmission :=
          Classical.not_not.mp admissionChanged
        have evidenceUnchanged : leftEvidence = rightEvidence :=
          Classical.not_not.mp evidenceChanged
        have inferenceUnchanged : leftInference = rightInference :=
          Classical.not_not.mp inferenceChanged
        subst rightWorld
        subst rightAdmission
        subst rightEvidence
        subst rightInference
        exact False.elim (conclusionChanged rfl)

/-- The fixed-world and changed-conclusion premises have a concrete model built
from the source primitives. -/
example :
    let leftAdmission : Bool -> Prop := fun world => world = true
    let rightAdmission : Bool -> Prop := fun _ => False
    let evidence : Bool -> Bool := id
    let inference : Unit -> Bool := fun _ => false
    let conclude := fun (admission : Bool -> Prop) (_ : Bool -> Bool)
      (_ : Unit -> Bool) (world : Bool) => admission world
    conclude leftAdmission evidence inference true ≠
        conclude rightAdmission evidence inference true ∧
      (leftAdmission ≠ rightAdmission ∨ evidence ≠ evidence ∨ inference ≠ inference) := by
  dsimp
  constructor
  · simp
  · left
    intro admissionUnchanged
    have atTrue := congrFun admissionUnchanged true
    simp at atTrue

/-- With all three components unchanged, the public trichotomy is false; hence
it is not an unconditional logical identity detached from source change. -/
example :
    let admission : Bool -> Prop := fun _ => True
    let evidence : Bool -> Bool := id
    let inference : Unit -> Bool := fun _ => false
    ¬ (admission ≠ admission ∨ evidence ≠ evidence ∨ inference ≠ inference) := by
  simp

#print axioms changed_conclusion_exposes_epistemic_component

end D5.S3.ConceptDynamics.Epistemic.EpistemicChangeTrichotomy
