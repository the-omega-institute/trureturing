/- GID: D5/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrationTemplates
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: State-dependent disjunction templates retain admissibility hypotheses and expose both Boolean alternatives as cut readouts. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.DisjunctionRegistrationTemplates

open RegistrationTemplates LeanInformationAudit

abbrev disjunctionSignature (X : Type) : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def disjunctionRealization {X : Type} (left right : X → Prop)
    [DecidablePred left] [DecidablePred right] :
    PrimitiveRealization (disjunctionSignature X) where
  readout := fun | false => fun x => decide (left x)
                 | true => fun x => decide (right x)
  anchor := Fin.elim0

def disjunctionArena (A : Arena) (admissible : A.State → Prop)
    [DecidablePred admissible] : PrimitiveLawArena where
  toArena := A
  signature := disjunctionSignature A.State
  Law r := ∀ x, admissible x →
    (r.readout false x = true ∨ r.readout true x = true)

theorem disjunctionLegacy (A : Arena) (admissible left right : A.State → Prop)
    [DecidablePred admissible] [DecidablePred left] [DecidablePred right] :
    LegacyPrimitiveRealization (disjunctionArena A admissible)
      (∀ x, admissible x → left x ∨ right x)
      (@disjunctionRealization A.State left right (inferInstance) (inferInstance)) := by
  refine ⟨?_⟩
  simp [disjunctionArena, disjunctionRealization]

theorem disjunction_sensitivity (A : Arena) (admissible : A.State → Prop)
    [DecidablePred admissible] (x : A.State) (hx : admissible x) :
    FiniteSlotSensitivity (disjunctionArena A admissible) := by
  classical
  constructor
  · intro i
    cases i with
    | false =>
        let q : A.State → Prop := fun y => y ≠ x
        refine ⟨disjunctionRealization (fun _ => True) q,
          disjunctionRealization (fun _ => False) q, ?_, ?_, ?_⟩
        · intro j hj; cases j
          · exact (hj rfl).elim
          · rfl
        · intro j; exact Fin.elim0 j
        · constructor
          · intro _ h'
            change ∀ y, admissible y → _ at h'
            have hbad := h' x hx
            simp [disjunctionRealization, q] at hbad
          · intro _
            change ∀ y, admissible y → _
            intro y hy
            by_cases hxy : y = x
            · subst y; exact Or.inl (by simp [disjunctionRealization])
            · exact Or.inr (by simp [disjunctionRealization, q, hxy])
    | true =>
        let p : A.State → Prop := fun y => y ≠ x
        refine ⟨disjunctionRealization p (fun _ => True),
          disjunctionRealization p (fun _ => False), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · rfl
          · exact (hj rfl).elim
        · intro j; exact Fin.elim0 j
        · constructor
          · intro _ h'
            change ∀ y, admissible y → _ at h'
            have hbad := h' x hx
            simp [disjunctionRealization, p] at hbad
          · intro _
            change ∀ y, admissible y → _
            intro y hy
            by_cases hxy : y = x
            · exact Or.inr (by simp [disjunctionRealization])
            · exact Or.inl (by simp [disjunctionRealization, p, hxy])
  · intro i; exact Fin.elim0 i

#print axioms disjunctionLegacy
#print axioms disjunction_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.DisjunctionRegistrationTemplates
