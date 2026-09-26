import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

namespace Reg.Support.LegacyContextObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open LeanInformationAudit

/-- A singleton output cannot support a Law-changing intervention in that slot,
regardless of the chosen Law or of the other slots. -/
theorem subsingleton_slot_obstruction (A : PrimitiveLawArena)
    (i : A.signature.Index) [Subsingleton (A.signature.Output i)] :
    ¬ FiniteSlotSensitivity A := by
  rintro ⟨sensitive, _⟩
  obtain ⟨r, r', fixed, anchors, flip⟩ := sensitive i
  have readouts : r.readout = r'.readout := by
    funext j x
    by_cases h : j = i
    · subst j
      exact Subsingleton.elim _ _
    · exact congrFun (fixed j h) x
  have same : r = r' := by
    cases r
    cases r'
    cases readouts
    cases funext anchors
    rfl
  subst r'
  by_cases h : A.Law r
  · exact flip.mp h h
  · exact h (flip.mpr h)

/-- Both historical context registrations use this exact, unchanged arena. -/
theorem context_sensitivity_impossible : ¬ FiniteSlotSensitivity contextArena :=
  @subsingleton_slot_obstruction contextArena ContextReadout.text
    (inferInstanceAs (Subsingleton Unit))

theorem context_text_constant (r : PrimitiveRealization contextSignature)
    (x y : contextArena.toArena.State) : r.readout .text x = r.readout .text y :=
  @Subsingleton.elim Unit inferInstance _ _

theorem context_rule_constant (r : PrimitiveRealization contextSignature)
    (x y : contextArena.toArena.State) :
    r.readout .interpretationRule x = r.readout .interpretationRule y :=
  @Subsingleton.elim Unit inferInstance _ _

#print axioms context_sensitivity_impossible
#print axioms context_text_constant
#print axioms context_rule_constant
end Reg.Support.LegacyContextObstruction
