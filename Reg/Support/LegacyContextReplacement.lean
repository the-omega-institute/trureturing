import Reg.Support.LegacySpectrum
import Reg.Support.LegacyContextCausalCodes
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import Reg.Support.LegacyContextObstruction

namespace Reg.Support.LegacyContextReplacement
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open RegistrationTemplates LeanInformationAudit
open Reg.Support.LegacyContextCausalCodes (contextCode contextDecode)
attribute [local instance] contextDecidableEq

/-- All eight original contexts, with the two singleton fields reconstructed. -/
abbrev ContextData := Bool × Bool × Bool

def contextEquiv : BinaryInterpretationContext ≃ ContextData where
  toFun c := (c.readerAdmission, c.background, c.evaluationGoal)
  invFun bits := ⟨(), bits.1, bits.2.1, bits.2.2, ()⟩
  left_inv := by rintro ⟨⟨⟩, a, b, c, ⟨⟩⟩; rfl
  right_inv := by rintro ⟨a, b, c⟩; rfl

def objectArena : Arena := Arena.ofFintype ContextData

/-- The complete eight-clause source law. Text and rule are structural Unit
fields, rather than falsely sensitive primitive slots. The one nonconstant
readout is the complete context data, including all three meaningful fields. -/
def lawArena : PrimitiveLawArena where
  toArena := objectArena
  signature := cutSignature ContextData (Fin 8)
  Law r :=
    let baseline := contextEquiv.symm (contextDecode (r.readout () (false, false, false)))
    let alternate := contextEquiv.symm (contextDecode (r.readout () (true, true, true)))
    baseline.text = alternate.text ∧
      baseline.interpretationRule = alternate.interpretationRule ∧
      baseline.readerAdmission ≠ alternate.readerAdmission ∧
      baseline.background ≠ alternate.background ∧
      baseline.evaluationGoal ≠ alternate.evaluationGoal ∧
      IsBinaryFixedMeaning baseline (false, false, false) ∧
      IsBinaryFixedMeaning alternate (true, true, true) ∧
      (false, false, false) ≠ (true, true, true)

def domainArena : ObjectDomainArena where
  toPrimitiveLawArena := lawArena
  Domain := BinaryInterpretationContext

def actual := cutRealization (fun x : ContextData => contextCode x)

theorem bridge : LegacyPrimitiveRealization lawArena
    (baselineContext.text = alternateContext.text ∧
      baselineContext.interpretationRule = alternateContext.interpretationRule ∧
      baselineContext.readerAdmission ≠ alternateContext.readerAdmission ∧
      baselineContext.background ≠ alternateContext.background ∧
      baselineContext.evaluationGoal ≠ alternateContext.evaluationGoal ∧
      IsBinaryFixedMeaning baselineContext (false, false, false) ∧
      IsBinaryFixedMeaning alternateContext (true, true, true) ∧
      (false, false, false) ≠ (true, true, true)) actual := ⟨Iff.rfl⟩

def constant := cutRealization (fun _ : ContextData => contextCode (false, false, false))

theorem constant_rejected : ¬ lawArena.Law constant := by
  intro h
  exact h.2.2.1 rfl

theorem variation : lawArena.Law actual ∧ ¬ lawArena.Law constant :=
  ⟨bridge.equivalence.mp context_parameters_can_select_distinct_fixed_points,
    constant_rejected⟩

theorem sensitivity : FiniteSlotSensitivity lawArena := by
  constructor
  · intro i
    refine ⟨actual, constant, ?_, ?_, ?_⟩
    · intro j different
      exact (different (@Subsingleton.elim Unit inferInstance _ _)).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => constant_rejected, fun _ => variation.1⟩
  · intro i
    exact Fin.elim0 i

theorem dependence : ∀ i : Unit, ∃ x y : ContextData,
    actual.readout i x ≠ actual.readout i y := by
  intro i
  cases i
  exact ⟨(false, false, false), (true, true, true), by
    change (0 : Fin 8) ≠ 7
    decide⟩

/-- The replacement retains the complete observational equivalence relation,
not only the two named witnesses. Singleton slots carry no additional relation. -/
theorem kernel_transport (x y : BinaryInterpretationContext) :
    actual.toPrimitiveBundle.agrees (contextEquiv x) (contextEquiv y) ↔
      _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations.contextRealization.toPrimitiveBundle.agrees x y := by
  rcases x with ⟨⟨⟩, a, b, c, ⟨⟩⟩
  rcases y with ⟨⟨⟩, d, e, f, ⟨⟩⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

#print axioms bridge
#print axioms sensitivity
#print axioms dependence
#print axioms kernel_transport
end Reg.Support.LegacyContextReplacement
