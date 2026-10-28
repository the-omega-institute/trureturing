import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure
import Reg.Support.DependentFamily

/-! Full-telescope audit attempt for the repeated-reference Bochner event norm. -/

open scoped ComplexOrder InnerProductSpace BigOperators
open TraceClassFiniteBlocks MeasureTheory Set
open _root_.D5.S3.Quantum.Fibers
open OriginalReferenceKraus OriginalReferenceOutputMeasure OriginalRepeatedPrefix
open OriginalControlMarkedJump OriginalMarkedConcatenation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => (-1:ℝ)) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool)
    (i : Fin 5) (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1),
    let k := if e then B.early n hn else B.late n hn
    let F := modeOutput B.c B.a k i rho hpos
    (∀ t : ℝ, (F t).1 =
      (referenceTensorJump B.c B.a (k t) (survival B.c k t) (jumpRate B.c k t) i).comp
        (rho.1.comp
          (referenceTensorJump B.c B.a (k t) (survival B.c k t) (jumpRate B.c k t) i).adjoint)) ∧
    IntegrableOn F (Ioc 0 2) ∧
    ∀ E : Set ℝ, MeasurableSet E →
      let D := (Ioc 0 2) ∩ E
      IntegrableOn F D ∧ 0 ≤ (∫ t in D, F t).1 ∧
      (∫ t in D, F t) =
        ((∫ t in D, modeCoefficient B.c B.a k i t : ℝ) : ℂ) •
          TraceClass.ofOperator (compression rho.1 i)
            (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i) ∧
      R.readout ⟨()⟩ () ‖∫ t in D, F t‖ = ∫ t in D, ‖F t‖

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

private def band : Band := ⟨1/5,3/10,2/5,by norm_num,by norm_num,by norm_num,by norm_num⟩

private theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ B n hn e i rho hpos
  exact repeated_failure_event B n hn e i rho hpos

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hz : 0 ≤ (0 : TraceClass (Blocks (Fin 5)
      (EuclideanSpace ℂ (ULift.{u} Unit)))).1 := by
    change (0 : Blocks (Fin 5) (EuclideanSpace ℂ (ULift.{u} Unit)) →L[ℂ]
      Blocks (Fin 5) (EuclideanSpace ℂ (ULift.{u} Unit))) ≤ 0
    exact le_rfl
  have hh := (h (H := EuclideanSpace ℂ (ULift.{u} Unit)) band 1
    (by norm_num) false 0 0 hz).2.2
    ∅ MeasurableSet.empty
  have he := hh.2.2.2
  norm_num [rejected, realize] at he

def family : Registration arena.{u} (type_of% (@repeated_failure_event.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_failure_event.{u})
    (type_of% (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure
