import Reg.Support.LegacyFiniteTransport
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign

namespace Reg.Support.LegacyStaticDesign
open LeanInformationAudit
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open Reg.Support.LegacyFiniteTransport
open RegistrationTemplates

def readouts : Bool → Three → Bool := fun experiment model =>
  Bool.rec (Sum.rec (fun b => b) (fun _ => false) model)
    (Sum.rec (fun _ => false) (fun _ => true) model) experiment

def actual := binaryFamilyRealization (fun i s => readouts i s)

def toOriginal (r : PrimitiveRealization (binaryFamilySignature Three Bool)) :
    PrimitiveRealization staticSignature :=
  ⟨fun i m => r.readout (decide (i = 1)) (threeEquiv.symm m), Fin.elim0⟩

def arena : ObjectDomainArena where
  Domain := Fin 3
  toArena := Arena.ofFintype Three
  signature := binaryFamilySignature Three Bool
  Law r := staticExactExperimentArena.Law (toOriginal r)

theorem nondegenerate : arena.toArena.Nondegenerate := by decide +kernel

def enumeration : Arena.StateEnumeration arena.toArena where
  states := ([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three)
  nodup := by
    change (([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three) : List Three).Nodup
    decide +kernel
  complete := by
    change (([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three) : List Three).toFinset = Finset.univ
    decide +kernel

theorem actual_correspondence : toOriginal actual = staticExactExperimentRealization := by
  apply realization_ext
  · funext i m
    fin_cases i <;> fin_cases m <;> rfl
  · funext i; exact Fin.elim0 i

theorem bridge : LegacyPrimitiveRealization arena.toPrimitiveLawArena StaticExactDesignStatement actual := by
  refine ⟨?_⟩
  change _ ↔ staticExactExperimentArena.Law (toOriginal actual)
  rw [actual_correspondence]
  exact static_exact_design_realization.equivalence

theorem actual_law : arena.Law actual := bridge.equivalence.mp static_exact_design

def eraseSlot (i : Bool) : PrimitiveRealization (binaryFamilySignature Three Bool) :=
  ⟨fun (j : Bool) (s : Three) => if j = i then false else actual.readout j s, Fin.elim0⟩

theorem erased_rejected (i : Bool) : ¬ arena.Law (eraseSlot i) := by
  intro h
  have inj := h.2.1
  cases i
  · have collision : (0 : Fin 3) = 1 := inj (by funext b; cases b <;> rfl)
    exact (by decide : (0 : Fin 3) ≠ 1) collision
  · have collision : (0 : Fin 3) = 2 := inj (by funext b; cases b <;> rfl)
    exact (by decide : (0 : Fin 3) ≠ 2) collision

theorem actual_sensitivity (i : Bool) : ∃ bad : PrimitiveRealization arena.signature,
    (∀ j, j ≠ i → actual.readout j = bad.readout j) ∧
    actual.anchor = bad.anchor ∧ ¬ arena.Law bad := by
  refine ⟨eraseSlot i, ?_, rfl, erased_rejected i⟩
  intro j h
  funext s
  simp [eraseSlot, h]

theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena := by
  constructor
  · intro i
    obtain ⟨bad, fixed, anchors, rejected⟩ := actual_sensitivity i
    exact ⟨actual, bad, fixed, congrFun anchors, ⟨fun _ => rejected, fun _ => actual_law⟩⟩
  · intro i; exact Fin.elim0 i

theorem variation : arena.Law actual ∧ ¬ arena.Law (eraseSlot false) :=
  ⟨actual_law, erased_rejected _⟩

theorem dependence : ∀ i : Bool, ∃ x y : Three, actual.readout i x ≠ actual.readout i y := by
  change ∀ i : Bool, ∃ x y : Three, readouts i x ≠ readouts i y
  decide +kernel

theorem kernel_correspondence (x y : Three) : actual.toPrimitiveBundle.agrees x y ↔
    staticExactExperimentRealization.toPrimitiveBundle.agrees (threeEquiv x) (threeEquiv y) := by
  revert x y
  decide +kernel

#print axioms bridge
#print axioms sensitivity
#print axioms dependence
end Reg.Support.LegacyStaticDesign
