import Reg.Support.LegacyFiniteTransport
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction

namespace Reg.Support.LegacyGluing
open LeanInformationAudit
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open Reg.Support.LegacyFiniteTransport

abbrev State := Bool × Bool × Bool

def roleEquiv : Fin 3 ≃ GluingReadout where
  toFun i := if i = 0 then .admit01 else if i = 1 then .admit12 else .admit02
  invFun | .admit01 => 0 | .admit12 => 1 | .admit02 => 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

/-- These are the original local equalities and disequality on global triples. -/
def readouts : Fin 3 → State → Bool := fun i s =>
  selectThree
    (Bool.rec (Bool.not s.2.1) s.2.1 s.1)
    (Bool.rec (Bool.not s.2.2) s.2.2 s.2.1)
    (Bool.rec s.2.2 (Bool.not s.2.2) s.1) i

def actual := admitRealization (fun i s => readouts i s)

def toOriginal (r : PrimitiveRealization (admitSignature State (Fin 3))) :
    PrimitiveRealization localLawGluingSignature :=
  ⟨fun i => r.readout (roleEquiv.symm i), Fin.elim0⟩

def arena : ObjectDomainArena where
  Domain := Bool × Bool × Bool
  toArena := Arena.ofFintype State
  signature := admitSignature State (Fin 3)
  Law r := localLawGluingArena.Law (toOriginal r)

theorem nondegenerate : arena.toArena.Nondegenerate := by decide +kernel

def enumeration : Arena.StateEnumeration arena.toArena where
  states := ([false, true] : List Bool).product (([false, true] : List Bool).product ([false, true] : List Bool))
  nodup := by
    change (([false, true] : List Bool).product (([false, true] : List Bool).product ([false, true] : List Bool)) : List State).Nodup
    decide +kernel
  complete := by
    change (([false, true] : List Bool).product (([false, true] : List Bool).product ([false, true] : List Bool)) : List State).toFinset = Finset.univ
    decide +kernel

theorem actual_correspondence : toOriginal actual = localLawGluingRealization := by
  apply realization_ext
  · funext i s
    cases i <;> rcases s with ⟨a,b,c⟩ <;> cases a <;> cases b <;> cases c <;> rfl
  · funext i; exact Fin.elim0 i

theorem bridge : LegacyPrimitiveRealization arena.toPrimitiveLawArena LocalLawGluingStatement actual := by
  refine ⟨?_⟩
  change _ ↔ localLawGluingArena.Law (toOriginal actual)
  rw [actual_correspondence]
  exact compatible_local_laws_can_lack_global_state_realization.equivalence

theorem actual_law : arena.Law actual := bridge.equivalence.mp compatible_local_laws_can_lack_global_state

def eraseSlot (i : (Fin 3)) : PrimitiveRealization (admitSignature State (Fin 3)) :=
  ⟨fun (j : (Fin 3)) (s : State) => if j = i then false else actual.readout j s, Fin.elim0⟩

theorem erased_rejected (i : Fin 3) : ¬ arena.Law (eraseSlot i) := by
  intro h
  fin_cases i
  · obtain ⟨s, hs, _⟩ := (h.1 false).mpr ⟨(false, false, false), rfl, rfl⟩
    exact Bool.false_ne_true hs
  · obtain ⟨s, hs, _⟩ := (h.1 false).mp ⟨(false, false, false), rfl, rfl⟩
    exact Bool.false_ne_true hs
  · obtain ⟨s, hs, _⟩ := (h.2.1 false).mp ⟨(false, false, false), rfl, rfl⟩
    exact Bool.false_ne_true hs

theorem actual_sensitivity (i : (Fin 3)) : ∃ bad : PrimitiveRealization arena.signature,
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

theorem variation : arena.Law actual ∧ ¬ arena.Law (eraseSlot 0) :=
  ⟨actual_law, erased_rejected _⟩

theorem dependence : ∀ i : (Fin 3), ∃ x y : State, actual.readout i x ≠ actual.readout i y := by
  change ∀ i : (Fin 3), ∃ x y : State, readouts i x ≠ readouts i y
  decide +kernel

theorem kernel_correspondence (x y : State) : actual.toPrimitiveBundle.agrees x y ↔
    localLawGluingRealization.toPrimitiveBundle.agrees x y := by
  revert x y
  decide +kernel

#print axioms bridge
#print axioms sensitivity
#print axioms dependence
end Reg.Support.LegacyGluing
