import Reg.Support.LegacyFiniteTransport
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations

namespace Reg.Support.LegacyResidue
open LeanInformationAudit
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open _root_.D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open Reg.Support.LegacyFiniteTransport
open RegistrationTemplates

abbrev State := Bool × Bool

def stateEquiv : State ≃ ResidueState where
  toFun s := if s.1 then (if s.2 then twentyOneState else fifteenState)
    else (if s.2 then tenState else zeroState)
  invFun s := if s = zeroState then (false, false) else if s = tenState then (false, true)
    else if s = fifteenState then (true, false) else (true, true)
  left_inv := by rintro ⟨a,b⟩; cases a <;> cases b <;> rfl
  right_inv := by intro s; fin_cases s <;> rfl

def sensorEquiv : Fin 3 ≃ ResidueSensor where
  toFun i := if i = 0 then .two else if i = 1 then .three else .five
  invFun | .two => 0 | .three => 1 | .five => 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

/-- Actual modular readouts under the two proved finite equivalences. -/
def readouts : Fin 3 → State → Bool := fun i s =>
  selectThree s.1 (Bool.and (Bool.not s.1) s.2) (Bool.and s.1 s.2) i

def actual := binaryFamilyRealization (fun i s => readouts i s)

def toOriginal (r : PrimitiveRealization (binaryFamilySignature State (Fin 3))) :
    PrimitiveRealization residueSignature :=
  ⟨fun i s => r.readout (sensorEquiv.symm i) (stateEquiv.symm s), Fin.elim0⟩

/-- The whole original Law, including allowed protocols and both dynamic minima. -/
def arena : ObjectDomainArena where
  Domain := ResidueState
  toArena := Arena.ofFintype State
  signature := binaryFamilySignature State (Fin 3)
  Law r := residueArena.Law (toOriginal r)

theorem nondegenerate : arena.toArena.Nondegenerate := by decide +kernel

def enumeration : Arena.StateEnumeration arena.toArena where
  states := ([false, true] : List Bool).product ([false, true] : List Bool)
  nodup := by
    change (([false, true] : List Bool).product ([false, true] : List Bool) : List State).Nodup
    decide +kernel
  complete := by
    change (([false, true] : List Bool).product ([false, true] : List Bool) : List State).toFinset = Finset.univ
    decide +kernel

theorem actual_correspondence : toOriginal actual = residueRealization := by
  apply realization_ext
  · funext i s
    cases i <;> fin_cases s <;> rfl
  · funext i; exact Fin.elim0 i

theorem bridge : LegacyPrimitiveRealization arena.toPrimitiveLawArena
    (twoStepStatement .two .three .five zeroState tenState fifteenState twentyOneState
      residueReadout residueAdaptiveDepth residueStaticDepth) actual := by
  refine ⟨?_⟩
  change _ ↔ residueArena.Law (toOriginal actual)
  rw [actual_correspondence]
  exact two_step_adaptive_residue_identification_realization.equivalence

theorem actual_law : arena.Law actual := bridge.equivalence.mp two_step_adaptive_residue_identification

/-- An allowed adaptive protocol cannot separate two states with equal sensor data. -/
theorem protocol_preserves_fibers {X I : Type} {n : Nat} (r : I → X → Bool)
    (p : BinaryProtocol X n) (uses : UsesReadoutFamily r p)
    (x y : X) (same : ∀ i, r i x = r i y) : p.transcript x = p.transcript y := by
  have bits : ∀ k (hk : k < n),
      (p.transcript x).getLsb ⟨k,hk⟩ = (p.transcript y).getLsb ⟨k,hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rw [p.transcript_consistent x ⟨k,hk⟩, p.transcript_consistent y ⟨k,hk⟩]
      have history :
          (fun j : Fin k => (p.transcript x).getLsb ⟨j.val, j.isLt.trans hk⟩) =
          (fun j : Fin k => (p.transcript y).getLsb ⟨j.val, j.isLt.trans hk⟩) := by
        funext j
        exact ih j.val j.isLt _
      rw [history]
      obtain ⟨i, hi⟩ := uses ⟨k,hk⟩ _
      rw [hi]
      exact same i
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  exact bits k hk

def eraseSlot (i : (Fin 3)) : PrimitiveRealization (binaryFamilySignature State (Fin 3)) :=
  ⟨fun (j : (Fin 3)) (s : State) => if j = i then false else actual.readout j s, Fin.elim0⟩

theorem erased_rejected (i : Fin 3) : ¬ arena.Law (eraseSlot i) := by
  intro h
  fin_cases i
  · have collision := (h.1 fifteenState).mp rfl
    rcases collision with h | h
    · exact (by decide : fifteenState ≠ zeroState) h
    · exact (by decide : fifteenState ≠ tenState) h
  · obtain ⟨p, _, _, uses, inj⟩ := h.2.2.1
    apply (show zeroState ≠ tenState by decide)
    apply inj
    exact protocol_preserves_fibers _ p uses zeroState tenState (by intro i; cases i <;> rfl)
  · obtain ⟨p, _, _, uses, inj⟩ := h.2.2.1
    apply (show fifteenState ≠ twentyOneState by decide)
    apply inj
    exact protocol_preserves_fibers _ p uses fifteenState twentyOneState (by intro i; cases i <;> rfl)

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
    residueRealization.toPrimitiveBundle.agrees (stateEquiv x) (stateEquiv y) := by
  revert x y
  decide +kernel

#print axioms bridge
#print axioms sensitivity
#print axioms dependence
end Reg.Support.LegacyResidue
