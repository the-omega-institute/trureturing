import Reg.Support.LegacyFiniteTransport
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations

namespace Reg.Support.LegacyAgenda
open LeanInformationAudit
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower
open _root_.D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
open Reg.Support.LegacyFiniteTransport

abbrev State := Three × Three × Three

/-- Normalize by the finalist, then rotate the cyclic profile to the desired winner.
The inverse records the actual source winner and both relative entrants. -/
def stateEquiv : State ≃ Agenda where
  toFun s :=
    let a := threeEquiv s.2.1
    let b := threeEquiv s.2.2
    let rotation := threeEquiv s.1 - sequentialWinner majorityPrefers ⟨a, b, 0⟩
    ⟨a + rotation, b + rotation, rotation⟩
  invFun a := (threeEquiv.symm (sequentialWinner majorityPrefers a),
    threeEquiv.symm (a.first - a.final), threeEquiv.symm (a.second - a.final))
  left_inv := by decide +kernel
  right_inv := by intro a; rcases a with ⟨a,b,c⟩; fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

/-- In normalized coordinates, validity means that the relative entrants are 1,2 or 2,1. -/
def valid : State → Bool := fun s =>
  Sum.rec (fun a => Bool.rec false
      (Sum.rec (fun _ => false) (fun _ => true) s.2.2) a)
    (fun _ => Sum.rec (fun b => b) (fun _ => false) s.2.2) s.2.1

def winnerCode (s : State) : Fin 3 := code s.1

def actual := agendaRealization (fun s => winnerCode s) (fun s => valid s)

def toOriginal (r : PrimitiveRealization (agendaSignature State (Fin 3))) :
    PrimitiveRealization agendaPowerSignature where
  readout
    | .winner => fun a => r.readout false (stateEquiv.symm a)
    | .valid => fun a => r.readout true (stateEquiv.symm a)
  anchor := Fin.elim0

def arena : ObjectDomainArena where
  Domain := Agenda
  toArena := Arena.ofFintype State
  signature := agendaSignature State (Fin 3)
  Law r := agendaPowerArena.Law (toOriginal r)

theorem nondegenerate : arena.toArena.Nondegenerate := by decide +kernel

def enumeration : Arena.StateEnumeration arena.toArena where
  states := ([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three).product (([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three).product ([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three))
  nodup := by
    change (([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three).product (([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three).product ([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three)) : List State).Nodup
    decide +kernel
  complete := by
    change (([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three).product (([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three).product ([Sum.inl false, Sum.inl true, Sum.inr ()] : List Three)) : List State).toFinset = Finset.univ
    decide +kernel

theorem actual_correspondence : toOriginal actual = agendaPowerRealization := by
  apply realization_ext
  · funext i a
    cases i <;> rcases a with ⟨a,b,c⟩ <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
  · funext i; exact Fin.elim0 i

theorem bridge : LegacyPrimitiveRealization arena.toPrimitiveLawArena
    ((∀ desired : Fin 3, ∃ agenda : Agenda,
      ValidAgenda agenda ∧ sequentialWinner majorityPrefers agenda = desired) ∧
    ∃ agenda agenda' : Agenda,
      ValidAgenda agenda ∧ ValidAgenda agenda' ∧ agenda ≠ agenda' ∧
        sequentialWinner majorityPrefers agenda ≠ sequentialWinner majorityPrefers agenda') actual := by
  refine ⟨?_⟩
  change _ ↔ agendaPowerArena.Law (toOriginal actual)
  rw [actual_correspondence]
  exact agenda_power_realization.equivalence

theorem actual_law : arena.Law actual := bridge.equivalence.mp agenda_power

def eraseWinner := agendaRealization (fun _ : State => (0 : Fin 3)) valid

def eraseValid := agendaRealization (fun s => winnerCode s) (fun _ : State => false)

theorem eraseWinner_rejected : ¬ arena.Law eraseWinner := by
  intro h
  obtain ⟨a, _, ha⟩ := h.1 1
  exact (by decide : (0 : Fin 3) ≠ 1) ha

theorem eraseValid_rejected : ¬ arena.Law eraseValid := by
  intro h
  obtain ⟨a, ha, _⟩ := h.1 0
  exact Bool.false_ne_true ha

theorem actual_sensitivity (i : Bool) : ∃ bad : PrimitiveRealization arena.signature,
    (∀ j, j ≠ i → actual.readout j = bad.readout j) ∧
    actual.anchor = bad.anchor ∧ ¬ arena.Law bad := by
  cases i
  · refine ⟨eraseWinner, ?_, rfl, eraseWinner_rejected⟩
    intro j h; cases j; exact (h rfl).elim; rfl
  · refine ⟨eraseValid, ?_, rfl, eraseValid_rejected⟩
    intro j h; cases j; rfl; exact (h rfl).elim

theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena := by
  constructor
  · intro i
    obtain ⟨bad, fixed, anchors, rejected⟩ := actual_sensitivity i
    exact ⟨actual, bad, fixed, congrFun anchors, ⟨fun _ => rejected, fun _ => actual_law⟩⟩
  · intro i; exact Fin.elim0 i

theorem variation : arena.Law actual ∧ ¬ arena.Law eraseWinner := ⟨actual_law, eraseWinner_rejected⟩

theorem dependence : ∀ i : Bool, ∃ x y : State, actual.readout i x ≠ actual.readout i y := by
  intro i
  cases i
  · change ∃ x y : State, winnerCode x ≠ winnerCode y
    decide +kernel
  · change ∃ x y : State, valid x ≠ valid y
    decide +kernel

theorem kernel_correspondence (x y : State) : actual.toPrimitiveBundle.agrees x y ↔
    agendaPowerRealization.toPrimitiveBundle.agrees (stateEquiv x) (stateEquiv y) := by
  revert x y
  decide +kernel

#print axioms bridge
#print axioms sensitivity
#print axioms dependence
end Reg.Support.LegacyAgenda
