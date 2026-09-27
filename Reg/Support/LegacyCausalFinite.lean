import Reg.Support.LegacyCausalSlots
import Reg.Support.LegacyFiniteTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Support.LegacyCausalFinite
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
open Reg.Support.LegacyCausalCoordinates

theorem local_nondegenerate : icObjectArena.Nondegenerate := by decide +kernel
theorem unified_nondegenerate : objectArena.Nondegenerate := by decide +kernel

def localStates : List ICData :=
  ([false, true] : List Bool).product (([false, true] : List Bool).product
    (([false, true] : List Bool).product ([false, true] : List Bool)))

def localEnumeration : Arena.StateEnumeration icObjectArena where
  states := localStates
  nodup := by change localStates.Nodup; decide +kernel
  complete := by change localStates.toFinset = Finset.univ; decide +kernel

/-- All 16 intervention/counterfactual models and all 32 observation/intervention
models occur once; the original coproduct branch is part of every state. -/
def unifiedStates : List UnifiedData :=
  localStates.map Sum.inl ++
    (([false, true] : List Bool).product
      ((([false, true] : List Bool).product ([false, true] : List Bool)).product
       (([false, true] : List Bool).product ([false, true] : List Bool)))).map Sum.inr

def unifiedEnumeration : Arena.StateEnumeration objectArena where
  states := unifiedStates
  nodup := by change unifiedStates.Nodup; decide +kernel
  complete := by change unifiedStates.toFinset = Finset.univ; decide +kernel

/-- Direct constructor selection of all eight coarse/fine components. -/
def selectEight {Y : Type} (a b c d e f g h : Y) (i : Fin 8) : Y :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (h) g (decide (i = Fin.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (by decide)))) f (decide (i = Fin.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (by decide)))) e (decide (i = Fin.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (by decide)))) d (decide (i = Fin.mk (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (by decide)))) c (decide (i = Fin.mk (Nat.succ (Nat.succ Nat.zero)) (by decide)))) b (decide (i = Fin.mk (Nat.succ Nat.zero) (by decide)))) a (decide (i = Fin.mk Nat.zero (by decide)))

def localRead (i : Fin 8) (x : ICData) : Bool :=
  selectEight (Bool.rec false x.2.2.1 x.1) (Bool.rec x.2.2.1 true x.1)
    (Bool.rec false x.2.2.2 x.2.1) (Bool.rec x.2.2.2 true x.2.1)
    x.1 x.2.1 x.2.2.1 x.2.2.2 i

def icRead (i : Fin 8) (x : UnifiedData) : Option Bool :=
  Sum.rec (fun b => some (localRead i b)) (fun _ => none) x

def oiRead (i : Fin 8) (x : UnifiedData) : Option Bool :=
  Sum.rec (fun _ => none) (fun b => some (
    selectEight (oiObs b).1 (oiObs b).2.1 (oiObs b).2.2.1 (oiObs b).2.2.2
      (oiInt b).1 (oiInt b).2.1 (oiInt b).2.2.1 (oiInt b).2.2.2 i)) x

def localActual := LegacyCausalSlots.slotRealization (fun i x => localRead i x)
def icActual := LegacyCausalSlots.slotRealization (fun i x => icRead i x)
def oiActual := LegacyCausalSlots.slotRealization (fun i x => oiRead i x)

theorem local_correspondence : localActual = LegacyCausalSlots.localActual := by
  apply LegacyFiniteTransport.realization_ext
  · funext i x; change Fin 8 at i; rcases x with ⟨a,b,c,d⟩
    fin_cases i <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl
  · rfl

theorem local_bridge : LegacyPrimitiveRealization LegacyCausalSlots.localArena
    (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N) localActual := by
  rw [local_correspondence]
  exact LegacyCausalSlots.local_bridge

theorem local_variation : LegacyCausalSlots.localArena.Law localActual ∧
    ¬ LegacyCausalSlots.localArena.Law (LegacyCausalSlots.constant false) := by
  rw [local_correspondence]
  exact LegacyCausalSlots.local_variation

theorem local_dependence : ∀ i : Fin 8, ∃ x y : ICData,
    localActual.readout i x ≠ localActual.readout i y := by
  rw [local_correspondence]
  exact LegacyCausalSlots.local_dependence

theorem ic_correspondence : icActual = LegacyCausalSlots.icActual := by
  apply LegacyFiniteTransport.realization_ext
  · funext i x; change Fin 8 at i
    rcases x with ⟨a,b,c,d⟩ | x
    · fin_cases i <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl
    · fin_cases i <;> rfl
  · rfl

theorem ic_bridge : LegacyPrimitiveRealization LegacyCausalSlots.icArena
    (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N) icActual := by
  rw [ic_correspondence]
  exact LegacyCausalSlots.ic_bridge

theorem ic_variation : LegacyCausalSlots.icArena.Law icActual ∧
    ¬ LegacyCausalSlots.icArena.Law (LegacyCausalSlots.constant none) := by
  rw [ic_correspondence]
  exact LegacyCausalSlots.ic_variation

theorem ic_dependence : ∀ i : Fin 8, ∃ x y : UnifiedData,
    icActual.readout i x ≠ icActual.readout i y := by
  rw [ic_correspondence]
  exact LegacyCausalSlots.ic_dependence

theorem oi_correspondence : oiActual = LegacyCausalSlots.oiActual := by
  apply LegacyFiniteTransport.realization_ext
  · funext i x; change Fin 8 at i; fin_cases i <;> cases x <;> rfl
  · rfl

theorem oi_bridge : LegacyPrimitiveRealization LegacyCausalSlots.oiArena
    (∃ M N : OI.Model, OI.Obs M = OI.Obs N ∧ OI.Int M ≠ OI.Int N) oiActual := by
  rw [oi_correspondence]
  exact LegacyCausalSlots.oi_bridge

theorem oi_variation : LegacyCausalSlots.oiArena.Law oiActual ∧
    ¬ LegacyCausalSlots.oiArena.Law (LegacyCausalSlots.constant none) := by
  rw [oi_correspondence]
  exact LegacyCausalSlots.oi_variation

theorem oi_dependence : ∀ i : Fin 8, ∃ x y : UnifiedData,
    oiActual.readout i x ≠ oiActual.readout i y := by
  rw [oi_correspondence]
  exact LegacyCausalSlots.oi_dependence

theorem ic_opposite_branch (x : OIData) (i : Fin 8) : icActual.readout i (.inr x) = none := rfl
theorem oi_opposite_branch (x : ICData) (i : Fin 8) : oiActual.readout i (.inl x) = none := rfl

#print axioms local_bridge
#print axioms ic_bridge
#print axioms oi_bridge
#print axioms local_dependence
#print axioms ic_dependence
#print axioms oi_dependence
end Reg.Support.LegacyCausalFinite
