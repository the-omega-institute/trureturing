import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit

universe u
noncomputable section

structure Parameters where
  Vertices : Type u
  lower : SimpleGraph Vertices
  upper : SimpleGraph Vertices
  a : Vertices
  b : Vertices
  c : Vertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := SimpleGraph p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mode
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p K => graphMode K p.a p.b p.c) (fun e => nomatch e)

def bad : Realization signature.{u} := realize _
  (fun _ _ _ => Mode.all) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} (H U : SimpleGraph V) (_hHU : H ≤ U) (a b c : V)
    (_ha : ¬ H.Reachable b a) (_hc : ¬ H.Reachable b c),
    (∃ K : SimpleGraph V, H ≤ K ∧ K ≤ U ∧
      R.readout () ⟨V,H,U,a,b,c⟩ K = .ac) ↔
      (sideGraph U {v | ¬ H.Reachable b v}).Reachable a c

private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  let a : ULift.{u} (Fin 2) := ULift.up 0
  let b : ULift.{u} (Fin 2) := ULift.up 1
  have hab : ¬ (⊥ : SimpleGraph (ULift.{u} (Fin 2))).Reachable b a := by
    simp [reachable_bot,a,b]
  have hh := h (⊥ : SimpleGraph (ULift.{u} (Fin 2))) ⊥ le_rfl a b a hab hab
  obtain ⟨K,_,_,hk⟩ := hh.mpr (.rfl :
    (sideGraph (⊥ : SimpleGraph (ULift.{u} (Fin 2)))
      {v | ¬ (⊥ : SimpleGraph (ULift.{u} (Fin 2))).Reachable b v}).Reachable a a)
  simp [bad,realize] at hk

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let a : ULift.{u} (Fin 2) := ULift.up 0
  let b : ULift.{u} (Fin 2) := ULift.up 1
  have htop : (⊤ : SimpleGraph (ULift.{u} (Fin 2))).Reachable a b :=
    (show (⊤ : SimpleGraph (ULift.{u} (Fin 2))).Adj a b by simp [a,b]).reachable
  have hbot : graphMode (⊥ : SimpleGraph (ULift.{u} (Fin 2))) a b a = .ac := by
    simp [graphMode,reachable_bot,a,b]
  have hfull : graphMode (⊤ : SimpleGraph (ULift.{u} (Fin 2))) a b a = .all := by
    simp [graphMode,htop,htop.symm]
  refine ⟨⟨ULift (Fin 2),⊥,⊤,a,b,a⟩,⊥,⊤,?_⟩
  change graphMode (⊥ : SimpleGraph (ULift.{u} (Fin 2))) a b a ≠
    graphMode (⊤ : SimpleGraph (ULift.{u} (Fin 2))) a b a
  rw [hbot,hfull]
  decide

def registration : Registration arena.{u}
    (type_of% @interval_ac_iff_avoiding_forced_component.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨interval_ac_iff_avoiding_forced_component,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_interval_ac_iff_avoiding_forced_component :
    Contract.Registration (@interval_ac_iff_avoiding_forced_component.{u})
      (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation.register_interval_ac_iff_avoiding_forced_component
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p K => graphMode K p.a p.b p.c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation.register_interval_ac_iff_avoiding_forced_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_interval_ac_iff_avoiding_forced_component

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation
