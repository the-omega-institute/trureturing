import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit

universe u
noncomputable section

structure Parameters where
  Vertices : Type u
  lower : SimpleGraph Vertices
  upper : SimpleGraph Vertices
  graph : SimpleGraph Vertices
  a : Vertices
  b : Vertices
  c : Vertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := SimpleGraph p.Vertices × p.Vertices × p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ _ s => @decide (s.1.Reachable s.2.1 s.2.2) (Classical.propDecidable _))
  (fun e => nomatch e)

def bad : Realization signature.{u} := realize _ (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law Q := ∀ {V : Type u} (H U K : SimpleGraph V)
    (_hHK : H ≤ K) (_hKU : K ≤ U) (a b c : V)
    (_ha : ¬ H.Reachable b a) (_hc : ¬ H.Reachable b c)
    (_hsep : ¬ (sideGraph U {v | ¬ H.Reachable b v}).Reachable a c),
    let A := {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}
    let L := H ⊔ touchGraph K A
    let R := H ⊔ sideGraph K Aᶜ
    let p : Parameters.{u} := ⟨V,H,U,K,a,b,c⟩
    (Q.readout () p ⟨K,a,b⟩ = true ↔ Q.readout () p ⟨L,a,b⟩ = true) ∧
      (Q.readout () p ⟨K,b,c⟩ = true ↔ Q.readout () p ⟨R,b,c⟩ = true) ∧
      (Q.readout () p ⟨K,a,c⟩ = true ↔
        Q.readout () p ⟨L,a,b⟩ = true ∧ Q.readout () p ⟨R,b,c⟩ = true) ∧
      graphMode K a b c =
        if Q.readout () p ⟨L,a,b⟩ = true then
          (if Q.readout () p ⟨R,b,c⟩ = true then .all else .ab)
        else if Q.readout () p ⟨R,b,c⟩ = true then .bc else .separate

private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  let a : ULift.{u} (Fin 3) := ULift.up 0
  let b : ULift.{u} (Fin 3) := ULift.up 1
  let c : ULift.{u} (Fin 3) := ULift.up 2
  let O : SimpleGraph (ULift.{u} (Fin 3)) := ⊥
  have ha : ¬ O.Reachable b a := by simp [O,reachable_bot,a,b]
  have hc : ¬ O.Reachable b c := by simp [O,reachable_bot,b,c]
  have hF : sideGraph O {v | ¬ O.Reachable b v} = ⊥ := by
    ext x y
    simp [sideGraph,O]
  have hsep : ¬ (sideGraph O {v | ¬ O.Reachable b v}).Reachable a c := by
    rw [hF]
    simp [reachable_bot,a,c]
  have hf := (h O O O le_rfl le_rfl a b c ha hc hsep).2.2.2
  simp [bad,realize,graphMode,O,reachable_bot,a,b,c] at hf

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let a : ULift.{u} (Fin 3) := ULift.up 0
  let b : ULift.{u} (Fin 3) := ULift.up 1
  let c : ULift.{u} (Fin 3) := ULift.up 2
  let U := SimpleGraph.starGraph b
  have hU : U.Reachable a b :=
    (show U.Adj a b by simp [U,starGraph_adj,a,b]).reachable
  have hbot : ¬ (⊥ : SimpleGraph (ULift.{u} (Fin 3))).Reachable a b := by
    simp [reachable_bot,a,b]
  refine ⟨⟨ULift (Fin 3),⊥,U,⊥,a,b,c⟩,⟨⊥,a,b⟩,⟨U,a,b⟩,?_⟩
  simp [actual,realize,hbot,hU]

def registration : Registration arena.{u} (type_of% @wired_separation.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h V H U K hHK hKU a b c ha hc hs
      have hh := @h V H U K hHK hKU a b c ha hc hs
      dsimp only at hh ⊢
      by_cases hL : (H ⊔ touchGraph K
          {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}).Reachable a b <;>
        by_cases hR : (H ⊔ sideGraph K
          {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}ᶜ).Reachable b c <;>
        simpa [actual,realize,hL,hR] using hh
    · intro h V H U K hHK hKU a b c ha hc hs
      have hh := @h V H U K hHK hKU a b c ha hc hs
      dsimp only at hh ⊢
      by_cases hL : (H ⊔ touchGraph K
          {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}).Reachable a b <;>
        by_cases hR : (H ⊔ sideGraph K
          {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}ᶜ).Reachable b c <;>
        simpa [actual,realize,hL,hR] using hh
  variation := ⟨by
    intro V H U K hHK hKU a b c ha hc hs
    have hh := @wired_separation.{u} V H U K hHK hKU a b c ha hc hs
    dsimp only at hh ⊢
    by_cases hL : (H ⊔ touchGraph K
        {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}).Reachable a b <;>
      by_cases hR : (H ⊔ sideGraph K
        {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}ᶜ).Reachable b c <;>
      simpa [actual,realize,hL,hR] using hh,bad,rejected⟩
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

def register_wired_separation : Contract.Registration (@wired_separation.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation.register_wired_separation
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation.registration
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
    (fun _ _ s => @decide (s.1.Reachable s.2.1 s.2.2) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation.register_wired_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_wired_separation

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation
