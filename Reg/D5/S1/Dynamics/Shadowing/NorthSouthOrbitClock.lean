import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S1.Dynamics.Shadowing.NorthSouthSelector

/-! The observed height coordinate is v(N), with the original StrictHeight
witness retained. Logical reconstruction does not assert a source selector. -/

noncomputable section
open Set Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing.PointwiseNorthSouth

namespace Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock
universe u

abbrev heightSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization heightSignature :=
  realize heightSignature (fun _ _ r => @decide (r = -1) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization heightSignature :=
  realize heightSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := heightSignature
  Law A := ∀ {M : Type u} [MetricSpace M] {f : M ≃ₜ M} {N S : M} [CompactSpace M],
    Pointwise f N S → ∃ v : StrictHeight f N S, A.readout () () (v.value N) = true

theorem source_bridge : (type_of% (@exists_strictHeight.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro hh M metric f N S compact h
    obtain ⟨v⟩ := hh h
    exact ⟨v, by simp [actual, realize, v.north]⟩
  · intro hh M metric f N S compact h
    obtain ⟨v, hv⟩ := hh h
    exact ⟨v⟩

theorem actual_law : arena.{u}.Law actual := source_bridge.mp (@exists_strictHeight.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  obtain ⟨v, hv⟩ := hh NorthSouthSelector.twoDynamics
  exact Bool.false_ne_true hv

def familyRegistration : Registration arena.{u} (type_of% (@exists_strictHeight.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), -1, 0, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_strictHeight.{u}) (Realization heightSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock.heightExistence
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize heightSignature
    (fun _ _ r => @decide (r = -1) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock

namespace Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock.FixedPole
universe u

abbrev arena : Arena where
  signature := NorthSouthSelector.outputSignature.{u}
  Law A := ∀ {M : Type u} [MetricSpace M] {f : M ≃ₜ M} {N : M},
    f N = N → ∀ i : ℤ, A.readout () ⟨M, N⟩ ((f ^ i) N) = true

theorem actual_law : arena.{u}.Law NorthSouthSelector.actual := by
  classical
  simpa only [arena, NorthSouthSelector.actual, realize, decide_eq_true_eq] using (@zpow_fixed.{u})

theorem rejected_law : ¬ arena.{u}.Law NorthSouthSelector.rejected := by
  intro hh
  exact Bool.false_ne_true (hh (f := Homeomorph.refl NorthSouthSelector.Two.{u})
    (N := NorthSouthSelector.north) rfl 0)

def familyRegistration : Registration arena.{u} (type_of% (@zpow_fixed.{u})) where
  actual := NorthSouthSelector.actual
  bridge := by
    classical
    simp only [arena, NorthSouthSelector.actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, NorthSouthSelector.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨NorthSouthSelector.rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := NorthSouthSelector.familyRegistration.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zpow_fixed.{u}) (Realization NorthSouthSelector.outputSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock.fixedPole
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock.FixedPole.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize NorthSouthSelector.outputSignature.{u}
    (fun _ p x => @decide (x = p.2) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock.FixedPole
