import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Dynamics.NativeProtocolEventArithmetic
import Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft

/-! Whole-family registration of the original native event input. -/

noncomputable section
open scoped BigOperators Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
namespace Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
local notation "NativeTree" => _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree

namespace Arithmetic

structure Event (L : Type) where
  tree : NativeTree L
  event : Path tree → Basis → Bool

abbrev signature : Signature where
  Params := Type
  State := Event
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => eventMass x.tree x.event) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => emptyTarget) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Basis → Bool),
    IsIntegral ℤ (r.readout () L ⟨T,e⟩) ∧
      r.readout () L ⟨T,e⟩ ≠ emptyTarget ∧
      r.readout () L ⟨T,e⟩ ≠ referenceTarget

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h Unit (.leaf ()) (fun _ _ => false)).2.1 rfl

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨Unit,⟨.leaf (),fun _ _ => false⟩,⟨.leaf (),fun _ _ => true⟩,?_⟩
  change eventMass ((.leaf ()) : NativeTree Unit) (fun _ _ => false) ≠
    eventMass ((.leaf ()) : NativeTree Unit) (fun _ _ => true)
  simp [eventMass, mass, operator, omega0]
  apply ne_of_lt
  exact_mod_cast (Finset.card_pos.mpr (Finset.univ_nonempty :
    (Finset.univ : Finset (Path ((.leaf ()) : NativeTree Unit))).Nonempty))

def family : Registration arena (type_of% (@original_event_arithmetic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e => original_event_arithmetic T e,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_event_arithmetic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_event_arithmetic.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Arithmetic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => eventMass x.tree x.event)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Arithmetic

#print axioms family
#print axioms registration

namespace Resources
abbrev signature := Arithmetic.signature
abbrev actual := Arithmetic.actual
abbrev rejected := Arithmetic.rejected

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Basis → Bool),
    (0 < r.readout () L ⟨T,e⟩ →
      (Coeff.kappa^(2*maxCalls T))⁻¹ ≤ r.readout () L ⟨T,e⟩) ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(13+5*Real.sqrt 5)/22)) ≤
      |r.readout () L ⟨T,e⟩-emptyTarget| ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(19+9*Real.sqrt 5)/22)) ≤
      |r.readout () L ⟨T,e⟩-referenceTarget|

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h Unit (.leaf ()) (fun _ _ => false)).2.1
  change 1/(11*(Coeff.kappa^(2*maxCalls ((.leaf ()) : NativeTree Unit))+
    (13+5*Real.sqrt 5)/22)) ≤ |emptyTarget-emptyTarget| at hh
  rw [sub_self, abs_zero] at hh
  have hp : 0 < 1/(11*(Coeff.kappa^(2*maxCalls ((.leaf ()) : NativeTree Unit))+
      (13+5*Real.sqrt 5)/22)) := by
    dsimp [Coeff.kappa, phi]
    positivity
  linarith

def family : Registration arena (type_of% (@original_event_resource_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e => original_event_resource_bounds T e,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,rejected_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := Arithmetic.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_event_resource_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_event_resource_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Resources.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => eventMass x.tree x.event)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Resources

#print axioms Resources.family
end Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft

namespace Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.PositiveNorm

abbrev signature : Signature where
  Params := ℝ
  State _ := Coeff.O
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Coeff.realPhysical x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1/2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (x : Coeff.O) (K : ℝ), 0 < K → 0 < r.readout () K x →
    |Coeff.realConjugate x| ≤ K → K⁻¹ ≤ r.readout () K x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1 (by norm_num) (by norm_num [rejected,realize]) (by simp)
  norm_num [rejected,realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1,0,1,?_⟩
  change Coeff.realPhysical 0 ≠ Coeff.realPhysical 1
  simp

def family : Registration arena (type_of% (@Coeff.positive_lower)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Coeff.positive_lower,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Coeff.positive_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.Coeff.positive_lower.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.PositiveNorm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Coeff.realPhysical x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.PositiveNorm
