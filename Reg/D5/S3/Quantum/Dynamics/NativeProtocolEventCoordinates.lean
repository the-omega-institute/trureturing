import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Dynamics.NativeProtocolEventCoordinates

import Reg.D5.S3.Quantum.Dynamics.NativeProtocolEventArithmetic
/-! Whole-family registration of the original native event input. -/

noncomputable section
open scoped BigOperators Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
namespace Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
local notation "NativeTree" => _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree

namespace Coordinates
abbrev signature := Arithmetic.signature
abbrev actual := Arithmetic.actual

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Basis → Bool),
    r.readout () L ⟨T,e⟩ = Coeff.realPhysical (Coeff.coordinates T e) ∧
    Coeff.realConjugate (Coeff.coordinates T e) =
      (∑ p, ∑ z, if e p z then (-1 : ℝ)^Coeff.exponent z *
        Complex.normSq (Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) z)
        else 0) ∧
    |Coeff.realConjugate (Coeff.coordinates T e)| ≤ Coeff.kappa^(2*maxCalls T)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h Unit (.leaf ()) (fun _ _ => false)).1
  change (1 : ℝ) = Coeff.realPhysical (Coeff.coordinates _ _) at hh
  simp [Coeff.coordinates] at hh

def family : Registration arena (type_of% (@original_event_coordinates_and_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e => original_event_coordinates_and_bound T e,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,rejected_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := Arithmetic.dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_event_coordinates_and_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_event_coordinates_and_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Coordinates.family
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
end Coordinates
end Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
