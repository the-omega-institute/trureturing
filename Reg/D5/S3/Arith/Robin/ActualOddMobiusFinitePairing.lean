import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
import Reg.Support.DependentFamily
namespace Reg.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
open Finset
open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (F : ℕ → ℝ),
    (∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ)*F n) =
      (∑ n ∈ Ioc 0 N, R.readout () () n*F n) -
        ∑ m ∈ Ioc 0 (N/2), R.readout () () m*F (2*m)
def actual : Realization signature :=
  realize signature (fun _ _ n => oddCoefficient n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (fun _ => 1)
  norm_num [rejected, realize, show Ioc 0 1 = {1} by decide] at hh

def registration : Registration arena (type_of% weighted_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_split, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, oddCoefficient]
noncomputable def registration_1 :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      weighted_split (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing.splitUnit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨registration⟩⟩
  options := #[] }
#print axioms registration
end
end Reg.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
