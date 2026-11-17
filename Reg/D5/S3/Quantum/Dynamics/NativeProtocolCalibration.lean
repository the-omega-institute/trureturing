import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Dynamics.NativeProtocolCalibration

/-! Whole-family registration of the original native event input. -/

noncomputable section
open scoped BigOperators Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
namespace Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
local notation "NativeTree" => _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree

namespace EmptyPetz
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Actual
local instance : NormedAddCommGroup Qubit := Matrix.instL2OpNormedAddCommGroup
local instance : NormedSpace ℂ Qubit := Matrix.instL2OpNormedSpace
local instance : NormedRing Qubit := Matrix.instL2OpNormedRing
local instance : NormedAlgebra ℂ Qubit := Matrix.instL2OpNormedAlgebra

abbrev Input := Fin 2 → NativeTree Stop
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Input) (fun _ => ℝ × ℕ)

/-- Both observed operands occur in the original continuation discrepancy:
the actual raw event and its complete syntactic maximum resource. -/
def actual : Realization signature :=
  realize signature (fun _ _ C =>
    (eventMass (extensionAt .active C) (fun _ z => z 2),
      maxCalls (extensionAt .active C))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ C =>
    (emptyTarget,maxCalls (extensionAt .active C))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    reduced ((operator sourceTree ()).mulVec omega0) = chi ∧
    calls sourceTree () = 3 ∧ chi.PosDef ∧ chi.trace = 1 ∧ chi.det = t^4 ∧
    cfc Real.sqrt chi = chiRoot ∧
    (∀ v : Basis → ℂ,
      (∑ j : Fin 2, reduced ((projector (readBit 2) j).mulVec v)) =
        delta (reduced v)) ∧
    reduced omega0 = p0 ∧
    (∀ j : Fin 2, (projector (readBit 2) j).mulVec omega0 =
      if j = 0 then omega0 else 0) ∧
    petz (reduced omega0) 1 1 = ((emptyTarget : ℝ) : ℂ) ∧
    (∀ C : Fin 2 → NativeTree Stop,
      let T := extensionAt .active C
      (r.readout () () C).1 ≠ (petz (reduced omega0) 1 1).re ∧
      1/(11*(Coeff.kappa^(2*(r.readout () () C).2)+(13+5*Real.sqrt 5)/22)) ≤
        |(r.readout () () C).1 - (petz (reduced omega0) 1 1).re|)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases h with ⟨_,_,_,_,_,_,_,_,_,hp,hall⟩
  have hx := (hall (fun _ => .leaf ⟨.normal,0⟩)).1
  change emptyTarget ≠ (petz (reduced omega0) 1 1).re at hx
  rw [hp, Complex.ofReal_re] at hx
  exact hx rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let x : Input := fun _ => .leaf ⟨.normal,0⟩
  let y : Input := fun _ => .call 0 .inverse (.leaf ⟨.normal,0⟩)
  refine ⟨(),x,y,?_⟩
  intro heq
  have hh := congrArg Prod.snd heq
  change maxCalls (extensionAt .active x) = maxCalls (extensionAt .active y) at hh
  have hx : maxCalls (extensionAt .active x) = 0 := by
    simp [maxCalls, extensionAt, x, calls]
  have hy : maxCalls (extensionAt .active y) = 9 := by
    simp only [maxCalls, extensionAt, y, calls, callCost, add_zero]
    exact Finset.sup_const Finset.univ_nonempty 9
  rw [hx,hy] at hh
  norm_num at hh

def family : Registration arena (type_of% (@original_empty_petz_consumer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_empty_petz_consumer,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- Whole-family evidence retains the exact original input and both readout
operands. Selected source reconstruction remains unresolved under issue 26627. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_empty_petz_consumer) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_empty_petz_consumer.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.EmptyPetz.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end EmptyPetz
end Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
