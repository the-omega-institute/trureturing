import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum
import Reg.Support.SingleDependentReadout

/-! The weight of a cube support as a readout at each dimension. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum

open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCrossing
open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped symmDiff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Finset (Finset (Fin n)))
    (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ S => S.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (_ : 6 ≤ n) (_ : Even n) (S : Finset (Finset (Fin n))),
    (R.readout () n S = n ∧ ∀ x, Even (neighborDirections S x).card) ↔
      ∃ x : Finset (Fin n), S = Finset.univ.image fun i : Fin n => x ∆ {i}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Finset (Finset (Fin 6)) := Finset.univ.image fun j : Fin 6 => ∅ ∆ {j}
  have hf := (@h 6 (by decide) ⟨3, rfl⟩ S).mpr ⟨∅, rfl⟩
  exact (by decide : ¬ (0 : ℕ) = 6) hf.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let S : Finset (Finset (Fin 6)) := Finset.univ.image fun j : Fin 6 => ∅ ∆ {j}
  refine ⟨6, ∅, S, ?_⟩
  intro h
  change 0 = S.card at h
  have hS := (minimum_support_iff (n := 6) (by decide) ⟨3, rfl⟩ S).mpr ⟨∅, rfl⟩
  exact (by decide : ¬ (0 : ℕ) = 6) (h.trans hS.1)

def family : Registration arena (type_of% (@minimum_support_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minimum_support_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@minimum_support_iff) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum.minimum_support_iff "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => S.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum
