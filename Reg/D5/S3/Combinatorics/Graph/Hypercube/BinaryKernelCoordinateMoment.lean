/- GID: Reg/D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment
   generality: G
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: none
   digest: A source-bound audit of binary cube adjacency in the kernel-image theorem. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment

open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Word (n : ℕ) := Finset (Fin n) → ZMod 2

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Word Word

def actual : Realization signature :=
  realize signature (fun _ _ f => adjacency f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (_ : Even n) (_ : Fin n) (f : Word n),
    R.readout () n f = 0 ↔ ∃ g : Word n, adjacency g = f

private theorem adjacency_zero (n : ℕ) : adjacency (0 : Word n) = 0 := by
  funext x
  simp [adjacency]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (@h 2 ⟨1, rfl⟩ 0 0).mpr ⟨0, adjacency_zero 2⟩
  exact one_ne_zero (congrFun hz ∅)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, coordinateBit 0, ?_⟩
  intro h
  have hbit : adjacency (coordinateBit (0 : Fin 2)) ∅ = 1 := by decide
  change adjacency (0 : Word 2) = adjacency (coordinateBit 0) at h
  rw [adjacency_zero] at h
  exact one_ne_zero (hbit.symm.trans (congrFun h ∅).symm)

def family : Registration arena (type_of% (@adjacency_eq_zero_iff_exists_adjacency)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjacency_eq_zero_iff_exists_adjacency, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@adjacency_eq_zero_iff_exists_adjacency) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment.adjacency_eq_zero_iff_exists_adjacency.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => adjacency f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
