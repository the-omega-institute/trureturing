import D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The five calibrated moments are an essential readout of the finite-moment law. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization

open _root_.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit Matrix

abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Generator 4) (fun _ => Fin 5 → PortMatrix)

def actual : Realization signature :=
  realize signature (fun _ _ S => momentWindow S) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => momentWindow (0 : Generator 4)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ExactOrderGap (R.readout () () generator)

private theorem zero_window_fails : ¬ ExactOrderGap (momentWindow (0 : Generator 4)) := by
  intro h
  have hzero : IsPhysical (0 : Generator 0) (fun _ => 1) := by
    simp [IsPhysical, Matrix.IsSymm]
  have hm (k : Fin 5) : moment (0 : Generator 0) k = momentWindow (0 : Generator 4) k := by
    fin_cases k <;> norm_num [momentWindow, moment, ports, Matrix.transpose_fromRows,
      Matrix.fromCols_mul_fromRows]
  have hsmall := h.2.2.2.2.2.2.1 0 0 (fun _ => 1) hzero hm
  exact (by decide : ¬ 6 ≤ Fintype.card (Vertex 0)) hsmall

private theorem rejected_fails : ¬ arena.Law rejected := zero_window_fails

def family : Registration arena (type_of% exact_order_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_order_gap, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := by
    intro role
    refine ⟨(), generator, (0 : Generator 4), ?_⟩
    intro h
    change momentWindow generator = momentWindow (0 : Generator 4) at h
    exact zero_window_fails (h ▸ exact_order_gap)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    exact_order_gap (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization.unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => momentWindow S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization
