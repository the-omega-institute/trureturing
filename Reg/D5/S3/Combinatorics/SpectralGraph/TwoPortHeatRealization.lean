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

namespace FixedMass

abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ m => Fintype.card (Vertex m)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (S : Generator m) (z : Vertex m → ℝ), IsPhysical S z →
    totalMass z = totalMass ground → moment S 1 = moment generator 1 →
    moment S 2 = moment generator 2 → moment S 3 = moment generator 3 →
    6 ≤ R.readout () () m

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  exact (by decide : ¬ 6 ≤ 0)
    (h 4 generator ground exact_order_gap.1 rfl rfl rfl rfl)

def family : Registration arena (type_of% fixed_total_mass_moment_obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_total_mass_moment_obstruction, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := by
    change ObservationalDependence signature actual
    intro role
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change Fintype.card (Vertex 0) ≠ Fintype.card (Vertex 1)
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    fixed_total_mass_moment_obstruction (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization.FixedMass.unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization.FixedMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => Fintype.card (Vertex m)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedMass

end Reg.D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization
