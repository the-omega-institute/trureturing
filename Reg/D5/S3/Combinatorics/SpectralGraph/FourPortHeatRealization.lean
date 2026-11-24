import D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization

open _root_.D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit Matrix
open scoped Matrix

namespace Gram

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun m => Matrix Port (Fin m) ℝ) (fun _ => PortMatrix)

private def phantomGram : PortMatrix :=
  !![2, 1, 0, 1; 1, 2, 1, 0; 0, 1, 2, 1; 1, 0, 1, 2]

def actual : Realization signature :=
  realize signature (fun _ _ A => A * Aᵀ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => phantomGram) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (A : Matrix Port (Fin m) ℝ), (∀ i k, 0 ≤ A i k) →
    CycleBounds (R.readout () m A) → 4 ≤ m

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hb : CycleBounds phantomGram := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [phantomGram]
    · intro i
      fin_cases i <;> norm_num [phantomGram] <;> decide
    · norm_num [phantomGram]
    · norm_num [phantomGram]
  exact (by decide : ¬ 4 ≤ 0) (h 0 0 (by simp) hb)

def family : Registration arena (type_of% cycle_gram_width) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_gram_width, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := by
    intro role
    refine ⟨(1 : ℕ), (0 : Matrix Port (Fin 1) ℝ), (Matrix.of fun _ _ => 1), ?_⟩
    intro h
    have hentry := congrArg (fun Q : PortMatrix => Q 0 0) h
    norm_num [actual, realize, Matrix.mul_apply, Fin.sum_univ_one] at hentry

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    cycle_gram_width (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization.Gram.unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization.Gram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A * Aᵀ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Gram

namespace Heat

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Generator 4) (fun _ => PortMatrix)

def actual : Realization signature :=
  realize signature (fun _ _ S => defect S) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := CycleHeatOrderGap (R.readout () () cycleGenerator)

private theorem zero_band_impossible : ¬ CycleHeatOrderGap 0 := by
  intro h
  have hzero : IsPhysical (0 : Generator 0) (fun _ => 1) := by
    simp [IsPhysical, Matrix.IsSymm]
  have hsmall := h.2.2.2.2 0 0 (fun _ => 1) hzero (.inr (by
    intro i j
    norm_num [defect, moment]))
  exact (by decide : ¬ 8 ≤ Fintype.card (Vertex 0)) hsmall

private theorem rejected_fails : ¬ arena.Law rejected :=
  zero_band_impossible

def family : Registration arena (type_of% cycle_heat_order_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_heat_order_gap, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := by
    intro role
    refine ⟨(), cycleGenerator, (0 : Generator 4), ?_⟩
    intro h
    change defect cycleGenerator = defect (0 : Generator 4) at h
    have hzero : defect (0 : Generator 4) = 0 := by simp [defect, moment]
    exact zero_band_impossible ((h.trans hzero) ▸ cycle_heat_order_gap)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    cycle_heat_order_gap (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization.Heat.unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization.Heat.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => defect S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization
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

end Heat

end Reg.D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization
