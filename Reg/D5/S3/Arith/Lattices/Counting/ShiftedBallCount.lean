import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.Lattices.Counting.ShiftedBallCount

namespace Reg.D5.S3.Arith.Lattices.Counting.ShiftedBallCount

open LeanInformationAudit Filter Set Metric
open _root_.D5.S3.Arith.Lattices.Counting.ShiftedBallCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Topology

noncomputable section

namespace Bounded

abbrev signature := Reg.Support.SingleDependentReadout.signature E
  (fun _ => ℝ) (fun _ => Set P)

def actual : Realization signature := realize signature (fun _ c r => body c r) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (c : E) (r : ℝ), Bornology.IsBounded (R.readout () c r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbound : Bornology.IsBounded (Set.univ : Set P) := h 0 0
  exact (inferInstance : NeBot (Bornology.cobounded P)).ne
    (Bornology.cobounded_eq_bot_iff.mpr (Bornology.isBounded_univ.mp hbound))

def family : Registration arena (type_of% @body_bounded) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨body_bounded, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(0 : E), (-1 : ℝ), (0 : ℝ), ?_⟩
    change body 0 (-1) ≠ body 0 0
    intro h
    have hz : (0 : P) ∈ body 0 0 := by simp [body]
    rw [← h] at hz
    simp [body] at hz

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Arith.Lattices.Counting.ShiftedBallCount.body_bounded) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.Counting.ShiftedBallCount.body_bounded.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.Counting.ShiftedBallCount.Bounded.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ c r => body c r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.Counting.ShiftedBallCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bounded

namespace Limit

abbrev signature := Reg.Support.SingleDependentReadout.signature E
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ c r => (centerCount c r : ℝ) / r ^ 3) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ c : E, Tendsto (fun r : ℝ => R.readout () c r) atTop (𝓝 (4 * Real.pi / 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 (4 * Real.pi / 3)) := h 0
  exact (ne_of_gt (by positivity : 0 < 4 * Real.pi / 3))
    (tendsto_nhds_unique h' tendsto_const_nhds)

def family : Registration arena (type_of% @shifted_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shifted_limit, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    cases i
    by_contra! h
    apply rejected_law
    intro c
    have hz : actual.readout () c 0 = 0 := by simp [actual, realize]
    have he : (fun r : ℝ => actual.readout () c r) = fun _ => 0 := by
      funext r
      exact (h c r (0 : ℝ)).trans hz
    have hl : Tendsto (fun r : ℝ => actual.readout () c r) atTop (𝓝 (4 * Real.pi / 3)) :=
      shifted_limit c
    rw [he] at hl
    exact hl

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Arith.Lattices.Counting.ShiftedBallCount.shifted_limit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.Counting.ShiftedBallCount.shifted_limit.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.Counting.ShiftedBallCount.Limit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ c r => (centerCount c r : ℝ) / r ^ 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.Counting.ShiftedBallCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "fn", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

end

end Reg.D5.S3.Arith.Lattices.Counting.ShiftedBallCount
