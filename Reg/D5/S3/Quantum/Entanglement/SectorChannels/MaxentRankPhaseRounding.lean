import D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
open scoped BigOperators
namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding
open _root_.D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => ℕ → ℝ → (ℕ → ℝ) → ℝ)

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ K => packingError K) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ K : ℕ, let observed := R.readout () () K; PhaseLaw K observed

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, _, _, _, hD, hEq⟩ := (h 1).2 (by decide) 1 (by norm_num)
  have hz := mul_pos (show ((1 : ℝ)+1)/(2*1+1)>0 by norm_num) hD
  change _ = (0 : ℝ) at hEq
  exact (ne_of_gt hz) (by simpa only [Nat.cast_one] using hEq)

private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 1 := by
  obtain ⟨c, hc, _, _, hD, hEq⟩ := (phase_rounding 1).2 (by decide) 1 (by norm_num)
  have hpos : 0 < packingError 1 4 1 c := by
    change _ = packingError 1 4 1 c at hEq
    rw [← hEq]
    exact mul_pos (by norm_num) hD
  have hzero : packingError 0 4 1 c = 0 := by
    unfold packingError
    have hg : RTMaxentRounding.sums (fun i => (RTMaxentRounding.greedyAt c 0 i)^2) 4 = 0 := by
      unfold RTMaxentRounding.sums
      apply Finset.sum_eq_zero
      intro i hi
      have hip : i < 4 := Finset.mem_range.mp hi
      have hsum : 0 ≤ RTMaxentRounding.sums c i := by
        apply Finset.sum_nonneg
        intro j hj
        exact (hc j (by have := Finset.mem_range.mp hj; omega)).1
      unfold RTMaxentRounding.greedyAt
      rw [max_eq_left (by linarith),min_eq_right (hc i hip).1]
      norm_num
    rw [Nat.cast_zero,hg]
    norm_num
  intro bad
  have hbad := congrFun (congrFun (congrFun bad 4) 1) c
  change packingError 0 4 1 c = packingError 1 4 1 c at hbad
  exact (ne_of_gt hpos) (hbad.symm.trans hzero)

noncomputable def family : Registration arena (type_of% @phase_rounding) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨phase_rounding,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, actual_dependence⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@phase_rounding) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding.phase_rounding.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
      owner := `D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding
      definition := none
      coordinates := #[]
      readouts := #[{
        path := #["body","value"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding
