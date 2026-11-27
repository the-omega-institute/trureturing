import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope

/-! The strict comparison in the scalar CAR envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope

local notation "certificateSpectrum" =>
  _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope.spectrum

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {w : Fin 4 → Fin 4 → ℝ} {e : Fin 4 → ℝ} {m : ℝ},
    CARConstraints certificateSpectrum w e m →
    R.readout () () (1 / 8000) (4 * Real.cosh temperature / 9 *
      (cubicEnergy w - sharpCoefficient * relativeEntropy m))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let w : Fin 4 → Fin 4 → ℝ := ![![0, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]]
  let e : Fin 4 → ℝ := ![1, 0, 0, 1]
  let m := certificateSpectrum 3 - certificateSpectrum 0
  have hw : CARConstraints certificateSpectrum w e m := by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [w]
    · intro i
      fin_cases i <;> norm_num [Fin.sum_univ_four, sym, w]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num [sym, w]
    · intro i
      fin_cases i <;> norm_num [w, e]
    · intro i
      fin_cases i <;> norm_num [Set.mem_Icc, e]
    · norm_num [Fin.sum_univ_four, e]
    · norm_num [orientationMoment, edgeSum, w, m]
      ring
    · intro v
      norm_num [Fin.sum_univ_four, e]
      rw [show m = (certificateSpectrum 3 - v) + (v - certificateSpectrum 0) by dsimp [m]; ring]
      simpa only [abs_sub_comm v (certificateSpectrum 0), add_comm] using
        abs_add_le (certificateSpectrum 3 - v) (v - certificateSpectrum 0)
  exact (lt_asymm (cubic_deficit_gt hw)) (h hw)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (lt_irrefl (1 : ℝ)) (Eq.mp (congrFun h 1) (by norm_num : (0 : ℝ) < 1))

def family : Registration arena (type_of% @cubic_deficit_gt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cubic_deficit_gt, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cubic_deficit_gt) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope.cubic_deficit_gt.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope
