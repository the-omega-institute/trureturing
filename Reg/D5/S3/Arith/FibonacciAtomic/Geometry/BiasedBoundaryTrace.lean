import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The actual boundary operator as the readout of the full Hardy family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (Edge H P)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass (a)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory hiding cylinder
open scoped ENNReal

abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ z => J z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ z : H, HasSum (fun p : Edge => z p • indicator p) (R.readout () () z)) ∧
    (∀ (h : ℕ) (z : H), ‖R.readout () () (z-P h z)‖^2 ≤
      (a^(h+1)/(1-a))*‖z‖^2)

private def leftEdge : Edge := ⟨[false], by simp⟩

private theorem indicator_ne_zero : indicator leftEdge ≠ 0 := by
  have hm : M.real (cylinder leftEdge.val) = a := by
    change (M (cylinder [false])).toReal = a
    rw [M, cylinder, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp only [List.length_singleton, Finset.prod_range_one, List.getD_cons_zero]
    change bit.real {false} = a
    exact ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem _
      (measurableSet_singleton false) (by simp) (by simp)
  intro he
  have hn := congrArg norm he
  rw [indicator, norm_indicatorConstLp (by norm_num) (by norm_num), hm] at hn
  have hp : 0 < a := inv_pos.mpr Real.goldenRatio_pos
  have := Real.rpow_pos_of_pos hp (1 / (2 : ℝ≥0∞).toReal)
  exact (ne_of_gt this) (by simpa only [norm_one, one_mul, norm_zero] using hn)

def rejected : Realization signature :=
  realize signature (fun _ _ z => J z + indicator leftEdge) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1 (0 : H)
  simp only [lp.coeFn_zero, Pi.zero_apply, zero_smul] at hh
  have hz : HasSum (fun _ : Edge => (0 : G)) 0 := hasSum_zero
  have he := hh.unique hz
  simp only [rejected, realize, map_zero, zero_add] at he
  exact indicator_ne_zero he

private theorem single_trace : J (lp.single 2 leftEdge (1 : ℝ)) = indicator leftEdge := by
  let z : H := lp.single 2 leftEdge (1 : ℝ)
  change J z = indicator leftEdge
  have he : (fun p : Edge => z p • indicator p) =
      (fun p : Edge => if p = leftEdge then indicator leftEdge else 0) := by
    funext p
    change Pi.single (M := fun _ : Edge => ℝ) leftEdge (1 : ℝ) p • indicator p = _
    by_cases hp : p = leftEdge
    · subst p
      simp
    · rw [Pi.single_eq_of_ne hp]
      simp [hp]
  have hs := boundary_trace_hardy.1 z
  rw [he] at hs
  exact hs.unique (hasSum_ite_eq leftEdge (indicator leftEdge))

/-- The full all-vector convergence and Hardy family, with the actual boundary map as readout. -/
def familyRegistration : Registration arena (type_of% boundary_trace_hardy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨boundary_trace_hardy, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : H), lp.single 2 leftEdge (1 : ℝ), ?_⟩
    change J 0 ≠ J (lp.single 2 leftEdge (1 : ℝ))
    rw [map_zero, single_trace]
    exact indicator_ne_zero.symm

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.boundary_trace_hardy)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ z => J z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.hardyUnit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ z => J z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
