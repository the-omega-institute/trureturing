import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Full simultaneous finite-source norm telescope on the original edge space. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry
open FiniteSourceCovariance (v B Sigma finite_source_covariance_convergence)
open FiniteSourceHardy (H Edge)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open InnerProductSpace MeasureTheory
open scoped ENNReal

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H × (H →L[ℝ] H) × (H →L[ℝ] H)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => (v n, B n, Sigma n)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ‖(R.readout () () n).1-BiasedBoundaryFreeRootForm.v‖ < ε ∧
    ‖(R.readout () () n).2.1-BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J‖ < ε ∧
    ‖(R.readout () () n).2.2-BiasedBoundaryFreeRootForm.Sigma‖ < ε

private def edge : Edge := ⟨[false], by simp⟩
private def unitEdge : H := lp.single 2 edge 1

def rejected : Realization signature :=
  realize signature (fun _ _ _ =>
    (BiasedBoundaryFreeRootForm.v+unitEdge,
     BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J,
     BiasedBoundaryFreeRootForm.Sigma)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N,hN⟩ := h (1/2) (by norm_num)
  have he := (hN N le_rfl).1
  change ‖BiasedBoundaryFreeRootForm.v+unitEdge-BiasedBoundaryFreeRootForm.v‖ < (1:ℝ)/2 at he
  simp only [add_sub_cancel_left] at he
  rw [show ‖unitEdge‖ = 1 by
    simp [unitEdge, lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)]] at he
  norm_num at he

private theorem J_zero : FiniteSourceHardy.J 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  change FiniteSourceHardy.trace 0 0 z = 0
  unfold FiniteSourceHardy.trace
  rw [← MemLp.toLp_zero (MemLp.zero : MemLp (0 : FiniteSourceMass.Node 0 → ℝ) 2 (FiniteSourceMass.μ 0))]
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro x
  have he : FiniteSourceHardy.edges 0 = ∅ := by
    ext p
    simp [FiniteSourceHardy.edges, FiniteSourceMass.vertices,
      ActualTreeReadoutAcquisition.nodes, AncestorAreaInstability.T, p.property]
  simp [FiniteSourceHardy.value, FiniteSourceHardy.path, he]

private theorem boundary_mean_ne_zero : BiasedBoundaryFreeRootForm.v ≠ 0 := by
  intro hz
  have he : inner ℝ unitEdge BiasedBoundaryFreeRootForm.v = FiniteSourceMass.a := by
    rw [BiasedBoundaryFreeRootForm.v, ContinuousLinearMap.adjoint_inner_right]
    unfold unitEdge
    rw [BiasedBoundaryTrace.J_single, one_smul, real_inner_comm]
    change BiasedBoundaryCentering.mean (BiasedBoundaryTrace.indicator edge) = _
    rw [BiasedBoundaryCentering.centered_suffix_residual.1]
    rw [BiasedBoundaryTrace.indicator, MeasureTheory.integral_indicatorConstLp]
    simpa [measureReal_def, edge, BiasedBoundaryTrace.mass] using
      BiasedBoundaryTrace.cylinder_mass edge.val
  rw [hz, inner_zero_right] at he
  exact (ne_of_gt BiasedBoundaryTrace.a_pos) he.symm

def familyRegistration : Registration arena (type_of% finite_source_covariance_convergence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_source_covariance_convergence, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    have hp := norm_pos_iff.mpr boundary_mean_ne_zero
    obtain ⟨N,hN⟩ := finite_source_covariance_convergence
      (‖BiasedBoundaryFreeRootForm.v‖/2) (by positivity)
    refine ⟨(), 0, N, ?_⟩
    intro he
    have hv : v 0 = v N := congrArg Prod.fst he
    have hz : v 0 = 0 := by simp [v, J_zero]
    have he := (hN N le_rfl).1
    rw [← hv, hz, zero_sub, norm_neg] at he
    linarith

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_source_covariance_convergence)
    (type_of% (realize signature (fun _ _ n => (v n, B n, Sigma n)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => (v n, B n, Sigma n)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance
