import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Nonlinear actual-L2 observations with the full normal-contraction telescope. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup
  (contractLp actual_trace_contraction)
open BiasedBoundaryTrace (G M)
open BiasedBoundaryPathSplit (constG boundary_path_split)
open BiasedBoundaryFreeRootForm (D energy)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Filter

abbrev Maps := {χ : ℝ → ℝ // LipschitzWith 1 χ}
abbrev signature : Signature where
  Params := Maps
  State _ := D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ χ F => contractLp χ.val χ.property F.val) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) (F : D),
    (R.readout () ⟨χ,hχ⟩ F =ᵐ[M] (fun ω => χ (F.val ω))) ∧
    R.readout () ⟨χ,hχ⟩ F ∈ D ∧ energy (R.readout () ⟨χ,hχ⟩ F) ≤ energy F.val

def rejected : Realization signature :=
  realize signature (fun _ _ _ => constG 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : LipschitzWith 1 (fun _ : ℝ => (0 : ℝ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp
  have he := (h (fun _ => 0) hz ⟨0,D.zero_mem⟩).1
  have hc := boundary_path_split.2.2.2.1 1
  obtain ⟨ω,hω⟩ := (he.and hc).exists
  change (constG 1) ω = 0 ∧ (constG 1) ω = 1 at hω
  linarith [hω.1,hω.2]

def familyRegistration : Registration arena (type_of% actual_trace_contraction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_trace_contraction,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    let χ : Maps := ⟨id, LipschitzWith.id⟩
    let F : D := ⟨0,D.zero_mem⟩
    let V : D := ⟨constG 1,1,0,by simp⟩
    refine ⟨χ,F,V,?_⟩
    have hi (U : D) : contractLp id LipschitzWith.id U.val = U.val :=
      Lp.ext ((actual_trace_contraction id LipschitzWith.id U).1)
    change contractLp id LipschitzWith.id F.val ≠ contractLp id LipschitzWith.id V.val
    rw [hi F,hi V]
    intro he
    have hm := congrArg BiasedBoundaryCentering.mean he
    change BiasedBoundaryCentering.mean 0 = BiasedBoundaryCentering.mean (constG 1) at hm
    rw [map_zero,BiasedBoundaryCentering.centered_suffix_residual.2.1] at hm
    norm_num at hm

/-- Typed family evidence; raw source occurrence selection is not supplied. -/
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_trace_contraction)
    (type_of% (realize signature (fun _ χ F => contractLp χ.val χ.property F.val) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ χ F => contractLp χ.val χ.property F.val) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup
