import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Actual normalized cylinder means in the full projection family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (Omega M G cylinder indicator)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG boundary_path_split)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (mean)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw (pullback conditional_pullback_law)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (Edge)
open _root_.D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory

abbrev signature : Signature where
  Params := Edge
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p F => atomMean p F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Finset Edge), IsPrefixFree (Subtype.val '' (A : Set Edge)) →
    (∀ (p : Edge) (F : G), R.readout () p F =
      (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, F ω ∂M) ∧
    (∀ (p : Edge) (F : G), R.readout () p F = mean (pullback p.val F)) ∧
    (∀ F : G, Q A F = (V A).starProjection F) ∧
    (∀ p ∈ A, Q A (indicator p) = indicator p)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

private def edge : Edge := ⟨[false], by simp⟩

private theorem normalized_one (p : Edge) :
    (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, constG 1 ω ∂M = 1 := by
  rw [integral_congr_ae (ae_restrict_of_ae (boundary_path_split.2.2.2.1 (1 : ℝ)))]
  rw [integral_const]
  simp only [smul_eq_mul, mul_one]
  exact inv_mul_cancel₀
    (ENNReal.toReal_pos (conditional_pullback_law.1 p.val) (measure_ne_top _ _)).ne'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h ∅ (by simp [IsPrefixFree])).1 edge (constG 1)
  change (0 : ℝ) = _ at he
  rw [normalized_one] at he
  norm_num at he

def familyRegistration : Registration arena (type_of% cylinder_average_projection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cylinder_average_projection, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨edge, (0 : G), constG 1, ?_⟩
    change atomMean edge 0 ≠ atomMean edge (constG 1)
    rw [map_zero, (cylinder_average_projection ∅ (by simp [IsPrefixFree])).1,
      normalized_one]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cylinder_average_projection)
    (type_of% (realize signature (fun _ p F => atomMean p F) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.unit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p F => atomMean p F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
