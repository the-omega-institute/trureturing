import Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
import D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport

/-! The equality readout retains the original source telescope and the actual
matrix-valued curvature-support criterion. -/

namespace Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport

open Matrix MeasureTheory Set
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickLoewnerSlopes
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type v} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : originalL1Value.{u} hf A B = (c : EReal)),
    r.readout () () (originalL1Value.{u} hf A B) (originalHockeyValue.{u} hf A B) ↔
      FiniteLoewnerSlopes A B hA hB (curvature hf).support

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let hf : ConvexOn ℝ (Ioi 0) (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 (convex_Ioi 0)
  let Z : Matrix (ULift.{v} Empty) (ULift.{v} Empty) ℂ := 0
  have hZ : Z.PosSemidef := Matrix.PosSemidef.zero
  have ho (t : PositiveThreshold) : overlapValue Z ((t : ℝ) • Z) = 0 := by
    have hs := (optimalOverlap_spec Z Z hZ hZ t t.2.le).2
    simpa only [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re] using hs.symm
  have ho0 : overlapValue (0 : Matrix (ULift.{v} Empty) _ ℂ) 0 = 0 := by
    simpa only [Z, smul_zero] using ho ⟨1, zero_lt_one⟩
  have hH : hockeyValue hf Z Z = 0 := by
    simp [hockeyValue, affineMass, maximalKernel, maximalHockey, Z, ho0]
  have hcomm : let S := Z + Z
      let C := _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickSupport.normalize S Z
      let P := _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral.interiorProjection C
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by simp [Z]
  have he := commute_implies_original_eq.{u} hf Z Z hZ hZ hcomm
  have hop := (hockeyValue_eq_original_operational.{u} hf Z Z hZ hZ).1
  have hc : originalL1Value.{u} hf Z Z = ((0 : ℝ) : EReal) :=
    he.trans (hop.symm.trans hH)
  have hcriterion := (original_eq_iff_finiteLoewnerSlopes.{u} hf Z Z hZ hZ 0 hc).1 he
  exact ((h hf Z Z hZ hZ 0 hc).2 hcriterion) he

def source_registration : Registration arena.{u,v}
    (type_of% @original_eq_iff_finiteLoewnerSlopes.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_eq_iff_finiteLoewnerSlopes.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := Identification.source_registration.{u,v}.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@original_eq_iff_finiteLoewnerSlopes.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport.unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ left right => left = right) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport
