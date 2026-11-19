import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment

/-! The source-bound attainment audit preserves the original source universe,
both PSD outputs, the finite-value premise and the existential reverse test. -/

namespace Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment

open Matrix Set
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder MatrixOrder ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Unit
  State _ := EReal
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := EReal → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ left right => left = right) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : EReal) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hfalse

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type v} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (c : ℝ)
    (hc : originalL1Value.{u} hf A B = (c : EReal)),
    ∃ (k : ℕ) (R : ReverseTest A B k), r.readout () () (finiteCost hf R) (c : EReal)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let n := ULift.{v} Unit
  let hf : ConvexOn ℝ (Ioi 0) (fun _ : ℝ => (0 : ℝ)) :=
    convexOn_const 0 (convex_Ioi 0)
  let R : ReverseTest (0 : Matrix n n ℂ) 0 0 :=
    { p := Fin.elim0
      q := Fin.elim0
      p_nonneg := fun i => Fin.elim0 i
      q_nonneg := fun i => Fin.elim0 i
      state := Fin.elim0
      prepares_left := by simp
      prepares_right := by simp }
  have hm : maximalValue hf (0 : Matrix n n ℂ) 0 = 0 := by
    apply le_antisymm
    · exact sInf_le ⟨0, R, by simp [finiteCost]⟩
    · apply le_sInf
      rintro _ ⟨k, S, rfl⟩
      rw [finiteCost_eq_affine_remainder]
      simpa [affineMass] using EReal.coe_ennreal_nonneg
        (∑ i, curvatureRemainder hf (S.p i) (S.q i))
  have hc : originalL1Value.{u} hf (0 : Matrix n n ℂ) 0 = (0 : ℝ) := by
    rw [originalL1Value,
      _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest.sigma_finite_source_infimum_eq]
    exact hm
  obtain ⟨k, S, hS⟩ := h hf (0 : Matrix n n ℂ) 0
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero 0 hc
  exact hS

def source_registration : Registration arena.{u,v} (type_of% @original_finite_attainment.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_finite_attainment.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@original_finite_attainment.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment.unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment.source_registration
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
    owner := `D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "fn", "fn"]
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
end Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment
