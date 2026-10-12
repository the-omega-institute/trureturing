import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Matrix
open Set
open _root_.D5.S3.Geometry.Hyperideal.LengthGramBody
open _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open _root_.D5.S3.Geometry.HyperbolicUpperHalfSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
noncomputable section

abbrev signature : Signature where
  Params := Σ l : Fin 6 → ℝ, Σ _f : cutBody l → HyperbolicThreeSpace,
    Σ _lambda : cutBody l, cutBody l
  State p := Icc (0 : ℝ) (dist (p.2.1 p.2.2.1) (p.2.1 p.2.2.2)) → HyperbolicThreeSpace
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set HyperbolicThreeSpace
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ gamma => range gamma) (fun e => nomatch e)
def rejected (i : Fin 2) : Realization signature :=
  realize signature (fun j _ gamma => if j = i then ∅ else range gamma) (fun e => nomatch e)

/-- The two range observations vary independently; the entire original telescope,
actual metric, endpoints and isometry requirement remain unchanged. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (m : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hfinj : Function.Injective f)
    (hframe : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* m ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (lambda mu : cutBody l),
    ∃ gamma : Icc (0 : ℝ) (dist (f lambda) (f mu)) → HyperbolicThreeSpace,
      Isometry gamma ∧
      gamma ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = f lambda ∧
      gamma ⟨dist (f lambda) (f mu), ⟨dist_nonneg, le_rfl⟩⟩ = f mu ∧
      R.readout 0 ⟨l, f, lambda, mu⟩ gamma = {z | ∃ v : cutBody l,
        v.val ∈ segment ℝ lambda.val mu.val ∧ f v = z} ∧
      R.readout 1 ⟨l, f, lambda, mu⟩ gamma = {z | dist (f lambda) z + dist z (f mu) = dist (f lambda) (f mu)}

theorem rejected_law (i : Fin 2) : ¬ arena.Law (rejected i) := by
  intro h
  let l : Fin 6 → ℝ := fun _ => Real.log 2
  have hl : ∀ k, 0 < l k := fun _ => Real.log_pos (by norm_num)
  obtain ⟨_,hbar,_,_,_,_,_,_,_,hreal⟩ := shared_radial_body l hl
  have hc : Real.cosh (Real.log 2) = 5/4 := by
    rw [Real.cosh_log (by norm_num)]
    norm_num
  have heval : cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
      (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) = 5/6 := by
    simp only [l,hc,cosine,numerator,rad]
    norm_num
    rw [div_div, div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 243),
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 32)]
    norm_num
  obtain ⟨m,_,_,_,f,_,hfinj,_,_,hframe⟩ := hreal (by rw [heval]; norm_num)
  let v : cutBody l := ⟨_,hbar⟩
  obtain ⟨gamma,_,_,_,hrange,hbetween⟩ := h l hl m f hfinj hframe v v
  have hmem : f v ∈ {z | ∃ u : cutBody l, u.val ∈ segment ℝ v.val v.val ∧ f u = z} :=
    ⟨v,left_mem_segment ℝ _ _,rfl⟩
  fin_cases i
  · rw [← hrange] at hmem
    exact hmem
  · have hb : f v ∈ {z | dist (f v) z + dist z (f v) = dist (f v) (f v)} := by simp
    rw [← hbetween] at hb
    exact hb

private def p0 : HyperbolicThreeSpace := ⟨⟨WithLp.toLp 2 ((0:ℂ),(1:ℝ)), by norm_num⟩⟩
private def p1 : HyperbolicThreeSpace := ⟨⟨WithLp.toLp 2 ((1:ℂ),(1:ℝ)), by norm_num⟩⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.same_body_metric_segments,
    rejected 0,rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_law i⟩
      intro j h
      simp [actual,rejected,realize,h]
    · intro i; exact nomatch i
  dependence := by
    intro i
    let l : Fin 6 → ℝ := fun _ => 1
    let v : cutBody l := ⟨_, (shared_radial_body l (fun _ => by norm_num [l])).2.1⟩
    let p : signature.Params := ⟨l, (fun _ => p0), v, v⟩
    refine ⟨p,(fun _ => p0),(fun _ => p1),?_⟩
    intro heq
    have hmem : p0 ∈ range (fun _ : Icc (0:ℝ) (dist p0 p0) => p0) :=
      ⟨⟨0,le_rfl,dist_nonneg⟩,rfl⟩
    change range (fun _ : Icc (0:ℝ) (dist p0 p0) => p0) =
      range (fun _ : Icc (0:ℝ) (dist p0 p0) => p1) at heq
    rw [heq] at hmem
    obtain ⟨t,ht⟩ := hmem
    have hh := congrArg (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.re) ht
    norm_num [p0,p1] at hh


noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.same_body_metric_segments)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ gamma => range gamma) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.same_body_metric_segments.range_unit,
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ gamma => range gamma) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Geometry.Hyperideal.LengthGramMetricSegments, definition := none, coordinates := #[0, 3, 6, 7], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end
end Reg.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
