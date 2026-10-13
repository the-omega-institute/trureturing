import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.HyperbolicPlaneRealization
import Reg.Support.DependentFamily

open scoped Matrix
open Set
open _root_.D5.S3.Geometry.Hyperideal.LengthGramBody
open _root_.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open _root_.D5.S3.Geometry.HyperbolicUpperHalfSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Geometry.HyperbolicPlaneRealization
noncomputable section

abbrev signature : Signature where
  Params := Fin 4 → ℝ
  State _ := UpperHalfPlane → HyperbolicThreeSpace
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set HyperbolicThreeSpace
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ e => range e) (fun i => nomatch i)
def rejected : Realization signature := realize signature (fun _ _ _ => ∅) (fun i => nomatch i)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : Fin 4 → ℝ), 0 < lorentz N N →
    ∃ e : UpperHalfPlane → HyperbolicThreeSpace, Isometry e ∧
      R.readout 0 N e = {p | lorentz (lift p) N = 0}

private def p0 : HyperbolicThreeSpace := ⟨⟨WithLp.toLp 2 ((0:ℂ),(1:ℝ)), by norm_num⟩⟩
private def p1 : HyperbolicThreeSpace := ⟨⟨WithLp.toLp 2 ((1:ℂ),(1:ℝ)), by norm_num⟩⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e,_,he⟩ := h ![0,1,0,0] (by norm_num [lorentz, Fin.sum_univ_succ])
  have hp : p0 ∈ {p : HyperbolicThreeSpace | lorentz (lift p) ![0,1,0,0] = 0} := by
    norm_num [p0,lift,lorentz,Fin.sum_univ_succ,height]
  rw [← he] at hp
  exact hp

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Geometry.HyperbolicPlaneRealization.supporting_plane_isometry,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨0,(fun _ => p0),(fun _ => p1),?_⟩
    intro heq
    have hp : p0 ∈ range (fun _ : UpperHalfPlane => p0) := ⟨UpperHalfPlane.I,rfl⟩
    change range (fun _ : UpperHalfPlane => p0) = range (fun _ : UpperHalfPlane => p1) at heq
    rw [heq] at hp
    obtain ⟨z,hz⟩ := hp
    have hh := congrArg (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.re) hz
    norm_num [p0,p1] at hh

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.HyperbolicPlaneRealization.supporting_plane_isometry)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ e => range e) (fun i => nomatch i)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.HyperbolicPlaneRealization.supporting_plane_isometry.range_unit,
  realizationName := `Reg.D5.S3.Geometry.HyperbolicPlaneRealization.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ e => range e) (fun i => nomatch i)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Geometry.HyperbolicPlaneRealization, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
namespace positive_time_of_pair
private def e3 : Fin 4 → ℝ := ![0,0,0,1]

abbrev signature : Signature where
  Params := Fin 4 → ℝ
  State _ := Fin 4 → ℝ
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ Y => Y 3) (fun i => nomatch i)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun i => nomatch i)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X Y : Fin 4 → ℝ),
    lorentz X X = -1 → lorentz Y Y = -1 →
    0 < X 3 → lorentz X Y < 0 → 0 < R.readout 0 X Y

theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hu : lorentz e3 e3 = -1 := by
    norm_num [e3, lorentz, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Pi.zero_apply]
  have ht : 0 < e3 3 := by norm_num [e3, Matrix.cons_val_three]
  have hp : lorentz e3 e3 < 0 := by rw [hu]; norm_num
  have hh := h e3 e3 hu hu ht hp
  norm_num [bad, realize] at hh

def mathematical : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair,
    bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨e3, (fun _ : Fin 4 => (0 : ℝ)), e3, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num

noncomputable def contract : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ Y => Y 3) (fun i => nomatch i)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair.observation_unit,
  realizationName := `Reg.D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair.mathematical,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨mathematical⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ Y => Y 3) (fun i => nomatch i)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.HyperbolicPlaneRealization,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms mathematical
#print axioms contract
end positive_time_of_pair

end
end Reg.D5.S3.Geometry.HyperbolicPlaneRealization
