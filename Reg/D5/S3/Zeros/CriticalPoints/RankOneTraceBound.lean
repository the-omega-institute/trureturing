import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.RankOneTraceBound
import Reg.Support.SingleDependentReadout

/-! Source-bound observation of the frequency in rotating-phase injectivity. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Rotating

open _root_.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ b => b + 1) (fun e => nomatch e)

/-- The original implication with only its final frequency occurrence observed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {u v : ℂ} {a b : ℝ} (hu : u ≠ 0)
    (h : ∀ y : ℝ, u * exp ((y : ℂ) * (a : ℂ) * I) =
      v * exp ((y : ℂ) * (b : ℂ) * I)),
      u = v ∧ a = R.readout () () b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (u := 1) (v := 1) (a := 0) (b := 0) one_ne_zero (by
    intro y
    rfl)
  have hh' : (0 : ℝ) = 0 + 1 := hh.2
  norm_num at hh'

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @rotating_phase_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rotating_phase_injective, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment.rotating_phase_injective)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Rotating.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Rotating.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneTraceBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Rotating

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Strip
open _root_.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex Complex.HadamardThreeLines
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℂ → ℂ) (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ f z => f z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ 1)
    (hright : ∀ z : ℂ, z.re = 1 → ‖f z‖ ≤ M),
    (∀ z ∈ verticalClosedStrip 0 1, ‖R.readout () f z‖ ≤ M ^ z.re) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → ‖f (θ : ℂ)‖ = M ^ θ →
        ∀ y : ℝ, ‖f (1 + (y : ℂ) * I)‖ = M)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (f := fun _ => 0) (M := 1) (by norm_num)
    (differentiable_const (0 : ℂ)).diffContOnCl
    (by refine ⟨0, ?_⟩; rintro x ⟨z, hz, rfl⟩; simp)
    (by intros; norm_num) (by intros; norm_num)).1 0 (by simp [verticalClosedStrip])
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨id, 0, 1, ?_⟩
  norm_num [actual, realize]
def source_registration : Registration arena (type_of% @strip_moment_bound_and_equality) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strip_moment_bound_and_equality, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@strip_moment_bound_and_equality) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Strip.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Strip.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f z => f z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneTraceBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Strip

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Trace
open _root_.D5.S3.Zeros.CriticalPoints.RankOneTraceBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Complex
open scoped ComplexConjugate
noncomputable section
abbrev signature.{u_1} : Signature where
  Params := Σ ι : Type u_1, ι → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ p j => p.2 j) (fun e => Empty.elim e)
def rejected.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => -1) (fun e => Empty.elim e)
def arena.{u_1,u_3} : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [Fintype ι] {n : Type u_3} [Fintype n] [DecidableEq n]
    (r : ι → EuclideanSpace ℂ n) (a : ι → ℝ) (γ : ι → ℂ)
    (ha : ∀ j, 0 ≤ a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ),
    ‖Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp))‖ ≤
        ∑ j, R.readout () ⟨ι, a⟩ j * ‖r j‖ ^ 2
private theorem rejected_law.{u_1,u_3} : ¬ arena.{u_1,u_3}.Law rejected := by
  intro h
  let r : ULift.{u_1} Unit → EuclideanSpace ℂ (ULift.{u_3} Unit) :=
    fun _ => EuclideanSpace.single ⟨()⟩ 1
  have hh := h r (fun _ => 1) (fun _ => 1)
    (by intro j; norm_num) (by intro j; norm_num) 1 (by simp)
  have hr : ∀ j, ‖r j‖ = 1 := by intro j; simp [r]
  have hnonneg := norm_nonneg (Matrix.trace ((1 : Matrix (ULift.{u_3} Unit) (ULift.{u_3} Unit) ℂ) *
    ∑ j : ULift.{u_1} Unit, (((1 : ℝ) : ℂ) * (1 : ℂ)) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp)))
  simp only [rejected, realize, hr, one_pow, mul_one, Fintype.sum_unique] at hh
  simp only [mul_one, Fintype.sum_unique] at hnonneg
  linarith
private theorem dependence.{u_1} : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Bool, fun j => if j.down then 1 else 0⟩, ⟨false⟩, ⟨true⟩, ?_⟩
  norm_num [actual, realize]
def source_registration.{u_1,u_3} : Registration arena.{u_1,u_3} (type_of% @norm_trace_rank_one_sum_le.{u_1,u_3}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_trace_rank_one_sum_le, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim (α := Unit) _ _)).elim,
    (by funext e; exact nomatch e), rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration.{u_1,u_3} : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norm_trace_rank_one_sum_le.{u_1,u_3}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Trace.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Trace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p j => p.2 j) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneTraceBound
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Trace

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Phase
open _root_.D5.S3.Zeros.CriticalPoints.RankOneTraceBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Complex
open scoped ComplexConjugate
noncomputable section
abbrev signature.{u_1} : Signature where
  Params := Σ ι : Type u_1, ι → ℂ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ p j => p.2 j) (fun e => Empty.elim e)
def rejected.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ p j => p.2 j + 1) (fun e => Empty.elim e)
def arena.{u_1,u_3} : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [Fintype ι] {n : Type u_3} [Fintype n] [DecidableEq n]
    (r : ι → EuclideanSpace ℂ n) (a : ι → ℝ) (γ : ι → ℂ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (hr : ∀ i j, inner ℂ (r i) (r j) ≠ 0)
    (heq : ‖Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp))‖ =
        ∑ j, a j * ‖r j‖ ^ 2), ∀ i j, γ i = R.readout () ⟨ι, γ⟩ j
private theorem rejected_law.{u_1,u_3} : ¬ arena.{u_1,u_3}.Law rejected := by
  intro h
  let r : ULift.{u_1} Unit → EuclideanSpace ℂ (ULift.{u_3} Unit) :=
    fun _ => EuclideanSpace.single ⟨()⟩ 1
  have hh := h r (fun _ => 1) (fun _ => 1)
    (by intro j; norm_num) (by intro j; norm_num) 1 (by simp)
    (by intro i j; simp [r, EuclideanSpace.inner_single_left])
    (by simp [r, Matrix.trace_vecMulVec, dotProduct, PiLp.single_apply])
    ⟨()⟩ ⟨()⟩
  norm_num [rejected, realize] at hh
private theorem dependence.{u_1} : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Bool, fun j => if j.down then 1 else 0⟩, ⟨false⟩, ⟨true⟩, ?_⟩
  norm_num [actual, realize]
def source_registration.{u_1,u_3} : Registration arena.{u_1,u_3} (type_of% @phases_eq_of_norm_trace_rank_one_sum_eq.{u_1,u_3}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨phases_eq_of_norm_trace_rank_one_sum_eq, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim (α := Unit) _ _)).elim,
    (by funext e; exact nomatch e), rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration.{u_1,u_3} : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@phases_eq_of_norm_trace_rank_one_sum_eq.{u_1,u_3}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Phase.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Phase.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p j => p.2 j) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneTraceBound
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.Phase

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.TraceIdentity
set_option linter.style.longLine false
set_option linter.unusedVariables true
set_option linter.unusedSimpArgs true
open _root_.D5.S3.Zeros.CriticalPoints.RankOneTraceBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
noncomputable section
universe u v
/-- Read the real weight as the complex coefficient in the trace expansion. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ a => (a : ℂ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ a => (a : ℂ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] {n : Type v} [Fintype n] [DecidableEq n]
    (r : ι → EuclideanSpace ℂ n) (a : ι → ℝ) (γ : ι → ℂ) (V : Matrix n n ℂ),
    Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp)) =
        ∑ j, R.readout () () (a j) * γ j * inner ℂ (r j) (V.toEuclideanLin (r j))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let r : ULift.{u} Unit → EuclideanSpace ℂ (ULift.{v} Unit) :=
    fun _ => EuclideanSpace.single ⟨()⟩ 1
  have hh := h r (fun _ => 0) (fun _ => 1) 1
  norm_num [rejected, realize, r, EuclideanSpace.inner_single_left,
    Matrix.toEuclideanLin, dotProduct] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @trace_rank_one_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_rank_one_sum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trace_rank_one_sum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.TraceIdentity.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.TraceIdentity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => (a : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneTraceBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print trace_rank_one_sum
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneTraceBound.TraceIdentity
