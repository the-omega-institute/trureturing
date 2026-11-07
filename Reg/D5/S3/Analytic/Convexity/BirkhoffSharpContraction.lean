import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Convexity.BirkhoffSharpContraction
import Reg.Support.SingleDependentReadout

/-! A source-bound logarithmic readout of the maximal minor, on the complete rectangular family. -/

open _root_.D5.S3.Analytic.Convexity.BirkhoffSharpContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Set Real

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.Convexity.BirkhoffSharpContraction
universe u v

/-- The scalar observation is the logarithm of the maximal positive minor. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => log z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] {A : Matrix I J ℝ}, (∀ i j, 0 < A i j) →
    (∀ x : J → ℝ, Positive x → Positive (A *ᵥ x)) ∧
    IsLUB (imageDistances A) (r.readout () () (theta A)) ∧
    sSup (imageDistances A) = log (theta A) ∧
    IsLeast (coefficients A) (kappa A) ∧ 0 ≤ kappa A ∧ kappa A < 1

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let I := ULift.{u} Bool
  let J := ULift.{v} Bool
  let A : Matrix I J ℝ := fun i j => if i.down = j.down then 2 else 1
  have hA : ∀ i j, 0 < A i j := by intro i j; dsimp [A]; split_ifs <;> norm_num
  have hΘ : (4 : ℝ) ≤ theta A := by
    have hh := le_ciSup (f := fun p : I × I × J × J =>
      A p.1 p.2.2.1 * A p.2.1 p.2.2.2 /
        (A p.1 p.2.2.2 * A p.2.1 p.2.2.1)) (Set.finite_range _).bddAbove
      (ULift.up false, ULift.up true, ULift.up false, ULift.up true)
    simpa [A,theta,show (2 : ℝ) * 2 = 4 by norm_num] using hh
  have hlu := (@h I J _ _ _ _ A hA).2.1
  have heq : log (theta A) = 0 := (sharp_contraction hA).2.1.unique hlu
  have hpos : 0 < log (theta A) := log_pos (by linarith)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, exp 1, ?_⟩
  norm_num [actual,realize]

/-- The law keeps both universes and all degenerate finite fibers. -/
def family : Registration arena.{u,v} (type_of% (@sharp_contraction.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_contraction.{u,v},rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sharp_contraction.{u,v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Convexity.BirkhoffSharpContraction.unit
  realizationName := `Reg.D5.S3.Analytic.Convexity.BirkhoffSharpContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Convexity.BirkhoffSharpContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Convexity.BirkhoffSharpContraction
