import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
import Reg.Support.DependentFamily

open MeasureTheory ProbabilityTheory Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.CategoricalProductPoisson

open scoped NNReal
noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
universe u

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := ⟨{⟨()⟩}, fun x => by
    have hx : x = ⟨()⟩ := Subsingleton.elim _ _
    simp only [hx, Finset.mem_singleton]⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (a : J → ℝ≥0) (ha : ∑ j, (a j : ℝ) ≤ 1) (s : ℕ) (E : Set (J → ℕ)),
    R.readout ⟨()⟩ () ((independentSumLaw (categoricalIncrement a) s).real E -
      (Measure.pi (fun j => poissonMeasure (s * a j))).real E) ≤
        s * (∑ j, (a j : ℝ)) ^ 2

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (J := ULift.{u} Empty) (fun x => nomatch x.down) (by simp) 0 ∅
  norm_num [rejected, realize] at hh

def family : Registration arena.{u} (type_of% (@categorical_product_poisson.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@categorical_product_poisson, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change |(0 : ℝ)| ≠ |(1 : ℝ)|
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@categorical_product_poisson.{u})
    (type_of% (realize signature.{u} (fun _ _ x => |x|) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Estimation.TimeArrow.CategoricalProductPoisson.categorical_product_poisson.__information_unit
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.CategoricalProductPoisson.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
