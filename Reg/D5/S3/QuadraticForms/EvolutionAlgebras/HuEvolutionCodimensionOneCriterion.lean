import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.FinCases

open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion

/-- The complete seed vector, with its dimension-dependent coordinate type. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ Coord Coord

def actual : Realization signature := realize signature (fun _ _ c => c) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the literal Krylov seed occurrence is observed; the original product law is retained. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 1 ≤ m) (a : ℂ) (ha : a ≠ 0)
    (c : Coord m) (T : Matrix (Fin m) (Fin m) ℂ) (hT : T.det ≠ 0)
    (μ : Product (m+1)) (hl : ∀ x y, μ x y = codimOneProduct m a c T x y),
    minimalPerfect μ ↔
      let N := T - (a/2) • (1 : Matrix (Fin m) (Fin m) ℂ)
      N^m = 0 ∧ Matrix.det (fun i j : Fin m => ((N^j.val).mulVec (R.readout () m c)) i) ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨μ, hJ, hc, hp, hn, hs, hd⟩ := jordan_family 1 (by omega)
  have hl : ∀ x y, μ x y = codimOneProduct 1 4 (fun _ => 2) ((2 : ℂ) • 1) x y := by
    intro x y
    rw [hJ x y]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [jordanProduct, codimOneProduct]
    · simp only [codimOneProduct, Fin.cases_succ]
      fin_cases j
      simp [jordanProduct, Matrix.mulVec, dotProduct,
        Matrix.smul_apply, Matrix.one_apply]
      ring
  have he := (h 1 (by omega) 4 (by norm_num) (fun _ => 2) ((2 : ℂ) • 1)
    (by norm_num [Matrix.det_fin_one]) μ hl).mp hp
  apply he.2
  apply Matrix.det_eq_zero_of_column_eq_zero (0 : Fin 1)
  intro i
  simp [rejected, realize]

def source_registration : Registration arena (type_of% @codimension_one_criterion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨codimension_one_criterion, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, (fun _ => 1), ?_⟩
    intro h
    have hh := congr_fun h 0
    change (0 : ℂ) = 1 at hh
    exact zero_ne_one hh

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion.codimension_one_criterion)
    (Realization signature) (ℕ → Type) Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion.unit
  realizationName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion
end
