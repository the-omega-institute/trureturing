import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily

/-- One dimension observation over all natural states; no complex domain is enumerated. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ x => 2*x+1) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original dependent telescope is retained, including all multiplication and subspace hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 1 ≤ m), ∃ μ : Product (m+1),
    jordanLaw m μ ∧ commutative μ ∧ minimalPerfect μ ∧ ¬ hasNaturalBasis μ ∧
    hasStableSquareEmbedding μ (R.readout () () m) ∧
    isEmbeddingDimension μ (R.readout () () m)


theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨μ, hL, hc, hp, hn, hs, hd⟩ := h 1 (by omega)
  obtain ⟨τ, hT, htc, htp, htn, hts, htd⟩ := jordan_family 1 (by omega)
  have heq : μ = τ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [hL x y, hT x y]
  have he : hasEvolutionEmbedding τ 1 := by
    rw [← heq]
    exact hd.1
  have h3 : 3 ≤ 1 := htd.2 1 he
  omega


def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨jordan_family, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily.jordan_family) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily.unit
  realizationName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 2*x+1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg", "arg"], booleanPredicate := false },
      { path := #["body", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
end
