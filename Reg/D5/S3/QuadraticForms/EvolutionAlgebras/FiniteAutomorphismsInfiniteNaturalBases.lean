import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.EvolutionAlgebras.FiniteAutomorphismsInfiniteNaturalBases
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.FiniteAutomorphismsInfiniteNaturalBases

open LeanInformationAudit
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.FiniteAutomorphismsInfiniteNaturalBases
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ), ℂ × ℂ)
    (fun _ => ℂ × ℂ) (fun _ => ℂ × ℂ)

def actual : Realization signature :=
  realize signature (fun _ p y => p.1 p.2 y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the annihilator's product observation is varied. All other source
clauses and their shared existential multiplication remain in the Law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ μ : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ),
    Module.finrank ℂ (ℂ × ℂ) = 2 ∧
    (∀ x y, μ x y = μ y x) ∧
    (∀ x, (∀ y, R.readout () ⟨μ, x⟩ y = 0) → x = 0) ∧
    Nonempty (NaturalBasis μ) ∧
    Finite (Aut μ) ∧ Infinite (Quotient (basisSetoid μ))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨μ, _, _, h, _⟩
  have hz := h (1, 0) (fun _ => rfl)
  have := congrArg Prod.fst hz
  norm_num at this

def source_registration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨mu, (1, 0)⟩, 0, (1, 0), ?_⟩
    intro h
    have := congrArg Prod.fst h
    change (1 * 0 + 0 * 0 : ℂ) = 1 * 1 + 0 * 0 at this
    norm_num at this

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (type_of% actual) Unit Unit := {
  unitName := Lean.Name.str ``result "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => p.1 p.2 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.EvolutionAlgebras.FiniteAutomorphismsInfiniteNaturalBases
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "fn", "arg", "body", "domain", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.FiniteAutomorphismsInfiniteNaturalBases
