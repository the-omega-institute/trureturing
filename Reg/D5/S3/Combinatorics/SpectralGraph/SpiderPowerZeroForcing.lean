import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing

open _root_.D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing
open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The source's actual right-hand readout, with power order as parameter
and the existing natural subtraction operand as state. -/
abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ k n => n * k) (fun e => nomatch e)

/-- The law retains every original parameter and hypothesis. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m k ell : ℕ, 2 ≤ m → 1 ≤ k → k + 1 ≤ ell →
    zeroForcingNumber (power m k ell) = R.readout () k (m - 1)

abbrev assertion : Prop := ∀ m k ell : ℕ, 2 ≤ m → 1 ≤ k → k + 1 ≤ ell →
  zeroForcingNumber (power m k ell) = (m - 1) * k

def intervention : Realization signature := realize signature
  (fun _ k n => n * k + 1) (fun e => nomatch e)

theorem actual_law : arena.Law actual := result

theorem intervention_rejected : ¬ arena.Law intervention := by
  intro h
  have equality := h 2 1 2 (by decide) (by decide) (by decide)
  have positive := result 2 1 2 (by decide) (by decide) (by decide)
  simp [intervention, realize, positive] at equality

def familyRegistration : Registration arena assertion where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, intervention, intervention_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention, ?_, rfl, intervention_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    norm_num [actual, realize]

noncomputable def registration_result : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing.result)
    (type_of% (realize signature (fun _ k n => n * k) (fun e => nomatch e))) ℕ Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => n * k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration_result

end
end Reg.D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing
