import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation

/-! Source binding for the lower endpoint of the distance-eigenvalue interval. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ε => -2 - ε) (fun e => nomatch e)

def collapsed : Realization signature :=
  realize signature (fun _ _ _ => -2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε →
    ∃ r : ℕ, 0 < r ∧ ∃ lam : ℝ, R.readout () () ε < lam ∧ lam < -2 ∧
      (family r).Connected ∧ P4Free (family r) ∧
      Module.End.HasEigenvalue (distanceMatrix (family r)).mulVecLin lam

private theorem collapsed_fails : ¬ arena.Law collapsed := by
  intro h
  obtain ⟨_, _, lam, hlower, hupper, _⟩ := h 1 (by norm_num)
  change (-2 : ℝ) < lam at hlower
  exact (not_lt_of_ge hupper.le) hlower

def familyRegistration : Registration arena (type_of% @registered_family_counters_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨registered_family_counters_gap, collapsed, collapsed_fails⟩
  sensitivity := by
    constructor
    · intro _
      refine ⟨collapsed, ?_, rfl, collapsed_fails⟩
      intro _ h
      exact (h rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change (-2 : ℝ) - 1 ≠ -2 - 2
    norm_num

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@registered_family_counters_gap) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation.registered_family_counters_gap.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ ε => -2 - ε) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation
