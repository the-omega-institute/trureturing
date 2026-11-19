import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.ULift

/-! The observed endomorphism retains its arbitrary source group and full source law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity

universe u

/-- Group dictionaries are fixed background; the original endomorphism is data. -/
abbrev Inputs := Σ G : Type u, Σ group : Group G, (letI := group; G →* G)

abbrev signature : Signature where
  Params := Inputs.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => by
    letI := p.2.1
    exact 1) (fun e => nomatch e)

/-- All source hypotheses remain premises, and injectivity ranges over all elements. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {G : Type u} [group : Group G] [Group.FG G]
    [Group.ResiduallyFinite G] {f : G →* G} (_hf : Function.Surjective f),
    Function.Injective (r.readout () ⟨G, group, f⟩)

theorem actual_law : arena.{u}.Law actual := by
  exact @surjective_endomorphism_injective.{u}

/-- One parameter in the full family, rather than a restriction of its source types. -/
def sample : Inputs.{u} :=
  ⟨ULift.{u} (Multiplicative (ZMod 2)), inferInstance, MonoidHom.id _⟩

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (G := ULift.{u} (Multiplicative (ZMod 2)))
    (f := MonoidHom.id _) Function.surjective_id
    (ULift.up (Multiplicative.ofAdd 0))
    (ULift.up (Multiplicative.ofAdd 1)) (by rfl)
  have hz : (0 : ZMod 2) = 1 :=
    congrArg (fun z : ULift.{u} (Multiplicative (ZMod 2)) =>
      Multiplicative.toAdd z.down) he
  exact zero_ne_one hz

theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨sample, ULift.up (Multiplicative.ofAdd 0),
    ULift.up (Multiplicative.ofAdd 1), ?_⟩
  change (ULift.up (Multiplicative.ofAdd (0 : ZMod 2)) :
    ULift.{u} (Multiplicative (ZMod 2))) ≠ ULift.up (Multiplicative.ofAdd 1)
  intro he
  have hz : (0 : ZMod 2) = 1 :=
    congrArg (fun z : ULift.{u} (Multiplicative (ZMod 2)) =>
      Multiplicative.toAdd z.down) he
  exact zero_ne_one hz

def source_registration : Registration arena.{u}
    (type_of% @surjective_endomorphism_injective.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@surjective_endomorphism_injective.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity.unit
  realizationName :=
    `Reg.D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => p.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity

end
