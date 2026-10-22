import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter
open scoped BigOperators PowerSeries PowerSeries.WithPiTopology

namespace Reg.D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter

universe colourLevel
noncomputable section

structure Parameters where
  C : Type colourLevel
  finite : Fintype C

abbrev signature : Signature where
  Params := Parameters.{colourLevel}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{colourLevel} :=
  realize signature (fun _ parameter level => letI := parameter.finite
    PowerSeries.coeff level (character parameter.C)) (fun empty => nomatch empty)

def zeroReplacement : Realization signature.{colourLevel} :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{colourLevel}
  Law readout := ∀ (parameter : Parameters.{colourLevel}) (level : ℕ),
    readout.readout () parameter level =
      letI := parameter.finite
      PowerSeries.coeff level ((∏' frequency : ℕ,
        (1 - (PowerSeries.X : ℂ⟦X⟧) ^ (frequency + 1))⁻¹) ^ Fintype.card parameter.C)

def statement : Prop := ∀ (C : Type colourLevel) [Fintype C],
  character C = (∏' frequency : ℕ,
    (1 - (PowerSeries.X : ℂ⟦X⟧) ^ (frequency + 1))⁻¹) ^ Fintype.card C

theorem sourceReconstruction : statement.{colourLevel} ↔ arena.{colourLevel}.Law actual := by
  constructor
  · intro identity parameter level
    letI := parameter.finite
    exact congrArg (PowerSeries.coeff level) (identity parameter.C)
  · intro law C finite
    apply PowerSeries.ext
    intro level
    exact law ⟨C, finite⟩ level

theorem actualPositive : arena.{colourLevel}.Law actual := by
  intro parameter level
  letI := parameter.finite
  exact congrArg (PowerSeries.coeff level) (character_euler_product parameter.C)

theorem rejected : ¬ arena.{colourLevel}.Law zeroReplacement := by
  intro law
  have equation := law ⟨ULift.{colourLevel} Empty, inferInstance⟩ 0
  norm_num [zeroReplacement, realize] at equation

theorem dependence : ObservationalDependence signature.{colourLevel} actual := by
  intro role
  refine ⟨⟨ULift.{colourLevel} Empty, inferInstance⟩, 0, 1, ?_⟩
  intro equality
  simpa [actual, realize, character_euler_product] using equality

def source : Registration arena.{colourLevel} statement.{colourLevel} where
  actual := actual
  bridge := sourceReconstruction
  variation := ⟨actualPositive, zeroReplacement, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroReplacement, ?_, rfl, rejected⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := dependence

def registration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter.character_euler_product.{colourLevel})
    (Realization signature.{colourLevel}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter.sourceReconstruction
  realizationName := `Reg.D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter.source
  realizationSource := some `Reg.D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter.source
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨source⟩⟩
  options := #[]

end

end Reg.D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter
