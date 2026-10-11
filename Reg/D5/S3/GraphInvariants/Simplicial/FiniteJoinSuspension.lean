import LeanInformationAuditInterface.Contract.Registration
import D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension
import Reg.Support.DependentFamily

namespace Reg.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension

open _root_.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Set Finset
universe u
noncomputable section

structure Params where
  vertices : Type u
  finite : Fintype vertices
  decidable : DecidableEq vertices
  complex : PreAbstractSimplicialComplex vertices

abbrev State (p : Params.{u}) :=
  @GeometricRealization p.vertices p.finite p.decidable p.complex × Height

abbrev Output (p : Params.{u}) : Type u :=
  letI := p.finite
  letI := p.decidable
  GeometricRealization (join p.complex D2)

abbrev signature : Signature :=
  { Params := Params
    State := State
    Role := Unit
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ => Output
    Anchor := Empty
    finiteAnchor := inferInstance }

def actual : Realization signature :=
  realize signature (fun _ p x => @suspensionMap p.vertices p.finite p.decidable p.complex x)
    (fun e => nomatch e)

/-- A genuine pole in the usual polyhedron, for every base precomplex. -/
def north (p : Params.{u}) : Output p := by
  letI := p.finite
  letI := p.decidable
  refine ⟨Pi.single (Sum.inr (0 : Fin 2)) (1 : ℝ), ?_⟩
  refine ⟨{Sum.inr (0 : Fin 2)}, ?_, ?_⟩
  · change ({Sum.inr (0 : Fin 2)} : Finset (p.vertices ⊕ Fin 2)).Nonempty ∧
      (_ = ∅ ∨ _ ∈ p.complex) ∧ (_ = ∅ ∨ _ ∈ D2)
    refine ⟨singleton_nonempty _, ?_, ?_⟩
    · left; ext i; simp
    · right
      change ∃ j, ({Sum.inr (0 : Fin 2)} : Finset (p.vertices ⊕ Fin 2)).toRight = {j}
      exact ⟨0, by ext j; simp⟩
  · exact subset_convexHull ℝ _ ⟨Sum.inr 0, mem_singleton_self _, rfl⟩

def rejected : Realization signature :=
  realize signature (fun _ p _ => north p) (fun e => nomatch e)

/-- The original finite telescope, with only the geometric map readout replaced. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (p q : GeometricRealization K × Height),
    R.readout () ⟨ι, fi, de, K⟩ p = R.readout () ⟨ι, fi, de, K⟩ q ↔
      (suspensionSetoid (GeometricRealization K)).r p q

def statement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (p q : GeometricRealization K × Height),
    suspensionMap p = suspensionMap q ↔ (suspensionSetoid (GeometricRealization K)).r p q

abbrev TestVertices := ULift.{u} Unit

def testBase : @GeometricRealization TestVertices inferInstance inferInstance ⊤ :=
  ⟨Pi.single ⟨()⟩ (1 : ℝ),
    ⟨{⟨()⟩}, singleton_nonempty _, subset_convexHull ℝ _
      ⟨⟨()⟩, mem_singleton_self _, rfl⟩⟩⟩

def lower : Height := ⟨-1, by constructor <;> norm_num⟩
def upper : Height := ⟨1, by constructor <;> norm_num⟩

theorem rejected_law : ¬ arena.Law (rejected : Realization signature.{u}) := by
  intro h
  have hrel := (@h TestVertices inferInstance inferInstance ⊤
    (testBase, lower) (testBase, upper)).mp rfl
  have heq : (-1 : ℝ) = 1 := congrArg Subtype.val hrel.1
  norm_num at heq

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨TestVertices, inferInstance, inferInstance, ⊤⟩,
    (testBase, lower), (testBase, upper), ?_⟩
  intro heq
  have hrel := (suspensionMap_fibres (⊤ : PreAbstractSimplicialComplex TestVertices)
    (testBase, lower) (testBase, upper)).mp heq
  have he : (-1 : ℝ) = 1 := congrArg Subtype.val hrel.1
  norm_num at he

def registration : Registration arena.{u} statement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(by
    intro ι fi de K p q
    exact @suspensionMap_fibres ι fi de K p q), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@suspensionMap_fibres.{u})
    (type_of% (realize signature.{u}
      (fun _ p x => @suspensionMap p.vertices p.finite p.decidable p.complex x)
      (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension
      "suspensionMap_fibres") "__information_unit",
  realizationName := `Reg.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p x => @suspensionMap p.vertices p.finite p.decidable p.complex x)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 4,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 5,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension

namespace Reg.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension.CarrierMembership

open _root_.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Set Finset
universe u
noncomputable section

structure Params where
  vertices : Type u
  finite : Fintype vertices
  decidable : DecidableEq vertices

abbrev State (p : Params.{u}) := PreAbstractSimplicialComplex p.vertices

abbrev signature : Signature :=
  { Params := Params
    State := State
    Role := Unit
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ p => Set (p.vertices → ℝ)
    Anchor := Empty
    finiteAnchor := inferInstance }

def actual : Realization signature :=
  realize signature (fun _ p K => @geometricCarrier p.vertices p.finite p.decidable K)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

/-- The original coordinate criterion, replacing only its geometric-carrier readout. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {x : ι → ℝ},
    x ∈ R.readout () ⟨ι, fi, de⟩ K ↔
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧ support x ∈ K

def statement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {x : ι → ℝ},
    x ∈ geometricCarrier K ↔
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧ support x ∈ K

theorem rejected_law : ¬ arena.Law (rejected : Realization signature.{u}) := by
  intro h
  have hc := (@h (ULift.{u} Unit) inferInstance inferInstance ⊥ (fun _ => 0)).mp
    (Set.mem_univ _)
  simpa using hc.2.1

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let ι := ULift.{u} Unit
  let v : ι := ⟨()⟩
  refine ⟨⟨ι, inferInstance, inferInstance⟩, ⊤, ⊥, ?_⟩
  intro heq
  have hx : Pi.single v (1 : ℝ) ∈ geometricCarrier (⊤ : PreAbstractSimplicialComplex ι) :=
    ⟨{v}, singleton_nonempty _, subset_convexHull ℝ _ ⟨v, mem_singleton_self _, rfl⟩⟩
  have he : geometricCarrier (⊤ : PreAbstractSimplicialComplex ι) =
      geometricCarrier (⊥ : PreAbstractSimplicialComplex ι) := heq
  have hy := he ▸ hx
  rcases hy with ⟨σ, hσ, _⟩
  exact hσ

def registration : Registration arena.{u} statement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(by
    intro ι fi de K x
    exact @mem_geometricCarrier_iff ι fi de K x), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mem_geometricCarrier_iff.{u})
    (type_of% (realize signature.{u}
      (fun _ p K => @geometricCarrier p.vertices p.finite p.decidable K)
      (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension
      "mem_geometricCarrier_iff") "__information_unit",
  realizationName :=
    `Reg.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension.CarrierMembership.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p K => @geometricCarrier p.vertices p.finite p.decidable K)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 3,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension.CarrierMembership
