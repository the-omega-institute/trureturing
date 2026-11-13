import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.Probability.SkorokhodRepresentation

/-! Dependent source reconstruction for the full native Skorokhod theorem.
The observation is pushforward of a real measure by a measurable-space-valued
function; the arbitrary Polish carrier and complete original telescope remain.
-/

open MeasureTheory Filter Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Analytic.Probability.SkorokhodRepresentation

structure MapParams where
  X : Type u
  mX : MeasurableSpace X

abbrev signature : Signature where
  Params := MapParams.{u}
  State p := ℝ → p.X
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Measure ℝ → @Measure p.X p.mX
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p f => @Measure.map ℝ p.X inferInstance p.mX f)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {X : Type u} [tX : TopologicalSpace X] [PolishSpace X]
      [mX : MeasurableSpace X] [BorelSpace X]
      (μ : ℕ → ProbabilityMeasure X) (μ₀ : ProbabilityMeasure X),
    Tendsto (fun n => μ n) atTop (nhds μ₀) →
    ∃ (Y : ℕ → ℝ → X) (Y₀ : ℝ → X),
      (∀ n, Measurable (Y n)) ∧ Measurable Y₀ ∧
      (∀ n, r.readout false ⟨X, mX⟩
        (Y n) (volume.restrict (Set.Icc (0 : ℝ) 1)) = (μ n : Measure X)) ∧
      r.readout true ⟨X, mX⟩
        Y₀ (volume.restrict (Set.Icc (0 : ℝ) 1)) = (μ₀ : Measure X) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
        Tendsto (fun n => Y n t) atTop (nhds (Y₀ t))

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Analytic.Probability.SkorokhodRepresentation.skorokhod_representation.{u}))
      ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual :=
  source_bridge.mp
    (@_root_.D5.S3.Analytic.Probability.SkorokhodRepresentation.skorokhod_representation.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let μ₀ : ProbabilityMeasure (ULift.{u} Unit) :=
    ⟨Measure.dirac ⟨()⟩, inferInstance⟩
  obtain ⟨Y, Y₀, hY, hY₀, hlaw, hlaw₀, hconv⟩ :=
    h (fun _ => μ₀) μ₀ tendsto_const_nhds
  have hzero : (0 : Measure (ULift.{u} Unit)) = (μ₀ : Measure (ULift.{u} Unit)) := hlaw₀
  have hmass := congrArg (fun ρ : Measure (ULift.{u} Unit) => ρ Set.univ) hzero
  simpa using hmass

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : MapParams.{u} := ⟨ULift.{u} Bool, ⊤⟩
  let f : ℝ → p.X := fun _ => ⟨false⟩
  let g : ℝ → p.X := fun _ => ⟨true⟩
  refine ⟨p, f, g, ?_⟩
  intro h
  have hmass := congrArg (fun k : Measure ℝ → @Measure p.X p.mX =>
    k (Measure.dirac 0) {⟨false⟩}) h
  change (Measure.map f (Measure.dirac 0)) {⟨false⟩} =
    (Measure.map g (Measure.dirac 0)) {⟨false⟩} at hmass
  simp [f, g, p, Measure.map_const, Pi.single_apply] at hmass

def source_registration : Registration arena.{u}
    (type_of%
      (@_root_.D5.S3.Analytic.Probability.SkorokhodRepresentation.skorokhod_representation.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨
    realize signature (fun j p f => if j = i then (fun _ => 0) else actual.readout j p f)
      (fun e => nomatch e),
    (by intro j hj; funext p f; simp [realize, hj]), rfl, (by
      intro h
      let μ₀ : ProbabilityMeasure (ULift.{u} Unit) :=
        ⟨Measure.dirac ⟨()⟩, inferInstance⟩
      obtain ⟨Y, Y₀, hY, hY₀, hlaw, hlaw₀, hconv⟩ :=
        h (fun _ => μ₀) μ₀ tendsto_const_nhds
      cases i with
      | false =>
        have hz := congrArg (fun ρ : Measure (ULift.{u} Unit) => ρ Set.univ) (hlaw 0)
        simp [realize] at hz
      | true =>
        have hz := congrArg (fun ρ : Measure (ULift.{u} Unit) => ρ Set.univ) hlaw₀
        simp [realize] at hz)⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Analytic.Probability.SkorokhodRepresentation.skorokhod_representation.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.SkorokhodRepresentation.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.SkorokhodRepresentation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p f => @Measure.map ℝ p.X inferInstance p.mX f)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.SkorokhodRepresentation
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Analytic.Probability.SkorokhodRepresentation
end
