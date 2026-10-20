import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditFibTests.AuricFib.SearchReduction

/-! Optional information-face calibration on compiled source contracts. -/
namespace LeanInformationAudit.Tests.SearchReduction.InformationTests
open Lean Meta Elab Command
open LeanInformationAudit LeanInformationAudit.SearchReduction
open LeanInformationAudit.AuricFib.Contract
open LeanInformationAuditFibTests.AuricFib

/-- A witness in a restricted domain remains a witness in every larger domain. -/
theorem separated_domain_mono {Θ : Type*} (law : Θ →
    D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window → ℝ)
    (small large : Θ → Prop) (included : ∀ θ, small θ → large θ)
    (separated : ∃ θ φ, small θ ∧ small φ ∧ Pyramid.CoarseEq (law θ) (law φ) ∧
      Pyramid.delta (law θ) ≠ Pyramid.delta (law φ)) :
    ∃ θ φ, large θ ∧ large φ ∧ Pyramid.CoarseEq (law θ) (law φ) ∧
      Pyramid.delta (law θ) ≠ Pyramid.delta (law φ) := by
  obtain ⟨θ, φ, hθ, hφ, same, different⟩ := separated
  exact ⟨θ, φ, included θ hθ, included φ hφ, same, different⟩

theorem strict_not_reduction :
    (∀ θ w, LawFixture.Separation.law θ w = LawFixture.Separation.law θ w) ∧
    (∃ θ φ, LawFixture.Separation.family.domain θ ∧
      LawFixture.Separation.family.domain φ ∧
      Pyramid.CoarseEq (LawFixture.Separation.family.law θ)
        (LawFixture.Separation.family.law φ) ∧
      Pyramid.delta (LawFixture.Separation.family.law θ) ≠
        Pyramid.delta (LawFixture.Separation.family.law φ)) := by
  constructor
  · exact LawFixture.Separation.target
  · exact LawFixture.Separation.separated

theorem bool_image_not_three {α : Type*} (f : Bool → α) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ((∃ x, f x = a) ∧ (∃ y, f y = b) ∧ (∃ z, f z = c)) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
  cases x <;> cases y <;> cases z <;> simp_all

example : informationTag .bindOnly .strictBound = some "conflict:strict-vs-bind-only" := rfl
example : informationTag .nonBindOnly .strictBound = some "both" := rfl
example : informationTag .insufficient .strictBound = some "information-only" := rfl
example (v : Verdict) : informationTag v .collapsedBound = none := rfl

run_cmd do
  let source ← getEnv
  for (target, application) in #[
      (``LawFixture.Separation.target, ``LawFixture.Separation.strict),
      (``LawFixture.Simplex.target, ``LawFixture.Simplex.strict),
      (``LawFixture.Star.target, ``LawFixture.Star.analysis)] do
    let reading ← acquireInformation source target #[] (some application)
    unless reading.face == .notBound "source_not_registered" do
      throwError "negative information binding: {application}: {repr reading.face}"
    logInfo s!"information-negative {target}: {reading.face.label}"
  let positive ← acquireInformation source ``LawFixture.RegisteredPos.target #[]
    (some ``LawFixture.RegisteredPos.strict)
  unless positive.face == .strictBound && !positive.ordinaryRecords.isEmpty do
    throwError "positive information binding: {repr positive.face}"
  logInfo s!"information-positive: {positive.face.label}; registration={positive.registration}"
  let unsafeRoot ← acquireInformation source ``LawFixture.RegisteredPos.target #[]
    (some ``LawFixture.RegisteredPos.unsafeApplication)
  unless unsafeRoot.face == .notBound "application_not_safe_definition" do
    throwError "unsafe Application root accepted: {repr unsafeRoot.face}"
  let polluted ← acquireInformation source ``LawFixture.RegisteredPos.target
    #[``LawFixture.Separation.law] (some ``LawFixture.RegisteredPos.strict)
  unless polluted.face.label.startsWith "not-bound(law_vocabulary_intersects_S:" do
    throwError "law vocabulary S overlap accepted: {repr polluted.face}"

run_cmd liftTermElabM do
  let info ← getConstInfo ``LawFixture.Separation.target
  let result ← localRebuild info.type
  unless result.cost == .zero && result.proof?.isSome do
    throwError "Separation tautology did not close at zero: {result.detail}"
  let computational : Observation := {
    target := info.name, base := .found, paired := .found, verdict := .bindOnly }
  let withStrict := withInformation computational { face := .strictBound }
  unless (computationalJson withStrict).compress == (computationalJson computational).compress do
    throwError "optional evidence changed computational projection"
  logInfo s!"Separation.target: d_B=0; bind-only; strict alone yields conflict tag; \
    submitted unregistered evidence remains not-bound"

#print axioms separated_domain_mono
#print axioms bool_image_not_three
#print axioms strict_not_reduction
#print axioms report_computational_unchanged
#print axioms verdict_parallel
end LeanInformationAudit.Tests.SearchReduction.InformationTests
