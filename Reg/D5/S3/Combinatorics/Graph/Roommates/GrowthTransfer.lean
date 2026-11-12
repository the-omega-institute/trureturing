import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.Combinatorics.Graph.Roommates
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer

/-- The readout carries the actual real probability operand. -/
abbrev probabilitySignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- An application of the enrolled dependent-family realization template. -/
def actual : Realization probabilitySignature :=
  realize probabilitySignature (fun _ _ x => x) (fun e => nomatch e)

/-- The original three count premises and complete source conclusion. -/
abbrev transferArena : Arena where
  signature := probabilitySignature
  Law R :=
    (∀ m k : ℕ, 0 < m → 0 < k →
      OpenCertificates.count m * OpenCertificates.count k ≤ OpenCertificates.count (m + k + 6)) →
    (∀ m : ℕ, 0 < m → OpenCertificates.count m ≤
      Fintype.card {p : SourceModel.Profile (m + 1) // SourceModel.HasStableMatching p}) →
    OpenCertificates.count 3 < 24 ^ 3 →
    ∃ q c C : ℝ, 0 < q ∧ q < 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        c * q ^ (n + 5) ≤ R.readout () () (SourceModel.solutionProbability n) ∧
        R.readout () () (SourceModel.solutionProbability n) ≤ C * q ^ (n + 5)

/-- Exact reconstruction of the source telescope; no count premise is omitted. -/
def sourceBridge : (type_of% GrowthTransfer.same_q_probability_of_counts) ↔
    transferArena.Law actual := Iff.rfl

/-- The actual readout observes its real operand. -/
def dependence : ObservationalDependence probabilitySignature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

/- A complete Contract.Registration is unavailable: whole-law variation and
role sensitivity require an inhabited instance of the three concrete premises.
Those premises are not proved by this analytic contribution. Source-selection
and current native binding evidence are also absent. See issue 29645.
This partial reconstruction is not declared_validated. -/

#print axioms sourceBridge
#print axioms dependence

end Reg.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer
