import Reg.Support.FibonacciConsensusUniverse
import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationCommonStem
noncomputable section
universe u v

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Label
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ w => w.length+1) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type u} {Z : Type v} [Finite Z]
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract)
    (processing : Processing action initialConfiguration (OperationRecord o b contract))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (alpha beta : Z → ℕ → Label) (highRecord lowRecord : Z → ℕ → Color)
    (n : ℕ) (w : List Label)
    (actualHigh : ∀ z, OperationRecord o b contract (alpha z) (highRecord z) ∧
      OperationFiniteSource (alpha z))
    (actualLow : ∀ z, OperationRecord o b contract (beta z) (lowRecord z))
    (past : ∀ z p, p < n → highRecord z p = lowRecord z p)
    (future : ∀ z z' p, highRecord z (n+p) = highRecord z' (n+p))
    (stemHigh : ∀ z i (hi : i < w.length), alpha z i = w[i])
    (stemLow : ∀ z i (hi : i < w.length), beta z i = w[i])
    (different : ∀ z, alpha z w.length ≠ beta z w.length)
    (sourceInjection : Function.Injective alpha),
    letI := Classical.decEq Configuration
    ∃ (cuts : Z → Frame Configuration Label) (states : Finset Configuration),
      (∀ z, Cut action initialConfiguration (front (highRecord z) n) (cuts z) ∧
        (cuts z).output.length ≤ w.length ∧
        (cuts z).output = w.take (cuts z).output.length ∧
        (cuts z).output <+: w) ∧
      Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
      (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
      Nat.card Z ≤ states.card * (r.readout () () w)

theorem rejected_law (b : ℝ) (bp : 0 ≤ b) (bl : b < lam)
    (supply : ActualPairSupply .original (fun _ => false) b .closed []) :
    ¬ sourceArena.{u,v}.Law rejected := by
  classical
  intro law
  let Z := ULift.{v} Unit
  let action := Reg.Support.FibonacciConsensusUniverse.action.{u} b
  let initialConfiguration := Reg.Support.FibonacciConsensusUniverse.initial.{u}
  let alpha : Z → ℕ → Label := fun _ => source .high .original []
  let beta : Z → ℕ → Label := fun _ => source .low .original []
  let highRecord : Z → ℕ → Color := fun _ => OperationPairedRecord .original (fun _ => false) [] .high
  let lowRecord : Z → ℕ → Color := fun _ => OperationPairedRecord .original (fun _ => false) [] .low
  have high := operation_pair_membership .original (fun _ => false) b .closed [] supply .high
  have low := operation_pair_membership .original (fun _ => false) b .closed [] supply .low
  have processing : Processing action initialConfiguration (OperationRecord (fun _ => false) b .closed) :=
    ⟨⟨_, ⟨[initialConfiguration], .refl⟩, Or.inr ⟨_, rfl⟩⟩,
      Reg.Support.FibonacciConsensusUniverse.postprocessing (fun _ => false) b⟩
  obtain ⟨cuts, states, cut, injection, membership, bound⟩ :=
    @law Reg.Support.FibonacciConsensusUniverse.Configuration.{u} Z inferInstance
      action initialConfiguration (fun _ => false) b .closed processing
      (Reg.Support.FibonacciConsensusUniverse.safety (fun _ => false) b bp)
      (Reg.Support.FibonacciConsensusUniverse.liveness (fun _ => false) b bp bl)
      alpha beta highRecord lowRecord 0 [] (fun _ => high) (fun _ => low.1)
      (by intro z p hp; omega) (by intro z z' p; rfl)
      (by intro z i hi; simp at hi) (by intro z i hi; simp at hi)
      (by intro z; change Label.L5 ≠ Label.L0; decide)
      (by intro z z' eq; exact Subsingleton.elim z z')
  norm_num [rejected, realize, Z] at bound

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationCommonStem
