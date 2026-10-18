import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FibonacciFactorCompletion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
import Reg.Support.FibonacciL22Budget
import Reg.Support.FibonacciConsensus
import Reg.Support.FibonacciConsensusUniverse

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion








namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal22
noncomputable section
universe u
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Bool → List Label)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ U L => canonicalReturnLo U L) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => phi + 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type u}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (θ : ℝ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hU : ∀ i, LegalWord s1 s1 (U i))
    (hV : ∀ i, LegalWord s2 s2 (V i)) (hUlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L) (hUWlen : ∀ i, (U i).length = (W i).length)
    (differentReturns : U false ≠ U true)
    (hbudget : familyEndpointBudget P Q h U V W L ≤ θ)
    (competingSingleton : canonicalReturnLo V L = canonicalReturnHi V L)
    (hfeasible : if 0 < (-g)^L then
      (CompetingT o θ s2 Q (V false) h W).Nonempty ∧
        canonicalReturnLo V L ∈ closure (CompetingT o θ s2 Q (V false) h W)
      else canonicalReturnLo V L ∈ CompetingT o θ s2 Q (V false) h W)
    (k : ℕ) (hk : k < P.length)
    (sameStem : ∀ p (hp : p < k), P[p] = Q[p]'(by omega))
    (differentStem : P[k] ≠ Q[k]'(by omega))
    (safety : ∀ alpha r, OperationRecord o θ .closed alpha r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p)
    (liveness : ∀ alpha r, OperationRecord o θ .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ alpha r, OperationRecord o θ .closed alpha r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t),
    ∃ (e : Guard) (w : List Label) (eta : ℕ → Label) (x : ℕ → ℝ),
      LegalWord s1 e w ∧ (r.readout () U L) < coordinate w 0 ∧ coordinate w 0 < (canonicalReturnHi U L) ∧
      ∀ n : ℕ, ∃ (beta : (Fin n → Bool) → ℕ → Label)
        (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed
          (address (synchronousPrefix P U z ++ w))
          (recordWithTail o (synchronousPrefix h W z) w) ∧
          OperationFiniteSource (address (synchronousPrefix P U z ++ w))) ∧
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed (beta z)
          (recordWithOmegaTail o (synchronousPrefix h W z) x)) ∧
        (∀ (z : Fin n → Bool) p (hp : p < (synchronousPrefix Q V z).length),
          beta z p = (synchronousPrefix Q V z)[p]) ∧
        (∀ (z : Fin n → Bool) p, beta z (P.length+n*L+p) = eta p) ∧
        (∀ (z : Fin n → Bool) p, recordWithTail o (synchronousPrefix h W z) w (P.length+n*L+p) =
          observe o (coordinate w p) 0) ∧
        Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z ++ w)) ∧
        (∀ (z : Fin n → Bool), Cut action initialConfiguration
          (front (recordWithTail o (synchronousPrefix h W z) w) (P.length+n*L)) (cuts z) ∧
          (cuts z).output.length ≤ k ∧
          (cuts z).output = (P.take k).take (cuts z).output.length ∧
          (cuts z).output <+: P.take k) ∧
        Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
        (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
        2^n ≤ states.card*(k+1)

theorem source_bridge :
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.canonical_synchronous_common_stem.{u}) ↔
      sourceArena.{u}.Law actual := Iff.rfl

theorem positive_law : sourceArena.{u}.Law actual :=
  @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.canonical_synchronous_common_stem.{u}

theorem actual_dependence : ObservationalDependence observationSignature actual :=
  CanonicalGeometry.ExactOriginal46.evidence.dependence

/-- Whole-Law rejection requires an actual decoder satisfying all three original premises. -/
theorem rejected_law_of_operational_premises {Configuration : Type u}
    (action : Configuration → Op Configuration Color Label)
    (initialConfiguration : Configuration)
    (safety : ∀ alpha r, OperationRecord Reg.Support.FibonacciL22.ownership
      Reg.Support.FibonacciL22.theta .closed alpha r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p)
    (liveness : ∀ alpha r, OperationRecord Reg.Support.FibonacciL22.ownership
      Reg.Support.FibonacciL22.theta .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ alpha r, OperationRecord Reg.Support.FibonacciL22.ownership
      Reg.Support.FibonacciL22.theta .closed alpha r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t) :
    ¬ sourceArena.{u}.Law rejected := by
  intro law
  let P := Reg.Support.FibonacciL22.P
  let Q := Reg.Support.FibonacciL22.Q
  have data := Reg.Support.FibonacciL22.legal_words
  have lens := Reg.Support.FibonacciL22.lengths
  have stems := Reg.Support.FibonacciL22.stem
  have singleton : canonicalReturnLo Reg.Support.FibonacciL22.V 22 =
      canonicalReturnHi Reg.Support.FibonacciL22.V 22 :=
    Reg.Support.FibonacciL22.endpoints.2.2.1.trans
      Reg.Support.FibonacciL22.endpoints.2.2.2.symm
  obtain ⟨e,w,eta,x,legal,lower,_⟩ := law action initialConfiguration
    Reg.Support.FibonacciL22.ownership Reg.Support.FibonacciL22.theta
    .G0 .G0 P Q Reg.Support.FibonacciL22.h data.1 data.2.1 lens.1 lens.2.1
    Reg.Support.FibonacciL22.U Reg.Support.FibonacciL22.V Reg.Support.FibonacciL22.W
    22 (by decide) data.2.2.1 data.2.2.2 lens.2.2.1 lens.2.2.2.1 lens.2.2.2.2
    Reg.Support.FibonacciL22.different_returns Reg.Support.FibonacciL22.budget_le
    singleton Reg.Support.FibonacciL22.feasibility
    1 stems.1 stems.2.1 stems.2.2 safety liveness postprocessing
  obtain ⟨path,h0,_,support,_⟩ := literal_address_path .G0 e w legal
  have upper := (support 0).2
  rw [h0] at upper
  change coordinate w 0 ≤ phi at upper
  change phi + 1 < coordinate w 0 at lower
  linarith


/-- The actual legal L22 tuple supplies a counterexample to the whole original Law.
The decoder's liveness proof is below lam; no endpoint or all-theta model is asserted. -/
theorem rejected_law : ¬ sourceArena.{u}.Law rejected := by
  exact rejected_law_of_operational_premises.{u}
    (Reg.Support.FibonacciConsensusUniverse.action Reg.Support.FibonacciL22.theta)
    Reg.Support.FibonacciConsensusUniverse.initial
    (Reg.Support.FibonacciConsensusUniverse.safety Reg.Support.FibonacciL22.ownership
      Reg.Support.FibonacciL22.theta Reg.Support.FibonacciL22.theta_bounds.1.le)
    (Reg.Support.FibonacciConsensusUniverse.liveness Reg.Support.FibonacciL22.ownership
      Reg.Support.FibonacciL22.theta Reg.Support.FibonacciL22.theta_bounds.1.le
      Reg.Support.FibonacciL22.theta_bounds.2)
    (Reg.Support.FibonacciConsensusUniverse.postprocessing Reg.Support.FibonacciL22.ownership
      Reg.Support.FibonacciL22.theta)

theorem sensitivity : Sensitivity sourceArena.{u} actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.{u}.Law actual rejected rejected_law

def evidence : Registration sourceArena.{u}
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.canonical_synchronous_common_stem.{u}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal22

