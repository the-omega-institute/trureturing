import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
import Reg.Support.FibonacciL22Budget
import Reg.Support.FibonacciConsensusUniverse

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter
open scoped Topology

namespace Reg.Support.FibonacciOriginalSourceWitness.Source84
noncomputable section
universe u

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ lo => lo) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => phi+1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type u}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U : Bool → List Label) (V : List Label) (W : Bool → List Color)
    (L : ℕ) (hU : ∀ i, LegalWord s1 s1 (U i))
    (hV : LegalWord s2 s2 V) (hUlen : ∀ i, (U i).length = L)
    (hVlen : V.length = L) (hUWlen : ∀ i, (U i).length = (W i).length)
    (differentReturns : U false ≠ U true)
    (lo hi : ℝ) (hwidth : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s1 z)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (U i) z ∧ compose (U i) z ≤ hi)
    (stemCert : EndpointCertificate θ lo hi P h)
    (returnCert : ∀ i, EndpointCertificate θ lo hi (U i) (W i))
    (a y : ℝ) (ha : -1 < a) (ha1 : a < 1) (hane : a ≠ 0)
    (hslope : a = (-g)^V.length) (hfixed : compose V y = y)
    (hfeasible : if 0 < a then
      (CompetingT o θ s2 Q V h W).Nonempty ∧ y ∈ closure (CompetingT o θ s2 Q V h W)
      else y ∈ CompetingT o θ s2 Q V h W)
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
      LegalWord s1 e w ∧ r.readout () () lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      ∀ n : ℕ, ∃ (beta : (Fin n → Bool) → ℕ → Label)
        (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed
          (address (synchronousPrefix P U z ++ w))
          (recordWithTail o (synchronousPrefix h W z) w) ∧
          OperationFiniteSource (address (synchronousPrefix P U z ++ w))) ∧
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed (beta z)
          (recordWithOmegaTail o (synchronousPrefix h W z) x)) ∧
        (∀ (z : Fin n → Bool) p (hp : p < (synchronousPrefix Q (fun _ => V) z).length),
          beta z p = (synchronousPrefix Q (fun _ => V) z)[p]) ∧
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

theorem rejected_law : ¬ sourceArena.{u}.Law rejected := by
  intro law
  let P := Reg.Support.FibonacciL22.P
  let Q := Reg.Support.FibonacciL22.Q
  let U := Reg.Support.FibonacciL22.U
  let V := Reg.Support.FibonacciL22.V
  let W := Reg.Support.FibonacciL22.W
  have data := Reg.Support.FibonacciL22.legal_words
  have lens := Reg.Support.FibonacciL22.lengths
  have stems := Reg.Support.FibonacciL22.stem
  have singleton : canonicalReturnLo V 22 = canonicalReturnHi V 22 :=
    Reg.Support.FibonacciL22.endpoints.2.2.1.trans Reg.Support.FibonacciL22.endpoints.2.2.2.symm
  have highHull := canonical_legal_return_hull .G0 U 22 (by decide) lens.2.2.1 data.2.2.1
  have lowHull := canonical_legal_return_hull .G0 V 22 (by decide) lens.2.2.2.1 data.2.2.2
  have cert := family_endpoint_certificates .G0 .G0 P Q Reg.Support.FibonacciL22.h data.1 data.2.1
    U V W 22 (by decide) lens.2.2.1 lens.2.2.2.1 data.2.2.1 data.2.2.2 lens.2.2.2.2
  have slope := return_slope_control 22 (by decide)
  have fixed : compose (V false) (canonicalReturnLo V 22) = canonicalReturnLo V 22 := by
    have atLo := lowHull.2.2.2.1 false (canonicalReturnLo V 22) le_rfl (le_of_eq singleton)
    rw [← singleton] at atLo
    exact le_antisymm atLo.2 atLo.1
  let theta := Reg.Support.FibonacciL22.theta
  let owner := Reg.Support.FibonacciL22.ownership
  obtain ⟨e,w,eta,x,legal,lower,rest⟩ := law
    (Reg.Support.FibonacciConsensusUniverse.action.{u} theta) Reg.Support.FibonacciConsensusUniverse.initial
    owner theta Reg.Support.FibonacciL22.theta_bounds.1.le
    .G0 .G0 P Q Reg.Support.FibonacciL22.h data.1 data.2.1 lens.1 lens.2.1
    U (V false) W 22 data.2.2.1 (data.2.2.2 false) lens.2.2.1 (lens.2.2.2.1 false) lens.2.2.2.2
    Reg.Support.FibonacciL22.different_returns
    (canonicalReturnLo U 22) (canonicalReturnHi U 22)
    (highHull.2.1 Reg.Support.FibonacciL22.different_returns) highHull.2.2.1 highHull.2.2.2.1
    (endpoint_certificate_mono _ theta _ _ P _ Reg.Support.FibonacciL22.budget_le cert.2.2.1)
    (fun i => endpoint_certificate_mono _ theta _ _ _ _ Reg.Support.FibonacciL22.budget_le (cert.2.2.2.1 i))
    ((-g)^22) (canonicalReturnLo V 22) slope.1 slope.2.1 slope.2.2
    (by rw [lens.2.2.2.1 false]) fixed Reg.Support.FibonacciL22.feasibility
    1 stems.1 stems.2.1 stems.2.2
    (Reg.Support.FibonacciConsensusUniverse.safety owner theta Reg.Support.FibonacciL22.theta_bounds.1.le)
    (Reg.Support.FibonacciConsensusUniverse.liveness owner theta Reg.Support.FibonacciL22.theta_bounds.1.le Reg.Support.FibonacciL22.theta_bounds.2)
    (Reg.Support.FibonacciConsensusUniverse.postprocessing owner theta)
  obtain ⟨path,h0,_,support,_⟩ := literal_address_path .G0 e w legal
  have upper := (support 0).2
  rw [h0] at upper
  change coordinate w 0 ≤ phi at upper
  change phi+1 < coordinate w 0 at lower
  linarith

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]

def evidence : Registration sourceArena.{u} (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.original_synchronous_common_stem.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.original_synchronous_common_stem.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

end
end Reg.Support.FibonacciOriginalSourceWitness.Source84
