import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FibonacciFactorCompletion
import Reg.Support.FibonacciConsensusUniverse
import Reg.Support.FibonacciQuadratic
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Mathlib.Logic.Encodable.Basic

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
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit (budget budget_interval budgetLower budgetUpper)

namespace Reg.Support.FibonacciOriginalSourceWitness.Source20
noncomputable section
universe u

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ENat) (fun _ => ENNReal)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ x => ENat.toENNReal x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (0 : ENNReal)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type u}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ a r, OperationRecord o b contract a r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
        (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}),
    ∀ sourceModel : Model,
    let W (n : ℕ) := Nat.card {xs : List Return //
      GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
      listWeight xs=n}
    ENNReal.ofReal (limsup (fun n : ℕ =>
      Real.logb 2 ((max 1 (W n) : ℕ) : ℝ)/(n : ℝ)) atTop) ≤
      liminf (fun H : ℕ => r.readout () ()
        (Peak action initialConfiguration (OperationRecord o b contract) encoding H)/
        (H : ENNReal)) atTop

theorem budget_bounds : 0 ≤ budget ∧ budget < lam := by
  have gp : 0 < g := tail_arithmetic.2.2.2.1
  have g1 : g < 1 := tail_arithmetic.2.2.2.2.1
  have cp : 0 < chi := by dsimp [chi]; positivity
  have c1 : chi < 1 := by dsimp [chi]; exact pow_lt_one₀ gp.le g1 (by decide)
  have rp : 0 < rho := by dsimp [rho]; positivity
  have r1 : rho < 1 := by dsimp [rho]; exact pow_lt_one₀ gp.le g1 (by decide)
  have den : 0 < 1-rho*chi^2 := by nlinarith [pow_lt_one₀ cp.le c1 (by decide : (2:ℕ) ≠ 0)]
  have hs : 0 < hSide .high := by
    have gq : g < 1/4 := by have ht := Reg.Support.FibonacciQuadratic.t_bounds.2; dsimp [g]; linarith
    dsimp [hSide]; linarith
  have ap : 0 < aSide .high := by dsimp [aSide]; exact mul_pos (sub_pos.mpr r1) hs
  have smaller : budgetUpper < lam := by
    dsimp [budgetUpper]
    exact sub_lt_self _ (mul_pos (mul_pos (sq_pos_of_pos gp) (sq_pos_of_pos cp)) (div_pos ap den))
  have supply := (actual_strict_record_supply .original (fun _ => false) budget [] 2 le_rfl
    budget_interval.1 budget_interval.2).1.mpr (by simp [GuardTrace])
  obtain ⟨err,bound,rest⟩ := supply .high
  have bp : 0 < budget := (abs_nonneg (err 0)).trans_lt (bound 0)
  exact ⟨bp.le,budget_interval.2.trans smaller⟩

noncomputable def encodeState (c : Reg.Support.FibonacciConsensusUniverse.Configuration.{u}) : List Bool :=
  List.replicate (Encodable.encode c) true

theorem encodeState_injective : Function.Injective encodeState.{u} := by
  intro c d eq
  apply Encodable.encode_injective
  simpa [encodeState] using congrArg List.length eq

theorem rejected_law : ¬ sourceArena.{u}.Law rejected := by
  intro law
  let owner : Ownership := fun _ => false
  have bound := law (Reg.Support.FibonacciConsensusUniverse.action.{u} budget)
    Reg.Support.FibonacciConsensusUniverse.initial owner budget .closed 2 le_rfl
    budget_interval.1 budget_interval.2
    (Reg.Support.FibonacciConsensusUniverse.safety owner budget budget_bounds.1)
    (Reg.Support.FibonacciConsensusUniverse.liveness owner budget budget_bounds.1 budget_bounds.2)
    (Reg.Support.FibonacciConsensusUniverse.postprocessing owner budget)
    encodeState (encodeState_injective.injOn) .original
  change ENNReal.ofReal (actualRate .original 2 ((lam-budget)/g^2/chi^2) false) ≤
    liminf (fun H : ℕ => (0 : ENNReal)/(H : ENNReal)) atTop at bound
  have bad : actualRate .original 2 ((lam-budget)/g^2/chi^2) false ≤ 0 := by
    have zero : ENNReal.ofReal (actualRate .original 2 ((lam-budget)/g^2/chi^2) false) = 0 := by
      apply le_antisymm
      · simpa using bound
      · exact bot_le
    exact ENNReal.ofReal_eq_zero.mp zero
  have positive := actual_rate_positive .original owner budget 2 le_rfl budget_interval.1 budget_interval.2 false
  linarith

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]

def evidence : Registration sourceArena.{u} (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.original_complete_storage_liminf.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.original_complete_storage_liminf.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

end
end Reg.Support.FibonacciOriginalSourceWitness.Source20
