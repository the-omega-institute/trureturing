import Reg.Support.FibonacciOperations.Witness
import Reg.Support.FibonacciConsensusUniverse
import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.SuppliedCodebookStorageLiminf
noncomputable section
open Filter
universe u

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ B => (B : ℝ)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type u}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract) (K : ℕ)
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
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c})
    (R : Return) (sourceModel model : Model) (N : ℕ) (hN : 0 < N)
    (ha : 1 ≤ Nat.card {xs : List Return //
      GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
      listWeight xs = N})
    (emptySupply : ActualPairSupply model o b contract [])
    (count : ∀ q : ℕ,
      Nat.card {xs : List Return //
        GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
        listWeight xs = N} ^ q ≤
      Nat.card {xs : List Return // ActualPairSupply model o b contract xs ∧
        listWeight xs = q*(N+(20+6*R.m))}),
    let a := Nat.card {xs : List Return //
      GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
      listWeight xs = N}
    let L := N+(20+6*R.m)
    let fullPeak := Peak action initialConfiguration (OperationRecord o b contract) encoding
    (∀ H B : ℕ, observationOffset model ≤ H → fullPeak H ≤ (B : WithTop ℕ) →
      (((H-observationOffset model)/L : ℕ) : ℝ)*Real.logb 2 (a : ℝ)-1 ≤ r.readout () () B) ∧
    ENNReal.ofReal (Real.logb 2 (a : ℝ)/(L : ℝ)) ≤
      liminf (fun H : ℕ => ENat.toENNReal (fullPeak H)/(H : ENNReal)) atTop

theorem rejected_law : ¬ sourceArena.{u}.Law rejected := by
  intro law
  obtain ⟨b, lower, upper⟩ := Reg.Support.FibonacciOperations.Witness.budget_witness
  obtain ⟨bp, bl⟩ := Reg.Support.FibonacciOperations.Witness.budget_bounds b lower upper
  obtain ⟨R, hr, books⟩ := original_equal_weight_codebook (fun _ => false) b 2
    (by decide) lower upper
  obtain ⟨finite, eps, ep, positive, uniform, count⟩ := books .original 78 (by decide)
  have emptySupply : ActualPairSupply .original (fun _ => false) b .closed [] := by
    have h := uniform .original [] (by simp)
    simpa [resetConcatenation] using h.2.1 .closed
  have ha := (_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.even_actual_positivity
    (fun _ => false) b 2 (by decide) lower upper 78 (by decide) le_rfl).2.2 .original false
  have result := law (Reg.Support.FibonacciConsensusUniverse.action.{u} b)
    Reg.Support.FibonacciConsensusUniverse.initial (fun _ => false) b .closed 2
    (Reg.Support.FibonacciConsensusUniverse.safety (fun _ => false) b bp)
    (Reg.Support.FibonacciConsensusUniverse.liveness (fun _ => false) b bp bl)
    (Reg.Support.FibonacciConsensusUniverse.postprocessing (fun _ => false) b)
    Reg.Support.FibonacciOperations.Witness.encoding
    Reg.Support.FibonacciOperations.Witness.encoding_injective.injOn R .original .original 78
    (by decide) (Nat.succ_le_of_lt ha.1) emptySupply (count .original .closed)
  obtain ⟨B, bound⟩ := Reg.Support.FibonacciOperations.Witness.finite_peak.{u}
    (fun _ => false) b bp (observationOffset .original)
  have bad := result.1 (observationOffset .original) B le_rfl bound
  norm_num [rejected, realize] at bad


def evidence : Registration sourceArena.{u} (type_of% @supplied_codebook_storage_liminf.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@supplied_codebook_storage_liminf.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

#print axioms rejected_law
#print axioms evidence
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.SuppliedCodebookStorageLiminf
