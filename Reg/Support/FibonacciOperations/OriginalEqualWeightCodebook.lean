import Reg.Support.FibonacciOperations.Witness
import Reg.Support.FibonacciConsensusUniverse
import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalEqualWeightCodebook
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ R => R.r) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, r.readout () () R = 1 ∧ ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam - b) / g ^ 2 / chi ^ K
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
    Finite V ∧ ∃ eps : ℝ, 0 < eps ∧ 0 < N + (20 + 6*R.m) ∧
      (∀ (targetModel : Model) (words : List (List Return)),
        (∀ xs ∈ words, GuardTrace K d false .high xs (initial .high sourceModel) ∧
          listWeight xs = N) →
        ActualPairSupply targetModel o (b-eps) .closed (resetConcatenation R words) ∧
        (∀ contract : Contract, ActualPairSupply targetModel o b contract
          (resetConcatenation R words)) ∧
        listWeight (resetConcatenation R words) = words.length * (N + (20 + 6*R.m))) ∧
      (∀ (targetModel : Model) (contract : Contract) (q : ℕ),
        Nat.card V ^ q ≤ Nat.card {xs : List Return //
          ActualPairSupply targetModel o b contract xs ∧
          listWeight xs = q * (N + (20 + 6*R.m))})

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro law
  obtain ⟨b, lower, upper⟩ := Reg.Support.FibonacciOperations.Witness.budget_witness
  obtain ⟨R, impossible, rest⟩ := law (fun _ => false) b 2 (by decide) lower upper
  change (0 : ℕ) = 1 at impossible
  exact Nat.zero_ne_one impossible


def evidence : Registration sourceArena (type_of% @original_equal_weight_codebook) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_equal_weight_codebook, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), ⟨1,1,by decide,by decide⟩, ⟨1,2,by decide,by decide⟩, ?_⟩
    norm_num [actual, realize]

#print axioms rejected_law
#print axioms evidence
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalEqualWeightCodebook
