import Reg.Support.FibonacciBranchStorageWitness.HighEndpoints
import Reg.Support.FibonacciBranchStorageWitness.LowEndpoints
import Reg.Support.FibonacciConsensusUniverse
import Mathlib.Logic.Encodable.Basic

namespace Reg.Support.FibonacciBranchStorageWitness
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
noncomputable section
universe u

theorem family_budget : familyEndpointBudget P Q h high low colors 86 ≤ budget := by
  have costs {a z : ℝ} {w : List Label} {cs : List Color}
      (hc : EndpointCertificate budget a z w cs) : ∀ x ∈ endpointCosts a z w cs, x ≤ budget := by
    intro x hx
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hx
    exact max_le (hc r r.isLt).1.2 (hc r r.isLt).2.2
  have fold (xs : List ℝ) (bounds : ∀ x ∈ xs, x ≤ budget) : xs.foldr max 0 ≤ budget := by
    induction xs with
    | nil => exact budget_bounds.1.le
    | cons x xs ih =>
        exact max_le (bounds x (by simp)) (ih (fun z hz => bounds z (by simp [hz])))
  unfold familyEndpointBudget
  apply fold
  rw [familyEndpointCosts,endpoints.1,endpoints.2.1,endpoints.2.2.1,endpoints.2.2.2]
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
  · exact costs certP x hx
  · exact costs certQ x hx
  · exact costs (certHigh false) x hx
  · exact costs (certHigh true) x hx
  · exact costs (certLow false) x hx
  · exact costs (certLow true) x hx

local instance : Encodable Reg.Support.FibonacciConsensusUniverse.Configuration.{u} :=
  Encodable.ofCountable _
def encoding (c : Reg.Support.FibonacciConsensusUniverse.Configuration.{u}) : List Bool :=
  List.replicate (Encodable.encode c) true

theorem encoding_injective : Function.Injective encoding.{u} := by
  intro x y eq
  apply Encodable.encode_injective
  have equalLengths := congrArg List.length eq
  simpa only [encoding,List.length_replicate] using equalLengths

theorem faithful : Set.InjOn encoding.{u} {c | ∃ H,
    ReachThrough (Reg.Support.FibonacciConsensusUniverse.action budget)
      Reg.Support.FibonacciConsensusUniverse.initial (OperationRecord (fun _ => false) budget .closed) H c} :=
  encoding_injective.injOn


#print axioms family_budget
#print axioms faithful
end
end Reg.Support.FibonacciBranchStorageWitness
