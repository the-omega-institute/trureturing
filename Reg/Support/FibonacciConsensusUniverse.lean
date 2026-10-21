import Reg.Support.FibonacciFiniteIsolation
import Reg.Support.DecoderConfigurationTransport

namespace Reg.Support.FibonacciConsensusUniverse
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Reg.Support.FibonacciConsensus
noncomputable section
universe u

abbrev Configuration := ULift.{u} FibonacciConsensus.Configuration

def equivalence : FibonacciConsensus.Configuration ≃ Configuration.{u} := Equiv.ulift.symm

def initial : Configuration.{u} := equivalence FibonacciConsensus.initial

def action (theta : ℝ) : Configuration.{u} → Op Configuration.{u} Color Label :=
  DecoderConfigurationTransport.action equivalence (FibonacciConsensus.action theta)

/-- Universe reindexing preserves safety for every original closed record. -/
theorem safety (o : Ownership) (theta : ℝ) (htheta : 0 ≤ theta) :
    ∀ alpha r, OperationRecord o theta .closed alpha r → ∀ t,
      Run (action.{u} theta) (full r) ⟨initial,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p := by
  intro alpha r record t execution p hp
  have lowered := DecoderConfigurationTransport.run_inverse equivalence
    (FibonacciConsensus.action theta) (full r) execution
  exact FibonacciConsensus.safety o theta htheta alpha r record
    (DecoderConfigurationTransport.frame equivalence.symm t) lowered p hp

/-- The below-lam isolation proof supplies all original finite-source liveness cases. -/
theorem liveness (o : Ownership) (theta : ℝ) (hzero : 0 ≤ theta) (htheta : theta < lam) :
    ∀ alpha r, OperationRecord o theta .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run (action.{u} theta) (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length := by
  intro alpha r record finite p
  obtain ⟨t,execution,length⟩ :=
    FibonacciFiniteIsolation.liveness_below o theta hzero htheta alpha r record finite p
  exact ⟨DecoderConfigurationTransport.frame equivalence t,
    DecoderConfigurationTransport.run equivalence (FibonacciConsensus.action theta)
      (full r) execution,length⟩

/-- Lifted consensus remains immediately ready after every acquire. -/
theorem postprocessing (o : Ownership) (theta : ℝ) :
    ∀ alpha r, OperationRecord o theta .closed alpha r →
      ∀ (c d : Configuration.{u}) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration.{u} × List Label)),
      Run (action theta) (full r) ⟨initial,0,[]⟩ ⟨c,q,out⟩ →
      action theta c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain (action theta) ⟨d,q+1,out++batch⟩ t := by
  intro alpha r record c d q out batch f execution instruction result
  exact ⟨_,⟨[d],.refl⟩,Or.inr ⟨_,rfl⟩⟩

#print axioms safety
#print axioms liveness
#print axioms postprocessing
end
end Reg.Support.FibonacciConsensusUniverse
