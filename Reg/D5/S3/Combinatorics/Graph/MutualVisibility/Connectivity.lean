import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
universe u
namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity

abbrev reachSignature : Signature where
  Params := Sigma fun W : Type u => DecidableEq W
  State p := SimpleGraph p.1 × Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def reachActual : Realization reachSignature :=
  realize reachSignature (fun _ p z s t => @CutReach p.1 p.2 z.1 z.2 s t) (fun e => nomatch e)

abbrev cutReach_stepArena : Arena where
  signature := reachSignature
  Law r := ∀ p G C s t u, r.readout () p (G,C) s t → G.Adj t u → u ∉ C → r.readout () p (G,C) s u

def cutReach_stepEvidence : Registration cutReach_stepArena (type_of% (@cutReach_step.{u})) where
  actual := reachActual
  bridge := by
    constructor
    · intro h p G C s t u hst htu hu; exact @h p.1 p.2 G C s t u hst htu hu
    · intro h W inst G C s t u hst htu hu; exact h ⟨W, inst⟩ G C s t u hst htu hu

noncomputable def cutReach_stepRegistration : Contract.Registration (@cutReach_step.{u})
    (type_of% reachActual) (type_of% (@CutReach.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.cutReach_step,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity.cutReach_stepEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cutReach_stepArena⟩, objectArena := .source ⟨cutReach_stepArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cutReach_stepArena ⟨cutReach_stepEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some reachActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@CutReach.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

abbrev cutReach_two_step_paymentArena : Arena where
  signature := reachSignature
  Law r := ∀ p G C s t u v, r.readout () p (G,C) s t → G.Adj t u → G.Adj u v → ¬r.readout () p (G,C) s v → u ∈ C ∨ v ∈ C

def cutReach_two_step_paymentEvidence : Registration cutReach_two_step_paymentArena (type_of% (@cutReach_two_step_payment.{u})) where
  actual := reachActual
  bridge := by
    constructor
    · intro h p G C s t u v hs htu huv hv; exact @h p.1 p.2 G C s t u v hs htu huv hv
    · intro h W inst G C s t u v hs htu huv hv; exact h ⟨W, inst⟩ G C s t u v hs htu huv hv

noncomputable def cutReach_two_step_paymentRegistration : Contract.Registration (@cutReach_two_step_payment.{u})
    (type_of% reachActual) (type_of% (@CutReach.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.cutReach_two_step_payment,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity.cutReach_two_step_paymentEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cutReach_two_step_paymentArena⟩, objectArena := .source ⟨cutReach_two_step_paymentArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cutReach_two_step_paymentArena ⟨cutReach_two_step_paymentEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some reachActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@CutReach.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

abbrev cutReach_chain_paymentArena : Arena where
  signature := reachSignature
  Law r := ∀ p G C s (f : ℕ → p.1) a b, a ≤ b → (∀ k, a ≤ k → k < b → G.Adj (f k) (f (k+1))) → (r.readout () p (G,C) s (f b) ∨ f b ∈ C) → ¬r.readout () p (G,C) s (f a) → ∃ k, a ≤ k ∧ k ≤ b ∧ f k ∈ C

def cutReach_chain_paymentEvidence : Registration cutReach_chain_paymentArena (type_of% (@cutReach_chain_payment.{u})) where
  actual := reachActual
  bridge := by
    constructor
    · intro h p G C s f a b hab hstep hstart hend; exact @h p.1 p.2 G C s f a b hab hstep hstart hend
    · intro h W inst G C s f a b hab hstep hstart hend; exact h ⟨W, inst⟩ G C s f a b hab hstep hstart hend

noncomputable def cutReach_chain_paymentRegistration : Contract.Registration (@cutReach_chain_payment.{u})
    (type_of% reachActual) (type_of% (@CutReach.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.cutReach_chain_payment,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity.cutReach_chain_paymentEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cutReach_chain_paymentArena⟩, objectArena := .source ⟨cutReach_chain_paymentArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cutReach_chain_paymentArena ⟨cutReach_chain_paymentEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some reachActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@CutReach.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity
