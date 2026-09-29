import D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
import Reg.Support.GraphCutRegistrationTemplates
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.GraphCutRegistrationTemplates
open _root_.D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
open _root_.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
open LeanInformationAudit
open Lean Elab Command
open SimpleGraph

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight

universe u

def actual : Realization graphGradientSignature.{u} :=
  realize graphGradientSignature.{u}
    (fun _ p x => edgeDifferential p.2 x) (fun e => nomatch e)

def rejected : Realization graphGradientSignature.{u} :=
  realize graphGradientSignature.{u}
    (fun _ p _ => (0 : p.2.edgeSet → ZMod 2)) (fun e => nomatch e)

def arena : Arena where
  signature := graphGradientSignature.{u}
  Law r := ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet] (k : Nat),
    G.IsEdgeConnected k ↔
      ∀ x : V → ZMod 2,
        (∃ a b : V, x a ≠ x b) →
          k ≤ hammingNorm (r.readout () ⟨V, G⟩ x)

run_cmd do
  let root := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
  let sourceName := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight ++
    `edge_connected_iff_gradient_weight
  let identity := "sha256:1adc10ad04469401acae8c1ce04439ddd5de2c262b30eb8bb5df995be3588364"
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let G : SimpleGraph (ULift.{u} Bool) := completeGraph _
  have hc : G.IsEdgeConnected 1 := isEdgeConnected_one.mpr (connected_top.preconnected)
  have hw := (h (V := ULift.{u} Bool) G 1).mp hc
  let x : ULift.{u} Bool → ZMod 2 := fun b => if b.down then 1 else 0
  have hx : ∃ a b : ULift.{u} Bool, x a ≠ x b :=
    ⟨⟨false⟩, ⟨true⟩, by norm_num [x]⟩
  have hbad := hw x hx
  change 1 ≤ hammingNorm (0 : G.edgeSet → ZMod 2) at hbad
  simp at hbad

theorem sensitivity_proof : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence graphGradientSignature.{u} actual.{u} := by
  intro i
  let G : SimpleGraph (ULift.{u} Bool) := completeGraph _
  let x : ULift.{u} Bool → ZMod 2 := fun b => if b.down then 1 else 0
  refine ⟨⟨ULift.{u} Bool, G⟩, (fun _ => 0), x, ?_⟩
  intro h
  have he : s((⟨false⟩ : ULift.{u} Bool), ⟨true⟩) ∈ G.edgeSet := by simp [G]
  have hp := congrArg (fun f : G.edgeSet → ZMod 2 =>
    f ⟨s((⟨false⟩ : ULift.{u} Bool), ⟨true⟩), he⟩) h
  change (0 : ZMod 2) = 0 + 1 at hp
  norm_num at hp

def registration : Registration arena.{u} (arena.{u}.Law actual.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨edge_connected_iff_gradient_weight, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem edge_connected_iff_gradient_weight in arena
  readout via (realize graphGradientSignature.{u}
    (fun _ p x => edgeDifferential p.2 x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body",
        "arg", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
