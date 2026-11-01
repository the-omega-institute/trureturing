import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
import D5.S3.Combinatorics.Graph.Domination.MinusFourBaseStates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourFamily

open LeanInformationAudit
open Finset
open _root_.D5.S3.Combinatorics.Graph.DominatingSetAverage
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourBaseStates
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourFamily
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
open _root_.D5.S3.ConceptDynamics.InformationEscape

noncomputable section
attribute [local instance] Classical.propDecidable

def signature : DependentFamily.Signature where
  Params := ℕ
  State n := Finset (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ S => S.card) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := evaluation sourceGraph (-4) = 0 → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ R.readout () n S = 0

abbrev sourceScope := type_of% (@result_of_base_root)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp result_of_base_root

end
end Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourFamily
