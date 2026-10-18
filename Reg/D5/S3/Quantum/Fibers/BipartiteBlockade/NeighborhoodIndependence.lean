import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence

noncomputable section
open scoped BigOperators Classical

namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence

open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

structure Parameters where
  V : Type u
  equality : DecidableEq V
  graph : SimpleGraph V
  neighborhoods : Finset (Finset V)
  coefficient : Finset V → ℝ
  constant : ℝ
  single : V → ℝ

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def actual : Realization signature.{u} := by
  classical
  exact realize signature
    (fun _ p S => by
      letI := p.equality
      exact ∑ N ∈ p.neighborhoods,
        p.coefficient N * (if Disjoint N S then 1 else 0))
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [equality : DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V))
    (_independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (_large : ∀ N ∈ F, 2 ≤ N.card)
    (coefficient : Finset V → ℝ) (constant : ℝ) (single : V → ℝ)
    (_relation : ∀ S : Finset V, (∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v) →
      r.readout () ⟨V, equality, G, F, coefficient, constant, single⟩ S =
        constant + ∑ v ∈ S, single v),
    ∀ N ∈ F, coefficient N = 0

/-- Exact source reconstruction without a claimed four-slot registration.
The complete source relation forces every actual blocking-sum observation to zero. -/
theorem source_equivalence :
    (type_of% (@blocking_independent_mod_singletons.{u})) ↔ arena.{u}.Law actual := Iff.rfl

#print axioms source_equivalence

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence
