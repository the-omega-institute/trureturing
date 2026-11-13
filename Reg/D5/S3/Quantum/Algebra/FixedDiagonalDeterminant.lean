import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.FixedDiagonalDeterminant

/-! Complete source reconstruction from the fixed coefficient matrix readout. -/

set_option autoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant

namespace Reg.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant
universe u v

structure Parameters where
  k : Type u
  I : Type v
  [field : Field k]
  [finite : Fintype I]
  [decidable : DecidableEq I]
  [nontrivial : Nontrivial I]

attribute [instance] Parameters.field Parameters.finite Parameters.decidable Parameters.nontrivial

abbrev signature : Signature where
  Params := Parameters.{u, v}
  State p := Matrix p.I p.I p.k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.I p.I p.k
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} := realize signature
  (fun _ _ N => N) (fun e => nomatch e)

def conclusion (p : Parameters.{u, v}) (N observed : Matrix p.I p.I p.k) : Prop :=
  (∀ i j, Relation.ReflTransGen (fun a b => N a b ≠ 0) i j) →
    Irreducible (rowMatrix observed).det

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ (p : Parameters.{u, v}) (N : signature.State p), conclusion p N (R.readout () p N)

theorem full_telescope_bridge :
    (type_of% (@row_determinant_irreducible.{u, v})) ↔ arena.{u, v}.Law actual := by
  constructor
  · intro h p N hN
    exact @h p.k p.I p.field p.finite p.decidable p.nontrivial N hN
  · intro h k I field finite decidable nontrivial N hN
    exact h { k := k, I := I, field := field, finite := finite,
      decidable := decidable, nontrivial := nontrivial } N hN

def rejected : Realization signature.{u, v} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

private def probe : Parameters.{u, v} where
  k := ULift.{u} ℚ
  I := ULift.{v} (Fin 2)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  have h := law probe (fun _ _ => 1)
    (fun _ _ => Relation.ReflTransGen.single one_ne_zero)
  change Irreducible (rowMatrix (0 : Matrix probe.I probe.I probe.k)).det at h
  simpa [rowMatrix] using h

theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  refine ⟨probe, 0, 1, ?_⟩
  change (0 : Matrix probe.I probe.I probe.k) ≠ 1
  exact zero_ne_one

def source_registration : Registration arena.{u, v}
    (type_of% (@row_determinant_irreducible.{u, v})) where
  actual := actual
  bridge := full_telescope_bridge
  variation := ⟨full_telescope_bridge.mp (@row_determinant_irreducible.{u, v}),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Reg.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant
