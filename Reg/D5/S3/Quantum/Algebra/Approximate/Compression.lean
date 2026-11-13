import D5.S3.Quantum.Algebra.Approximate.Compression
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.Approximate.Compression

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.Approximate.Compression

structure Scope where
  A : Type u
  [ring : NormedRing A]
  [algebra : NormedAlgebra ℝ A]
  [complete : CompleteSpace A]
  [normOne : NormOneClass A]

attribute [instance] Scope.ring Scope.algebra Scope.complete Scope.normOne

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ t => correction t) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@correction_idempotent.{u})

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (p : Scope.{u}) (t : p.A), ‖t ^ 2 - 1‖ < 1 →
    r.readout () p t * r.readout () p t = r.readout () p t

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p t ht
    exact h t ht
  · intro h A ring algebra complete normOne t ht
    exact h ⟨A⟩ t ht

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@correction_idempotent.{u})

end Reg.D5.S3.Quantum.Algebra.Approximate.Compression
