import D5.S3.Quantum.Algebra.Approximate.RegularCompression
import Reg.Support.DependentFamily

/-! The full original-product telescope and its actual compression readout. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.Approximate.RegularCompression

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.Approximate.RegularCompression

structure Scope where
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [finite : FiniteDimensional ℂ H]
  [starAdd : StarAddMonoid H]
  [starModule : StarModule ℂ H]
  M : ℝ
  δ : ℝ
  product : Product H M δ

attribute [instance] Scope.normed Scope.inner Scope.finite Scope.starAdd Scope.starModule

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.H × p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.H →L[ℂ] p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p pq => p.product.compression pq.1 pq.2) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@Product.compression_idempotent.{u})

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (p : Scope.{u}) (P Q : p.H), star P = P → star Q = Q →
    ∀ (τ : ℝ), 0 ≤ τ → τ + p.M * p.δ ≤ 1 / 1024 →
    p.product.p (p.product.mul P P - P) ≤ τ →
    p.product.p (p.product.mul Q Q - Q) ≤ τ →
    r.readout () p (P, Q) * r.readout () p (P, Q) = r.readout () p (P, Q)

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p P Q hP hQ τ hτ hs hPP hQQ
    exact h p.product P Q hP hQ hτ hs hPP hQQ
  · intro h H normed inner finite starAdd starModule M δ D P Q hP hQ τ hτ hs hPP hQQ
    exact h ⟨H, M, δ, D⟩ P Q hP hQ τ hτ hs hPP hQQ

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@Product.compression_idempotent.{u})

end Reg.D5.S3.Quantum.Algebra.Approximate.RegularCompression
