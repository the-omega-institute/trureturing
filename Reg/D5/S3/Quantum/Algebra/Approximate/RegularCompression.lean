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

namespace ProductSupport

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.H × p.H × p.H × p.H × p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.product.p
    (p.product.compression s.1 s.2.2.1
      (p.product.mul s.2.2.2.1 s.2.2.2.2) -
        p.product.mul s.2.2.2.1 s.2.2.2.2)) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@Product.corner_product_support.{u})

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (p : Scope.{u}) (P Q R : p.H),
    star P = P → star Q = Q → star R = R →
    ∀ (τ : ℝ), 0 ≤ τ → τ + p.M * p.δ ≤ 1 / 1024 →
    p.product.p (p.product.mul P P - P) ≤ τ →
    p.product.p (p.product.mul Q Q - Q) ≤ τ →
    p.product.p (p.product.mul R R - R) ≤ τ →
    ∀ (x y : p.H), x ∈ p.product.corner P Q → y ∈ p.product.corner Q R →
    r.readout () p (P, Q, R, x, y) ≤
      260000 * (τ + p.M * p.δ) * p.product.p x * p.product.p y

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p P Q R hP hQ hR τ hτ hs hPP hQQ hRR x y hx hy
    exact h p.product P Q R hP hQ hR hτ hs hPP hQQ hRR hx hy
  · intro h H normed inner finite starAdd starModule M δ D P Q R hP hQ hR
      τ hτ hs hPP hQQ hRR x y hx hy
    exact h ⟨H, M, δ, D⟩ P Q R hP hQ hR τ hτ hs hPP hQQ hRR x y hx hy

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@Product.corner_product_support.{u})

end ProductSupport

namespace SquareNondegenerate

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.H × p.H × p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s =>
    p.product.compression s.2.1 s.2.1 (p.product.mul (star s.2.2) s.2.2))
    (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@Product.corner_square_nondegenerate.{u})

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (p : Scope.{u}) (P Q : p.H), star P = P → star Q = Q →
    ∀ (τ : ℝ), 0 ≤ τ → τ + p.M * p.δ ≤ 1 / 1024 →
    p.product.p (p.product.mul P P - P) ≤ τ →
    p.product.p (p.product.mul Q Q - Q) ≤ τ →
    520000 * (τ + p.M * p.δ) * p.M ^ 2 ≤ 1 →
    ∀ (x : p.H), x ∈ p.product.corner P Q →
    ‖x‖ ^ 2 / 2 ≤ (inner ℂ p.product.unit (r.readout () p (P, Q, x))).re ∧
      (r.readout () p (P, Q, x) = 0 ↔ x = 0)

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p P Q hP hQ τ hτ hs hPP hQQ hpositive x hx
    exact h p.product P Q hP hQ hτ hs hPP hQQ hpositive hx
  · intro h H normed inner finite starAdd starModule M δ D P Q hP hQ
      τ hτ hs hPP hQQ hpositive x hx
    exact h ⟨H, M, δ, D⟩ P Q hP hQ τ hτ hs hPP hQQ hpositive x hx

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@Product.corner_square_nondegenerate.{u})

end SquareNondegenerate

end Reg.D5.S3.Quantum.Algebra.Approximate.RegularCompression
