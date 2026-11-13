import D5.S3.Quantum.Algebra.Approximate.RankOneCorner
import Reg.D5.S3.Quantum.Algebra.Approximate.RegularCompression

/-! The original rank-one telescope and its scalar-coefficient observation. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.Approximate.RankOneCorner

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.Approximate.RegularCompression
open _root_.Reg.D5.S3.Quantum.Algebra.Approximate.RegularCompression (Scope)

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.H × p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p qx => p.product.cornerPairing qx.1 qx.2 qx.2)
    (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@Product.rank_one_pairing_bounds.{u})

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (p : Scope.{u}) (Q : p.H) (τ : ℝ),
    p.product.RankOneInput Q τ →
    p.product.cornerUnit Q ≠ 0 ∧ 0 < (r.readout () p (Q, p.product.cornerUnit Q)).re ∧
      0 < p.product.cornerAlpha Q ∧
      |(r.readout () p (Q, p.product.cornerUnit Q)).re - 1| ≤
        219140 * (τ + p.M * p.δ) ∧
    ∀ (P : p.H), star P = P → p.product.p (p.product.mul P P - P) ≤ τ →
      ∀ (x : p.H), x ∈ p.product.corner P Q →
      r.readout () p (Q, x) • p.product.cornerUnit Q =
        p.product.compression Q Q (p.product.mul (star x) x) ∧
      0 ≤ (r.readout () p (Q, x)).re ∧
      ((r.readout () p (Q, x)).re = 0 ↔ x = 0) ∧
      ((1 - 260000 * (τ + p.M * p.δ) * p.M ^ 2) * ‖x‖ ^ 2 ≤
        p.product.cornerAlpha Q * (r.readout () p (Q, x)).re ∧
       p.product.cornerAlpha Q * (r.readout () p (Q, x)).re ≤
        (1 + 260000 * (τ + p.M * p.δ) * p.M ^ 2) * ‖x‖ ^ 2) ∧
      ((1 - (p.δ + 260000 * (τ + p.M * p.δ))) * p.product.p x ^ 2 ≤
        (r.readout () p (Q, x)).re * p.product.p (p.product.cornerUnit Q) ∧
       (r.readout () p (Q, x)).re * p.product.p (p.product.cornerUnit Q) ≤
        (1 + (p.δ + 260000 * (τ + p.M * p.δ))) * p.product.p x ^ 2)

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p Q τ I
    exact h I
  · intro h H normed inner finite starAdd starModule M δ D Q τ I
    exact h ⟨H, M, δ, D⟩ Q τ I

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@Product.rank_one_pairing_bounds.{u})

end Reg.D5.S3.Quantum.Algebra.Approximate.RankOneCorner
