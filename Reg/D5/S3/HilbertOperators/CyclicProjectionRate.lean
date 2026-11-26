import D5.S3.HilbertOperators.CyclicProjectionRate
import Reg.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
open _root_.D5.S3.HilbertOperators.CyclicProjectionRate
open Reg.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
universe u v
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace CyclicRateAudit
private def observed (R : Realization signature.{u,v})
    {k : Type u} [RCLike k] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace k H] [CompleteSpace H] (Us : List (ClosedSubmodule k H))
    (x : H) (n : ℕ) : H :=
  R.readout () (@Parameters.mk k inferInstance H inferInstance inferInstance inferInstance Us) x n

private abbrev geometric_rate_arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {k : Type u} [RCLike k] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace k H] [CompleteSpace H] (Us : List (ClosedSubmodule k H)) (_ : Us ≠ [])
    (ell : ℝ) (_ : 0 < ell) (_ : ell ≤ 1) (_ : LinearRegular Us ell) (n : ℕ) (x : H),
    ‖observed R Us x n - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2 ≤
      (1 - ell ^ 2 / (Us.length : ℝ) ^ 2) ^ n *
        ‖x - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2
private theorem geometric_rate_actual : geometric_rate_arena.{u,v}.Law actual := @geometric_rate.{u,v}
def geometric_rate_attempt : Registration geometric_rate_arena.{u,v} (type_of% (@geometric_rate.{u,v})) where
  actual := actual
  bridge := Iff.rfl

private abbrev linear_regular_iff_uniform_geometric_arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {k : Type u} [RCLike k] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace k H] [CompleteSpace H] (Us : List (ClosedSubmodule k H)) (_ : Us ≠ []),
    (∃ ell : ℝ, 0 < ell ∧ ell ≤ 1 ∧ LinearRegular Us ell) ↔
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (x : H),
        ‖observed R Us x n - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2 ≤
          q ^ n * ‖x - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2
private theorem linear_regular_iff_uniform_geometric_actual : linear_regular_iff_uniform_geometric_arena.{u,v}.Law actual := @linear_regular_iff_uniform_geometric.{u,v}
def linear_regular_iff_uniform_geometric_attempt : Registration linear_regular_iff_uniform_geometric_arena.{u,v} (type_of% (@linear_regular_iff_uniform_geometric.{u,v})) where
  actual := actual
  bridge := Iff.rfl

end CyclicRateAudit
