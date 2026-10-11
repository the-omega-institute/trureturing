/- GID: D5/S3/Quantum/Algebra/CStarSendov
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarSendov
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarSendov.claimSendov; result=D5/S3/Quantum/Algebra/CStarSendov.result; claim=D5/S3/Quantum/Algebra/CStarSendov.claimSendov
   digest: Critical-branch exchange refutes the C*-algebraic Sendov conjecture. -/

/-
proof_shape: cstarDisc: bind-only (consumer: CStarSendov.claimSendov, CStarSendov.critical_in_disc, CStarSendov.disc_iff_norm, CStarSendov.no_critical_in_half_disc, CStarSendov.result, CStarSendov.roots_in_disc, CStarSendovCommutative.claimSendovCommutative, CStarSendovCommutative.result)
proof_shape: IsConvexForm: bind-only (consumer: CStarSendov.claimSendov, CStarSendov.critical_convex_form, CStarSendov.result, CStarSendovCommutative.claimSendovCommutative, CStarSendovCommutative.result)
proof_shape: claimSendov: bind-only (consumer: CStarSendov.result)
proof_shape: Interval: bind-only (consumer: CStarSendov.Alg, CStarSendov.a, CStarSendov.bad_endpoints, CStarSendov.bminus, CStarSendov.bplus, CStarSendov.c, CStarSendov.c_endpoints, CStarSendov.c_norm_le, CStarSendov.cfun_ne_half, CStarSendov.continuous_sfun_interval, CStarSendov.critical_both, CStarSendov.critical_convex_form, CStarSendov.critical_gap, CStarSendov.critical_in_disc, CStarSendov.critical_unit_convex_form, CStarSendov.derivative_factorization, CStarSendov.disc_iff_norm, CStarSendov.discriminant_chartI_middle, CStarSendov.discriminant_chartR_left, CStarSendov.discriminant_chartR_right, CStarSendov.discriminant_ne_zero, CStarSendov.every_critical_branch, CStarSendov.no_critical_in_half_disc, CStarSendov.ordered_deriv_apply, CStarSendov.polygon_normSq_le, CStarSendov.result, CStarSendov.roots_in_disc, CStarSendov.s, CStarSendov.s_norm_le, CStarSendov.square_root_endpoints, CStarSendov.square_root_ne_zero, CStarSendov.square_root_squared, CStarSendov.t0, CStarSendov.t6, CStarSendovCommutative.cubic_cstar_deriv_iff, CStarSendovCommutative.cubic_has_cstar_deriv, CStarSendovCommutative.cubic_increment_identity, CStarSendovCommutative.cubic_quotient_identity, CStarSendovCommutative.invertibles_dense, CStarSendovCommutative.polynomial_pair_approximation, CStarSendovCommutative.result)
proof_shape: Alg: bind-only (consumer: CStarSendov.a, CStarSendov.bad_endpoints, CStarSendov.bminus, CStarSendov.bplus, CStarSendov.bs, CStarSendov.c_endpoints, CStarSendov.c_norm_le, CStarSendov.critical_both, CStarSendov.critical_convex_form, CStarSendov.critical_gap, CStarSendov.critical_in_disc, CStarSendov.critical_unit_convex_form, CStarSendov.derivative_factorization, CStarSendov.disc_iff_norm, CStarSendov.every_critical_branch, CStarSendov.no_critical_in_half_disc, CStarSendov.ordered_deriv_apply, CStarSendov.result, CStarSendov.roots_in_disc, CStarSendov.s_norm_le, CStarSendov.square_root_endpoints, CStarSendov.square_root_ne_zero, CStarSendov.square_root_squared, CStarSendovCommutative.cubic_cstar_deriv_iff, CStarSendovCommutative.cubic_has_cstar_deriv, CStarSendovCommutative.cubic_increment_identity, CStarSendovCommutative.cubic_quotient_identity, CStarSendovCommutative.invertibles_dense, CStarSendovCommutative.polynomial_pair_approximation, CStarSendovCommutative.result)
proof_shape: two_branch_exhaustion: bind-only (consumer: CStarSendov.every_critical_branch)
proof_shape: ordered_deriv_cubic: bind-only (consumer: CStarSendov.ordered_deriv_apply)
proof_shape: ramp: bind-only (consumer: CStarSendov.c_endpoints, CStarSendov.continuous_cfun, CStarSendov.continuous_ramp, CStarSendov.cx, CStarSendov.cy, CStarSendov.discriminant_at_four, CStarSendov.discriminant_at_two, CStarSendov.polygon_segments, CStarSendov.ramp_middle, CStarSendov.ramp_one, CStarSendov.ramp_zero, CStarSendov.square_root_endpoints)
proof_shape: continuous_ramp: bind-only (consumer: CStarSendov.continuous_cfun)
proof_shape: ramp_zero: bind-only (consumer: CStarSendov.polygon_segments)
proof_shape: ramp_one: bind-only (consumer: CStarSendov.polygon_segments)
proof_shape: ramp_middle: bind-only (consumer: CStarSendov.polygon_segments)
proof_shape: cx: bind-only (consumer: CStarSendov.c_endpoints, CStarSendov.cfun, CStarSendov.cfun_re, CStarSendov.continuous_cfun, CStarSendov.discriminant_at_four, CStarSendov.discriminant_at_two, CStarSendov.square_root_endpoints)
proof_shape: cy: bind-only (consumer: CStarSendov.c_endpoints, CStarSendov.cfun, CStarSendov.cfun_im, CStarSendov.cfun_re, CStarSendov.continuous_cfun, CStarSendov.discriminant_at_four, CStarSendov.discriminant_at_two, CStarSendov.square_root_endpoints)
proof_shape: cfun: bind-only (consumer: CStarSendov.c, CStarSendov.c_endpoints, CStarSendov.c_norm_le, CStarSendov.cfun_im, CStarSendov.cfun_ne_half, CStarSendov.cfun_re, CStarSendov.continuous_cfun, CStarSendov.continuous_dfun, CStarSendov.dfun, CStarSendov.discriminant_at_four, CStarSendov.discriminant_at_two, CStarSendov.discriminant_chartI_middle, CStarSendov.discriminant_chartR_left, CStarSendov.discriminant_chartR_right, CStarSendov.discriminant_ne_zero, CStarSendov.polygon_normSq_le, CStarSendov.polygon_segments, CStarSendov.square_root_endpoints)
proof_shape: cfun_re: bind-only (consumer: CStarSendov.polygon_segments)
proof_shape: cfun_im: bind-only (consumer: CStarSendov.polygon_segments)
proof_shape: continuous_cfun: bind-only (consumer: CStarSendov.c, CStarSendov.c_endpoints, CStarSendov.continuous_dfun)
proof_shape: c: bind-only (consumer: CStarSendov.a, CStarSendov.bad_endpoints, CStarSendov.bminus, CStarSendov.bplus, CStarSendov.c_endpoints, CStarSendov.c_norm_le, CStarSendov.critical_gap, CStarSendov.critical_in_disc, CStarSendov.critical_unit_convex_form, CStarSendov.derivative_factorization, CStarSendov.every_critical_branch, CStarSendov.ordered_deriv_apply, CStarSendov.result, CStarSendov.roots_in_disc, CStarSendov.s_norm_le, CStarSendov.square_root_ne_zero, CStarSendov.square_root_squared, CStarSendovCommutative.cubic_has_cstar_deriv, CStarSendovCommutative.cubic_increment_identity, CStarSendovCommutative.cubic_quotient_identity, CStarSendovCommutative.result)
proof_shape: polygon_segments: bind-only (consumer: CStarSendov.cfun_ne_half, CStarSendov.discriminant_chartI_middle, CStarSendov.discriminant_chartR_left, CStarSendov.discriminant_chartR_right, CStarSendov.discriminant_ne_zero, CStarSendov.polygon_normSq_le)
proof_shape: dfun: bind-only (consumer: CStarSendov.continuous_dfun, CStarSendov.continuous_sfun_interval, CStarSendov.discriminant_at_four, CStarSendov.discriminant_at_two, CStarSendov.discriminant_chartI_middle, CStarSendov.discriminant_chartR_left, CStarSendov.discriminant_chartR_right, CStarSendov.discriminant_ne_zero, CStarSendov.sfun, CStarSendov.square_root_endpoints, CStarSendov.square_root_squared)
proof_shape: continuous_dfun: bind-only (consumer: CStarSendov.continuous_sfun_interval)
proof_shape: polygon_normSq_le: bind-only (consumer: CStarSendov.c_norm_le)
proof_shape: discriminant_ne_zero: bind-only (consumer: CStarSendov.square_root_ne_zero)
proof_shape: discriminant_chartR_left: bind-only (consumer: CStarSendov.continuous_sfun_interval, CStarSendov.square_root_squared)
proof_shape: discriminant_chartI_middle: bind-only (consumer: CStarSendov.continuous_sfun_interval, CStarSendov.square_root_squared)
proof_shape: discriminant_chartR_right: bind-only (consumer: CStarSendov.continuous_sfun_interval, CStarSendov.square_root_squared)
proof_shape: cfun_ne_half: bind-only (consumer: CStarSendov.critical_gap, CStarSendov.critical_unit_convex_form)
proof_shape: rootU: bind-only (consumer: CStarSendov.continuousAt_rootR, CStarSendov.continuous_rootU, CStarSendov.rootR, CStarSendov.rootR_im, CStarSendov.rootR_re, CStarSendov.rootR_sq, CStarSendov.rootV_pos, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.square_root_endpoints)
proof_shape: rootV: bind-only (consumer: CStarSendov.continuousAt_rootI, CStarSendov.continuous_rootV, CStarSendov.rootI, CStarSendov.rootI_im, CStarSendov.rootI_re, CStarSendov.rootI_sq, CStarSendov.rootV_pos, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper)
proof_shape: rootR: bind-only (consumer: CStarSendov.continuousAt_rootR, CStarSendov.continuous_sfun_interval, CStarSendov.rootR_im, CStarSendov.rootR_re, CStarSendov.rootR_sq, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.sfun, CStarSendov.square_root_endpoints, CStarSendov.square_root_squared)
proof_shape: rootI: bind-only (consumer: CStarSendov.continuousAt_rootI, CStarSendov.continuous_sfun_interval, CStarSendov.rootI_im, CStarSendov.rootI_re, CStarSendov.rootI_sq, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.sfun, CStarSendov.square_root_endpoints, CStarSendov.square_root_squared)
proof_shape: rootR_re: bind-only (consumer: CStarSendov.rootR_sq, CStarSendov.square_root_endpoints)
proof_shape: rootR_im: bind-only (consumer: CStarSendov.rootR_sq, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.square_root_endpoints)
proof_shape: rootI_re: bind-only (consumer: CStarSendov.rootI_sq)
proof_shape: rootI_im: bind-only (consumer: CStarSendov.rootI_sq, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper)
proof_shape: norm_squared: bind-only (consumer: CStarSendov.rootI_sq, CStarSendov.rootR_sq, CStarSendov.rootU_pos)
proof_shape: rootU_pos: bind-only (consumer: CStarSendov.continuous_sfun_interval, CStarSendov.rootV_pos, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.square_root_squared)
proof_shape: rootV_pos: bind-only (consumer: CStarSendov.continuous_sfun_interval, CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.square_root_squared)
proof_shape: rootR_sq: bind-only (consumer: CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.square_root_squared)
proof_shape: rootI_sq: bind-only (consumer: CStarSendov.roots_agree_lower, CStarSendov.roots_agree_upper, CStarSendov.square_root_squared)
proof_shape: continuous_rootU: bind-only (consumer: CStarSendov.continuousAt_rootR)
proof_shape: continuous_rootV: bind-only (consumer: CStarSendov.continuousAt_rootI)
proof_shape: continuousAt_rootR: bind-only (consumer: CStarSendov.continuous_sfun_interval)
proof_shape: continuousAt_rootI: bind-only (consumer: CStarSendov.continuous_sfun_interval)
proof_shape: roots_agree_upper: bind-only (consumer: CStarSendov.continuous_sfun_interval)
proof_shape: roots_agree_lower: bind-only (consumer: CStarSendov.continuous_sfun_interval)
proof_shape: sfun: bind-only (consumer: CStarSendov.s, CStarSendov.square_root_endpoints, CStarSendov.square_root_squared)
proof_shape: discriminant_at_two: bind-only (consumer: CStarSendov.continuous_sfun_interval)
proof_shape: discriminant_at_four: bind-only (consumer: CStarSendov.continuous_sfun_interval)
proof_shape: continuous_sfun_interval: bind-only (consumer: CStarSendov.s, CStarSendov.square_root_endpoints)
proof_shape: s: bind-only (consumer: CStarSendov.bad_endpoints, CStarSendov.bminus, CStarSendov.bplus, CStarSendov.critical_in_disc, CStarSendov.derivative_factorization, CStarSendov.every_critical_branch, CStarSendov.s_norm_le, CStarSendov.square_root_endpoints, CStarSendov.square_root_ne_zero, CStarSendov.square_root_squared)
proof_shape: square_root_squared: bind-only (consumer: CStarSendov.derivative_factorization, CStarSendov.every_critical_branch, CStarSendov.s_norm_le, CStarSendov.square_root_ne_zero)
proof_shape: square_root_ne_zero: bind-only (consumer: CStarSendov.every_critical_branch)
proof_shape: t0: bind-only (consumer: CStarSendov.bad_endpoints, CStarSendov.c_endpoints, CStarSendov.every_critical_branch, CStarSendov.no_critical_in_half_disc, CStarSendov.square_root_endpoints)
proof_shape: t6: bind-only (consumer: CStarSendov.bad_endpoints, CStarSendov.c_endpoints, CStarSendov.no_critical_in_half_disc, CStarSendov.square_root_endpoints)
proof_shape: c_endpoints: bind-only (consumer: CStarSendov.bad_endpoints)
proof_shape: square_root_endpoints: bind-only (consumer: CStarSendov.bad_endpoints)
proof_shape: a: bind-only (consumer: CStarSendov.critical_both, CStarSendov.critical_convex_form, CStarSendov.critical_gap, CStarSendov.critical_unit_convex_form, CStarSendov.derivative_factorization, CStarSendov.every_critical_branch, CStarSendov.no_critical_in_half_disc, CStarSendov.ordered_deriv_apply, CStarSendov.result, CStarSendov.roots_in_disc, CStarSendovCommutative.cubic_cstar_deriv_iff, CStarSendovCommutative.cubic_has_cstar_deriv, CStarSendovCommutative.cubic_increment_identity, CStarSendovCommutative.cubic_quotient_identity, CStarSendovCommutative.result)
proof_shape: bplus: bind-only (consumer: CStarSendov.bad_endpoints, CStarSendov.bs, CStarSendov.critical_both, CStarSendov.critical_in_disc, CStarSendov.derivative_factorization, CStarSendov.no_critical_in_half_disc, CStarSendov.result, CStarSendovCommutative.result)
proof_shape: bminus: bind-only (consumer: CStarSendov.bad_endpoints, CStarSendov.bs, CStarSendov.critical_both, CStarSendov.critical_in_disc, CStarSendov.derivative_factorization, CStarSendov.no_critical_in_half_disc, CStarSendov.result, CStarSendovCommutative.result)
proof_shape: bs: bind-only (consumer: CStarSendov.result, CStarSendovCommutative.result)
proof_shape: ordered_deriv_apply: bind-only (consumer: CStarSendov.critical_gap, CStarSendov.critical_unit_convex_form, CStarSendov.derivative_factorization, CStarSendov.every_critical_branch, CStarSendovCommutative.cubic_increment_identity)
proof_shape: derivative_factorization: bind-only (consumer: CStarSendov.critical_both)
proof_shape: critical_both: bind-only (consumer: CStarSendov.result, CStarSendovCommutative.result)
proof_shape: every_critical_branch: bind-only (consumer: CStarSendov.no_critical_in_half_disc)
proof_shape: disc_iff_norm: bind-only (consumer: CStarSendov.critical_in_disc, CStarSendov.no_critical_in_half_disc, CStarSendov.roots_in_disc)
proof_shape: c_norm_le: bind-only (consumer: CStarSendov.critical_in_disc, CStarSendov.roots_in_disc, CStarSendov.s_norm_le)
proof_shape: s_norm_le: bind-only (consumer: CStarSendov.critical_in_disc)
proof_shape: roots_in_disc: bind-only (consumer: CStarSendov.result, CStarSendovCommutative.result)
proof_shape: critical_in_disc: bind-only (consumer: CStarSendov.result, CStarSendovCommutative.result)
proof_shape: bad_endpoints: bind-only (consumer: CStarSendov.no_critical_in_half_disc)
proof_shape: no_critical_in_half_disc: bind-only (consumer: CStarSendov.result, CStarSendovCommutative.result)
proof_shape: scalar_root_ne_roots: bind-only (consumer: CStarSendov.critical_gap, CStarSendov.critical_unit_convex_form)
proof_shape: inverse_sum_of_products: bind-only (consumer: CStarSendov.scalar_inverse_sum)
proof_shape: scalar_inverse_sum: bind-only (consumer: CStarSendov.scalar_weighted_residual)
proof_shape: qscalar: bind-only (consumer: CStarSendov.critical_unit_convex_form, CStarSendov.scalar_weighted_residual)
proof_shape: scalar_weighted_residual: bind-only (consumer: CStarSendov.critical_unit_convex_form)
proof_shape: critical_gap: bind-only (consumer: CStarSendov.critical_unit_convex_form)
proof_shape: critical_unit_convex_form: bind-only (consumer: CStarSendov.critical_convex_form)
proof_shape: critical_convex_form: bind-only (consumer: CStarSendov.result, CStarSendovCommutative.result)
proof_shape: result: bind-only (consumer: settling result)
escape_witness: none
admission_basis: open-problem-resolution (#15036; Refuted)
Direct frozen dependencies (constant owners):
  D5/S3/Quantum/Algebra/CStarSchoenberg.orderedDeriv statement_id: sha256:ce1938b197e00c32d6073b1ab7f80e347fafc998daeebfbe011a7ba6ce98cba7
Escape audit unfinished for the six public helpers: https://github.com/the-omega-institute/trureturing/issues/15114
Positive means nonnegative; the constructed weights are also invertible.
Only degrees at least two and unital algebras in Type are encoded.
-/

import D5.S3.Quantum.Algebra.CStarSchoenberg
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Units

open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Algebra
namespace D5.S3.Quantum.Algebra.CStarSendov
noncomputable section

def cstarDisc {A : Type} [CStarAlgebra A] [PartialOrder A] (a : A) (r : ℝ) : Set A :=
  {z | (z - a) * star (z - a) ≤ ((Real.sqrt r : ℝ) : ℂ) • (1 : A)}

def IsConvexForm {A : Type} [CStarAlgebra A] [PartialOrder A] {n : ℕ}
    (a : Fin n → A) (z : A) : Prop :=
  ∃ w : Fin n → A, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ z = ∑ j, w j * a j

def claimSendov : Prop :=
  ∀ (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (n : ℕ),
    2 ≤ n → ∀ a : Fin n → A, (∀ j, a j ∈ cstarDisc 0 1) →
    ∀ b : Fin (n - 1) → A, (∀ k, CStarSchoenberg.orderedDeriv a (b k) = 0) →
    (∀ k, b k ∈ cstarDisc 0 1) → (∀ k, IsConvexForm a (b k)) →
    ∀ j, ∃ z, CStarSchoenberg.orderedDeriv a z = 0 ∧ z ∈ cstarDisc (a j) 1

abbrev Interval := Set.Icc (0 : ℝ) 6
abbrev Alg := C(Interval, ℂ)
end
end D5.S3.Quantum.Algebra.CStarSendov


open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Algebra
open D5.S3.Quantum.Algebra.CStarSendov
noncomputable section

namespace D5.S3.Quantum.Algebra.CStarSendov

-- The square-root quotient is a map into a discrete two-point set.
private theorem two_branch_exhaustion {X : Type} [TopologicalSpace X] [PreconnectedSpace X]
    [Nonempty X] (c s b : C(X, ℂ)) (hs : ∀ x, s x ≠ 0)
    (hsq : ∀ x, (s x)^2 = (c x)^2 + 3 / 4)
    (hb : ∀ x, 3 * (b x)^2 - 2 * c x * b x - 1 / 4 = 0) :
    b = (1/3 : ℂ) • (c + s) ∨ b = (1/3 : ℂ) • (c - s) := by
  let h : X → ℂ := fun x => (3 * b x - c x) / s x
  have hc : Continuous h :=
    ((continuous_const.mul b.continuous).sub c.continuous).div s.continuous hs
  have hsq1 (x : X) : (h x)^2 = 1 := by
    dsimp [h]
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 (hs x))]
    calc
      (3 * b x - c x)^2 = (c x)^2 + 3 / 4 := by linear_combination 3 * hb x
      _ = (s x)^2 := (hsq x).symm
  have hm : Set.MapsTo h Set.univ ({1, -1} : Set ℂ) := by
    intro x _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (sq_eq_one_iff.mp (hsq1 x))
  let x0 : X := Classical.choice ‹Nonempty X›
  have hh (x : X) : h x = h x0 :=
    isPreconnected_univ.constant_of_mapsTo (Set.toFinite _).isDiscrete hc.continuousOn hm
      (Set.mem_univ x) (Set.mem_univ x0)
  rcases sq_eq_one_iff.mp (hsq1 x0) with hp | hn
  · left
    ext x
    have he : (3 * b x - c x) / s x = 1 := (hh x).trans hp
    have he' := (div_eq_iff (hs x)).mp he
    change b x = (1/3 : ℂ) * (c x + s x)
    rw [one_div_mul_eq_div]
    apply (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).mpr
    linear_combination he'
  · right
    ext x
    have he : (3 * b x - c x) / s x = -1 := (hh x).trans hn
    have he' := (div_eq_iff (hs x)).mp he
    change b x = (1/3 : ℂ) * (c x - s x)
    rw [one_div_mul_eq_div]
    apply (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).mpr
    linear_combination he'

-- A cubic's ordered derivative and its two explicit roots.
private theorem ordered_deriv_cubic (c z : ℂ) :
    CStarSchoenberg.orderedDeriv ![(1/2 : ℂ), -1/2, c] z =
      3 * z^2 - 2 * c * z - 1/4 := by
  simp [CStarSchoenberg.orderedDeriv, Fin.sum_univ_succ, List.ofFn_succ]
  ring

end D5.S3.Quantum.Algebra.CStarSendov


open scoped ComplexOrder
open D5.S3.Quantum.Algebra.CStarSendov
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendov

def ramp (t : ℝ) : ℝ := min 1 (max 0 t)
@[fun_prop] private theorem continuous_ramp : Continuous ramp := by unfold ramp; fun_prop
private theorem ramp_zero {t : ℝ} (h : t ≤ 0) : ramp t = 0 := by simp [ramp, max_eq_left h]
private theorem ramp_one {t : ℝ} (h : 1 ≤ t) : ramp t = 1 := by
  simp [ramp, max_eq_right (le_trans (show (0:ℝ) ≤ 1 by norm_num) h), min_eq_left h]
private theorem ramp_middle {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ramp t = t := by
  simp [ramp, max_eq_right h0, min_eq_right h1]

def cx (t : ℝ) : ℝ := -9/10 + 4/5 * ramp t + 1/5 * ramp (t-1) -
  1/5 * ramp (t-3) - 4/5 * ramp (t-5)
def cy (t : ℝ) : ℝ := 4/5 * ramp t + 1/10 * ramp (t-2) -
  1/10 * ramp (t-4) - 4/5 * ramp (t-5)
def cfun (t : ℝ) : ℂ := (cx t : ℂ) + (cy t : ℂ) * Complex.I
@[simp] private theorem cfun_re (t : ℝ) : (cfun t).re = cx t := by simp [cfun]
@[simp] private theorem cfun_im (t : ℝ) : (cfun t).im = cy t := by simp [cfun]
@[fun_prop] private theorem continuous_cfun : Continuous cfun := by
  unfold cfun cx cy
  fun_prop

def c : Alg := ⟨fun t => cfun t, continuous_cfun.comp continuous_subtype_val⟩

private theorem polygon_segments {t : ℝ} (h0 : 0 ≤ t) (h6 : t ≤ 6) :
  (t ≤ 1 ∧ cfun t = ⟨-9/10 + 4/5*t, 4/5*t⟩) ∨
  (1 ≤ t ∧ t ≤ 2 ∧ cfun t = ⟨-1/10 + 1/5*(t-1), 4/5⟩) ∨
  (2 ≤ t ∧ t ≤ 3 ∧ cfun t = ⟨1/10, 4/5 + 1/10*(t-2)⟩) ∨
  (3 ≤ t ∧ t ≤ 4 ∧ cfun t = ⟨1/10 - 1/5*(t-3), 9/10⟩) ∨
  (4 ≤ t ∧ t ≤ 5 ∧ cfun t = ⟨-1/10, 9/10 - 1/10*(t-4)⟩) ∨
  (5 ≤ t ∧ cfun t = ⟨-1/10 - 4/5*(t-5), 4/5 - 4/5*(t-5)⟩) := by
  by_cases h1 : t ≤ 1
  · left
    refine ⟨h1, ?_⟩
    apply Complex.ext <;> simp only [cfun_re, cfun_im, cx, cy]
    all_goals simp only [ramp_middle h0 h1,
      ramp_zero (by linarith : t-1 ≤ 0), ramp_zero (by linarith : t-2 ≤ 0),
      ramp_zero (by linarith : t-3 ≤ 0), ramp_zero (by linarith : t-4 ≤ 0),
      ramp_zero (by linarith : t-5 ≤ 0)] <;> ring
  · have hl1 : 1 ≤ t := le_of_lt (lt_of_not_ge h1)
    right
    by_cases h2 : t ≤ 2
    · left
      refine ⟨hl1, h2, ?_⟩
      apply Complex.ext <;> simp only [cfun_re, cfun_im, cx, cy]
      all_goals simp only [ramp_one hl1, ramp_middle (by linarith : 0 ≤ t-1) (by linarith : t-1 ≤ 1),
        ramp_zero (by linarith : t-2 ≤ 0), ramp_zero (by linarith : t-3 ≤ 0),
        ramp_zero (by linarith : t-4 ≤ 0), ramp_zero (by linarith : t-5 ≤ 0)] <;> ring
    · have hl2 : 2 ≤ t := le_of_lt (lt_of_not_ge h2)
      right
      by_cases h3 : t ≤ 3
      · left
        refine ⟨hl2, h3, ?_⟩
        apply Complex.ext <;> simp only [cfun_re, cfun_im, cx, cy]
        all_goals simp only [ramp_one (by linarith : 1 ≤ t), ramp_one (by linarith : 1 ≤ t-1),
          ramp_middle (by linarith : 0 ≤ t-2) (by linarith : t-2 ≤ 1),
          ramp_zero (by linarith : t-3 ≤ 0), ramp_zero (by linarith : t-4 ≤ 0),
          ramp_zero (by linarith : t-5 ≤ 0)] <;> ring
      · have hl3 : 3 ≤ t := le_of_lt (lt_of_not_ge h3)
        right
        by_cases h4 : t ≤ 4
        · left
          refine ⟨hl3, h4, ?_⟩
          apply Complex.ext <;> simp only [cfun_re, cfun_im, cx, cy]
          all_goals simp only [ramp_one (by linarith : 1 ≤ t), ramp_one (by linarith : 1 ≤ t-1),
            ramp_one (by linarith : 1 ≤ t-2),
            ramp_middle (by linarith : 0 ≤ t-3) (by linarith : t-3 ≤ 1),
            ramp_zero (by linarith : t-4 ≤ 0), ramp_zero (by linarith : t-5 ≤ 0)] <;> ring
        · have hl4 : 4 ≤ t := le_of_lt (lt_of_not_ge h4)
          right
          by_cases h5 : t ≤ 5
          · left
            refine ⟨hl4, h5, ?_⟩
            apply Complex.ext <;> simp only [cfun_re, cfun_im, cx, cy]
            all_goals simp only [ramp_one (by linarith : 1 ≤ t), ramp_one (by linarith : 1 ≤ t-1),
              ramp_one (by linarith : 1 ≤ t-2), ramp_one (by linarith : 1 ≤ t-3),
              ramp_middle (by linarith : 0 ≤ t-4) (by linarith : t-4 ≤ 1),
              ramp_zero (by linarith : t-5 ≤ 0)] <;> ring
          · right
            refine ⟨le_of_lt (lt_of_not_ge h5), ?_⟩
            apply Complex.ext <;> simp only [cfun_re, cfun_im, cx, cy]
            all_goals simp only [ramp_one (by linarith : 1 ≤ t), ramp_one (by linarith : 1 ≤ t-1),
              ramp_one (by linarith : 1 ≤ t-2), ramp_one (by linarith : 1 ≤ t-3),
              ramp_one (by linarith : 1 ≤ t-4),
              ramp_middle (by linarith : 0 ≤ t-5) (by linarith : t-5 ≤ 1)] <;> ring

end D5.S3.Quantum.Algebra.CStarSendov

open scoped ComplexOrder
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendov

def dfun (t : ℝ) : ℂ := (cfun t)^2 + 3/4
@[fun_prop] private theorem continuous_dfun : Continuous dfun := by unfold dfun; fun_prop
private theorem polygon_normSq_le (t : Interval) : Complex.normSq (cfun t) ≤ 82/100 := by
  have h0 := t.property.1
  have h6 := t.property.2
  rcases polygon_segments t.property.1 t.property.2 with
    ⟨ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, he⟩
  all_goals rw [he]; simp only [Complex.normSq_apply]
  · nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr ht)]
  · nlinarith [mul_nonneg (show 0 ≤ (t:ℝ)-1 by linarith) (show 0 ≤ 2-(t:ℝ) by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ (t:ℝ)-2 by linarith) (show 0 ≤ 3-(t:ℝ) by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ (t:ℝ)-3 by linarith) (show 0 ≤ 4-(t:ℝ) by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ (t:ℝ)-4 by linarith) (show 0 ≤ 5-(t:ℝ) by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ (t:ℝ)-5 by linarith) (show 0 ≤ 6-(t:ℝ) by linarith)]

private theorem discriminant_ne_zero (t : Interval) : dfun t ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  have h0 := t.property.1
  have h6 := t.property.2
  rcases polygon_segments t.property.1 t.property.2 with
    ⟨ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, ht, he⟩ | ⟨hl, he⟩
  all_goals simp only [dfun, he, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.zero_re, Complex.zero_im] at hr hi
  all_goals norm_num at hr hi
  all_goals nlinarith [t.property.1, t.property.2]

-- Both charts avoid their cuts on the subintervals where they are used.
private theorem discriminant_chartR_left (t : Interval) (ht : (t:ℝ) ≤ 2) :
    0 < (dfun t).re ∨ (dfun t).im ≠ 0 := by
  have h0 := t.property.1
  have h6 := t.property.2
  rcases polygon_segments t.property.1 t.property.2 with
    ⟨h1, he⟩ | ⟨hl, h2, he⟩ | ⟨hl, h3, he⟩ | ⟨hl, h4, he⟩ | ⟨hl, h5, he⟩ | ⟨hl, he⟩
  all_goals simp only [dfun, he, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.div_re, Complex.div_im]
  all_goals norm_num
  all_goals first | left; nlinarith [t.property.1, t.property.2] | right; intro hi; nlinarith [t.property.1, t.property.2]

private theorem discriminant_chartI_middle (t : Interval) (hl : 2 ≤ (t:ℝ)) (ht : (t:ℝ) ≤ 4) :
    (dfun t).re < 0 ∨ (dfun t).im ≠ 0 := by
  have h0 := t.property.1
  have h6 := t.property.2
  rcases polygon_segments t.property.1 t.property.2 with
    ⟨h1, he⟩ | ⟨hl1, h2, he⟩ | ⟨hl2, h3, he⟩ | ⟨hl3, h4, he⟩ | ⟨hl4, h5, he⟩ | ⟨hl5, he⟩
  all_goals simp only [dfun, he, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.div_re, Complex.div_im]
  all_goals norm_num
  all_goals first | left; nlinarith [mul_nonneg (show 0 ≤ (t:ℝ)-3 by linarith) (show 0 ≤ 4-(t:ℝ) by linarith)] | right; intro hi; nlinarith

private theorem discriminant_chartR_right (t : Interval) (hl : 4 ≤ (t:ℝ)) :
    0 < (dfun t).re ∨ (dfun t).im ≠ 0 := by
  have h0 := t.property.1
  have h6 := t.property.2
  rcases polygon_segments t.property.1 t.property.2 with
    ⟨h1, he⟩ | ⟨hl1, h2, he⟩ | ⟨hl2, h3, he⟩ | ⟨hl3, h4, he⟩ | ⟨hl4, h5, he⟩ | ⟨hl5, he⟩
  all_goals simp only [dfun, he, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.div_re, Complex.div_im]
  all_goals norm_num
  all_goals first | left; nlinarith | right; intro hi; nlinarith

private theorem cfun_ne_half (t : Interval) : cfun t ≠ (1/2:ℂ) ∧ cfun t ≠ (-1/2:ℂ) := by
  constructor <;> intro h
  all_goals have hr := congrArg Complex.re h; have hi := congrArg Complex.im h
  all_goals rcases polygon_segments t.property.1 t.property.2 with
    ⟨h1, he⟩ | ⟨hl, h2, he⟩ | ⟨hl, h3, he⟩ | ⟨hl, h4, he⟩ | ⟨hl, h5, he⟩ | ⟨hl, he⟩
  all_goals (norm_num [he] at * <;> linarith)

end D5.S3.Quantum.Algebra.CStarSendov


open scoped ComplexOrder
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendov

def rootU (z : ℂ) : ℝ := Real.sqrt ((‖z‖ + z.re) / 2)
def rootV (z : ℂ) : ℝ := Real.sqrt ((‖z‖ - z.re) / 2)
def rootR (z : ℂ) : ℂ := (rootU z : ℂ) + ((z.im / (2 * rootU z) : ℝ) : ℂ) * Complex.I
def rootI (z : ℂ) : ℂ := ((z.im / (2 * rootV z) : ℝ) : ℂ) + (rootV z : ℂ) * Complex.I

@[simp] private theorem rootR_re (z : ℂ) : (rootR z).re = rootU z := by
  simp only [rootR, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
@[simp] private theorem rootR_im (z : ℂ) : (rootR z).im = z.im / (2 * rootU z) := by
  simp only [rootR, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
@[simp] private theorem rootI_re (z : ℂ) : (rootI z).re = z.im / (2 * rootV z) := by
  simp only [rootI, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
@[simp] private theorem rootI_im (z : ℂ) : (rootI z).im = rootV z := by
  simp only [rootI, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

 private theorem norm_squared (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem rootU_pos (z : ℂ) (h : 0 < z.re ∨ z.im ≠ 0) : 0 < rootU z := by
  apply Real.sqrt_pos.mpr
  have hr := (abs_le.mp (Complex.abs_re_le_norm z)).1
  rcases h with h | h
  · have hn := norm_nonneg z
    linarith
  · have hy : 0 < z.im^2 := sq_pos_of_ne_zero h
    have hn := norm_squared z
    have hp : 0 < ‖z‖ + z.re := by
      by_contra hp
      have he : ‖z‖ = -z.re := by linarith
      rw [he] at hn
      nlinarith
    linarith

private theorem rootV_pos (z : ℂ) (h : z.re < 0 ∨ z.im ≠ 0) : 0 < rootV z := by
  have h' := rootU_pos (-z) (by simpa using h)
  simpa [rootU, rootV] using h'

private theorem rootR_sq (z : ℂ) (h : 0 < rootU z) : (rootR z)^2 = z := by
  have hu : (rootU z)^2 = (‖z‖ + z.re)/2 := Real.sq_sqrt (by
    have := (abs_le.mp (Complex.abs_re_le_norm z)).1
    linarith)
  have hn := norm_squared z
  have he : (z.im / (2 * rootU z))^2 = (‖z‖ - z.re)/2 := by
    rw [div_pow, mul_pow, hu]
    apply (div_eq_iff (by nlinarith [sq_pos_of_pos h] : (2:ℝ)^2 * ((‖z‖+z.re)/2) ≠ 0)).mpr
    nlinarith
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, rootR_re, rootR_im]
    nlinarith
  · simp only [pow_two, Complex.mul_im, rootR_re, rootR_im]
    field_simp [ne_of_gt h] <;> ring

 private theorem rootI_sq (z : ℂ) (h : 0 < rootV z) : (rootI z)^2 = z := by
  have hv : (rootV z)^2 = (‖z‖ - z.re)/2 := Real.sq_sqrt (by
    have := Complex.re_le_norm z
    linarith)
  have hn := norm_squared z
  have he : (z.im / (2 * rootV z))^2 = (‖z‖ + z.re)/2 := by
    rw [div_pow, mul_pow, hv]
    apply (div_eq_iff (by nlinarith [sq_pos_of_pos h] : (2:ℝ)^2 * ((‖z‖-z.re)/2) ≠ 0)).mpr
    nlinarith
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, rootI_re, rootI_im]
    nlinarith
  · simp only [pow_two, Complex.mul_im, rootI_re, rootI_im]
    field_simp [ne_of_gt h] <;> ring

@[fun_prop] private theorem continuous_rootU : Continuous rootU := by unfold rootU; fun_prop
@[fun_prop] private theorem continuous_rootV : Continuous rootV := by unfold rootV; fun_prop

private theorem continuousAt_rootR (z : ℂ) (h : 0 < rootU z) : ContinuousAt rootR z := by
  unfold rootR
  fun_prop (disch := positivity)

private theorem continuousAt_rootI (z : ℂ) (h : 0 < rootV z) : ContinuousAt rootI z := by
  unfold rootI
  fun_prop (disch := positivity)

private theorem roots_agree_upper (z : ℂ) (h : 0 < z.im) : rootR z = rootI z := by
  have hu := rootU_pos z (Or.inr h.ne')
  have hv := rootV_pos z (Or.inr h.ne')
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((rootR_sq z hu).trans (rootI_sq z hv).symm) with he | he
  · exact he
  · have him := congrArg Complex.im he
    simp only [rootR_im, Complex.neg_im, rootI_im] at him
    have hd : 0 < z.im / (2 * rootU z) := div_pos h (by positivity)
    linarith

private theorem roots_agree_lower (z : ℂ) (h : z.im < 0) : -rootR z = rootI z := by
  have hu := rootU_pos z (Or.inr h.ne)
  have hv := rootV_pos z (Or.inr h.ne)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((rootR_sq z hu).trans (rootI_sq z hv).symm) with he | he
  · have him := congrArg Complex.im he
    simp only [rootR_im, rootI_im] at him
    have hd : z.im / (2 * rootU z) < 0 := div_neg_of_neg_of_pos h (by positivity)
    linarith
  · exact neg_eq_iff_eq_neg.mpr he

end D5.S3.Quantum.Algebra.CStarSendov


open Set Topology
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendov

-- Three overlapping chart pieces; all cut avoidance is certified on the interval.
def sfun (t : ℝ) : ℂ :=
  if t ≤ 2 then rootR (dfun t) else if t ≤ 4 then rootI (dfun t) else -rootR (dfun t)

private theorem discriminant_at_two : dfun 2 = (3/25 : ℂ) + (4/25 : ℂ) * Complex.I := by
  apply Complex.ext <;> norm_num [dfun, cfun, cx, cy, ramp, pow_two, Complex.mul_re, Complex.mul_im]
private theorem discriminant_at_four : dfun 4 = (-1/20 : ℂ) - (9/50 : ℂ) * Complex.I := by
  apply Complex.ext <;> norm_num [dfun, cfun, cx, cy, ramp, pow_two, Complex.mul_re, Complex.mul_im]

private theorem continuous_sfun_interval : Continuous (fun t : Interval => sfun t) := by
  have hRleft : ContinuousOn (fun t : Interval => rootR (dfun t)) {t | (t:ℝ) ≤ 2} := by
    intro t ht
    exact ((continuousAt_rootR _ (rootU_pos _ (discriminant_chartR_left t ht))).comp (x := t)
      (continuous_dfun.comp continuous_subtype_val).continuousAt).continuousWithinAt
  have hImid : ContinuousOn (fun t : Interval => rootI (dfun t)) {t | 2 ≤ (t:ℝ) ∧ (t:ℝ) ≤ 4} := by
    intro t ht
    exact ((continuousAt_rootI _ (rootV_pos _ (discriminant_chartI_middle t ht.1 ht.2))).comp (x := t)
      (continuous_dfun.comp continuous_subtype_val).continuousAt).continuousWithinAt
  have hRright : ContinuousOn (fun t : Interval => -rootR (dfun t)) {t | 4 ≤ (t:ℝ)} := by
    intro t ht
    exact (((continuousAt_rootR _ (rootU_pos _ (discriminant_chartR_right t ht))).comp (x := t)
      (continuous_dfun.comp continuous_subtype_val).continuousAt).neg).continuousWithinAt
  have he2 : rootR (dfun 2) = rootI (dfun 2) := roots_agree_upper _ (by rw [discriminant_at_two]; norm_num)
  have he4 : rootI (dfun 4) = -rootR (dfun 4) := (roots_agree_lower _ (by rw [discriminant_at_four]; norm_num)).symm
  have hinner : ContinuousOn (fun t : Interval => if (t:ℝ) ≤ 4 then rootI (dfun t) else -rootR (dfun t))
      {t | 2 ≤ (t:ℝ)} := by
    apply ContinuousOn.if
    · intro t ht
      have hte : (t:ℝ) = 4 := frontier_le_subset_eq continuous_subtype_val continuous_const ht.2
      simpa only [hte] using he4
    · apply hImid.mono
      intro t ht
      refine ⟨ht.1, ?_⟩
      simpa only [(isClosed_le continuous_subtype_val continuous_const).closure_eq, Set.mem_setOf_eq] using ht.2
    · apply hRright.mono
      intro t ht
      have hs : {x : Interval | ¬ (x:ℝ) ≤ 4} = {x : Interval | 4 < (x:ℝ)} := by ext; simp
      rw [hs] at ht
      exact closure_lt_subset_le continuous_const continuous_subtype_val ht.2
  exact continuous_if_le continuous_subtype_val continuous_const hRleft hinner (by
    intro t ht
    simpa only [ht, if_pos (by norm_num : (2:ℝ) ≤ 4)] using he2)

def s : Alg := ⟨fun t => sfun t, continuous_sfun_interval⟩

private theorem square_root_squared (t : Interval) : (s t)^2 = (c t)^2 + 3/4 := by
  change (sfun t)^2 = dfun t
  unfold sfun
  split_ifs with h2 h4
  · exact rootR_sq _ (rootU_pos _ (discriminant_chartR_left t h2))
  · exact rootI_sq _ (rootV_pos _ (discriminant_chartI_middle t (by linarith) h4))
  · rw [neg_sq]
    exact rootR_sq _ (rootU_pos _ (discriminant_chartR_right t (by linarith)))

private theorem square_root_ne_zero (t : Interval) : s t ≠ 0 := by
  intro h
  have hh := square_root_squared t
  rw [h, zero_pow (by decide)] at hh
  exact discriminant_ne_zero t hh.symm

def t0 : Interval := ⟨0, by norm_num⟩
def t6 : Interval := ⟨6, by norm_num⟩

private theorem c_endpoints : c t0 = (-9/10 : ℂ) ∧ c t6 = (-9/10 : ℂ) := by
  constructor <;> apply Complex.ext <;> norm_num [c, t0, t6, cfun, cx, cy, ramp]

private theorem square_root_endpoints : s t0 = (Real.sqrt (39/25) : ℂ) ∧
    s t6 = -(Real.sqrt (39/25) : ℂ) := by
  constructor <;> apply Complex.ext <;>
    norm_num [s, sfun, t0, t6, rootR_re, rootR_im, rootU, dfun, cfun, cx, cy, ramp]

end D5.S3.Quantum.Algebra.CStarSendov


open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Algebra
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendov

def a : Fin 3 → Alg := ![(1/2 : ℂ) • (1:Alg), (-1/2 : ℂ) • (1:Alg), c]
def bplus : Alg := (1/3 : ℂ) • (c+s)
def bminus : Alg := (1/3 : ℂ) • (c-s)
def bs : Fin 2 → Alg := ![bplus,bminus]

 theorem ordered_deriv_apply (z : Alg) (t : Interval) :
    (CStarSchoenberg.orderedDeriv a z) t = 3 * (z t)^2 - 2 * c t * z t - 1/4 := by
  simpa [a, CStarSchoenberg.orderedDeriv, Fin.sum_univ_succ, List.ofFn_succ] using
    ordered_deriv_cubic (c t) (z t)

private theorem derivative_factorization (z : Alg) :
    CStarSchoenberg.orderedDeriv a z = (3:ℂ) • ((z-bplus)*(z-bminus)) := by
  ext t
  rw [ordered_deriv_apply]
  have hs := square_root_squared t
  change 3 * (z t)^2 - 2 * c t * z t - 1/4 =
    3 * ((z t - (1/3:ℂ)*(c t+s t))*(z t-(1/3:ℂ)*(c t-s t)))
  linear_combination (1/3:ℂ)*hs

theorem critical_both : CStarSchoenberg.orderedDeriv a bplus = 0 ∧
    CStarSchoenberg.orderedDeriv a bminus = 0 := by
  constructor <;> rw [derivative_factorization] <;> ext t <;>
    simp [ContinuousMap.smul_apply, smul_eq_mul]

private theorem every_critical_branch (z : Alg) (hz : CStarSchoenberg.orderedDeriv a z = 0) :
    z = bplus ∨ z = bminus := by
  letI : PreconnectedSpace Interval := Subtype.preconnectedSpace isPreconnected_Icc
  letI : Nonempty Interval := ⟨t0⟩
  apply two_branch_exhaustion c s z square_root_ne_zero square_root_squared
  intro t
  have h := congrArg (fun f : Alg => f t) hz
  simpa only [ordered_deriv_apply, ContinuousMap.zero_apply] using h

private theorem disc_iff_norm {f g : Alg} : f ∈ cstarDisc g 1 ↔ ∀ t, ‖f t - g t‖ ≤ 1 := by
  simp only [cstarDisc, Set.mem_setOf_eq, Real.sqrt_one, Complex.ofReal_one,
    one_smul, ContinuousMap.le_def, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    ContinuousMap.sub_apply, ContinuousMap.one_apply]
  apply forall_congr'
  intro t
  change (f t - g t) * (starRingEnd ℂ) (f t - g t) ≤ 1 ↔ _
  rw [Complex.mul_conj, ← Complex.ofReal_one, Complex.real_le_real, Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (f t - g t)]
  · intro h
    nlinarith [norm_nonneg (f t - g t)]

private theorem c_norm_le (t : Interval) : ‖c t‖ ≤ 1 := by
  have h := polygon_normSq_le t
  rw [Complex.normSq_eq_norm_sq] at h
  change ‖c t‖^2 ≤ 82/100 at h
  nlinarith [norm_nonneg (c t)]

private theorem s_norm_le (t : Interval) : ‖s t‖ ≤ 2 := by
  have h := congrArg norm (square_root_squared t)
  rw [norm_pow] at h
  have hu := norm_add_le ((c t)^2) (3/4:ℂ)
  rw [norm_pow] at hu
  norm_num [norm_div] at hu
  have hc := c_norm_le t
  nlinarith [norm_nonneg (c t), norm_nonneg (s t)]

theorem roots_in_disc : ∀ j, a j ∈ cstarDisc 0 1 := by
  intro j
  apply disc_iff_norm.mpr
  intro t
  fin_cases j
  · norm_num [a, norm_div]
  · norm_num [a, norm_div]
  · simpa [a] using c_norm_le t

theorem critical_in_disc : bplus ∈ cstarDisc 0 1 ∧ bminus ∈ cstarDisc 0 1 := by
  constructor <;> apply disc_iff_norm.mpr <;> intro t
  · change ‖(1/3:ℂ)*(c t+s t) - 0‖ ≤ 1
    rw [sub_zero, norm_mul]
    norm_num [norm_div]
    nlinarith [norm_add_le (c t) (s t), c_norm_le t, s_norm_le t]
  · change ‖(1/3:ℂ)*(c t-s t) - 0‖ ≤ 1
    rw [sub_zero, norm_mul]
    norm_num [norm_div]
    nlinarith [norm_sub_le (c t) (s t), c_norm_le t, s_norm_le t]

 private theorem bad_endpoints : 1 < ‖bminus t0 - (1/2:ℂ)‖ ∧ 1 < ‖bplus t6 - (1/2:ℂ)‖ := by
  have hs : 3/5 < Real.sqrt (39/25) := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 39/25)
    have h0 := Real.sqrt_nonneg (39/25)
    nlinarith
  constructor
  · have hl := (abs_le.mp (Complex.abs_re_le_norm (bminus t0-(1/2:ℂ)))).1
    have he : (bminus t0 - (1/2:ℂ)).re = (-9/10 - Real.sqrt (39/25))/3 - 1/2 := by
      simp [bminus, c_endpoints.1, square_root_endpoints.1, Complex.mul_re]
      ring
    rw [he] at hl
    linarith
  · have hl := (abs_le.mp (Complex.abs_re_le_norm (bplus t6-(1/2:ℂ)))).1
    have he : (bplus t6 - (1/2:ℂ)).re = (-9/10 - Real.sqrt (39/25))/3 - 1/2 := by
      simp [bplus, c_endpoints.2, square_root_endpoints.2, Complex.mul_re]
      ring
    rw [he] at hl
    linarith

theorem no_critical_in_half_disc (z : Alg) (hz : CStarSchoenberg.orderedDeriv a z = 0) :
    z ∉ cstarDisc ((1/2:ℂ) • (1:Alg)) 1 := by
  intro hd
  have h := disc_iff_norm.mp hd
  rcases every_critical_branch z hz with rfl | rfl
  · exact (not_le_of_gt bad_endpoints.2) (by simpa using h t6)
  · exact (not_le_of_gt bad_endpoints.1) (by simpa using h t0)

end D5.S3.Quantum.Algebra.CStarSendov


open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Algebra
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendov

 private theorem scalar_root_ne_roots (c z : ℂ) (hc : c ≠ (1/2:ℂ) ∧ c ≠ (-1/2:ℂ))
    (hz : 3*z^2 - 2*c*z - 1/4 = 0) :
    z - 1/2 ≠ 0 ∧ z + 1/2 ≠ 0 ∧ z - c ≠ 0 := by
  constructor
  · intro h
    have he : z = 1/2 := sub_eq_zero.mp h
    rw [he] at hz
    apply hc.1
    linear_combination -hz
  · constructor
    · intro h
      have he : z = -1/2 := by linear_combination h
      rw [he] at hz
      apply hc.2
      linear_combination hz
    · intro h
      have he : z = c := sub_eq_zero.mp h
      rw [he] at hz
      have hp : (c - (1/2:ℂ)) * (c + 1/2) = 0 := by linear_combination hz
      rcases mul_eq_zero.mp hp with h | h
      · exact hc.1 (sub_eq_zero.mp h)
      · apply hc.2
        linear_combination h

private theorem inverse_sum_of_products (x y w : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (he : x*y + x*w + y*w = 0) : x⁻¹ + y⁻¹ + w⁻¹ = 0 := by
  have hm : (x⁻¹+y⁻¹+w⁻¹)*(x*y*w) = 0 := by
    linear_combination (y*w)*(inv_mul_cancel₀ hx) + (x*w)*(inv_mul_cancel₀ hy) +
      (x*y)*(inv_mul_cancel₀ hw) + he
  exact (mul_eq_zero.mp hm).resolve_right (mul_ne_zero (mul_ne_zero hx hy) hw)

private theorem scalar_inverse_sum (c z : ℂ) (h0 : z-1/2 ≠ 0) (h1 : z+1/2 ≠ 0)
    (h2 : z-c ≠ 0) (hz : 3*z^2 - 2*c*z - 1/4 = 0) :
    (z-1/2)⁻¹ + (z+1/2)⁻¹ + (z-c)⁻¹ = 0 := by
  apply inverse_sum_of_products _ _ _ h0 h1 h2
  linear_combination hz

def qscalar (z r : ℂ) : ℝ := (Complex.normSq (z-r))⁻¹

private theorem scalar_weighted_residual (c z : ℂ) (h0 : z-1/2 ≠ 0) (h1 : z+1/2 ≠ 0)
    (h2 : z-c ≠ 0) (hz : 3*z^2 - 2*c*z - 1/4 = 0) :
    (qscalar z (1/2) : ℂ)*(z-1/2) + (qscalar z (-1/2) : ℂ)*(z+1/2) +
      (qscalar z c : ℂ)*(z-c) = 0 := by
  have hi := scalar_inverse_sum c z h0 h1 h2 hz
  simp only [qscalar, neg_div, sub_neg_eq_add]
  apply Complex.ext
  · have hr := congrArg Complex.re hi
    simp only [Complex.add_re, Complex.inv_re, Complex.zero_re] at hr
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, zero_mul, sub_zero, qscalar, sub_neg_eq_add]
    simpa only [div_eq_mul_inv, mul_comm] using hr
  · have hr := congrArg Complex.im hi
    simp only [Complex.add_im, Complex.inv_im, Complex.zero_im] at hr
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, zero_mul, add_zero, qscalar, sub_neg_eq_add]
    simp only [div_eq_mul_inv, neg_mul] at hr
    simp only [div_eq_mul_inv] at *
    linear_combination -hr

end D5.S3.Quantum.Algebra.CStarSendov


open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Algebra
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendov

 private theorem critical_gap (z : Alg) (hz : CStarSchoenberg.orderedDeriv a z = 0)
    (t : Interval) (j : Fin 3) : z t - a j t ≠ 0 := by
  have h := congrArg (fun f : Alg => f t) hz
  rw [ordered_deriv_apply] at h
  have hg := scalar_root_ne_roots (c t) (z t) (cfun_ne_half t) h
  fin_cases j
  · simpa [a] using hg.1
  · simpa [a, neg_div] using hg.2.1
  · simpa [a] using hg.2.2

 private theorem critical_unit_convex_form (z : Alg) (hz : CStarSchoenberg.orderedDeriv a z = 0) :
    ∃ u : Fin 3 → Algˣ, (∀ j, 0 ≤ (u j : Alg)) ∧
      ∑ j, (u j : Alg) = 1 ∧ z = ∑ j, (u j : Alg) * a j := by
  let q : Fin 3 → Interval → ℝ := fun j t => qscalar (z t) (a j t)
  let Q : Interval → ℝ := fun t => ∑ j, q j t
  have hqpos (j : Fin 3) (t : Interval) : 0 < q j t :=
    inv_pos.mpr (Complex.normSq_pos.mpr (critical_gap z hz t j))
  have hQpos (t : Interval) : 0 < Q t :=
    Finset.sum_pos (by intro j hj; exact hqpos j t) Finset.univ_nonempty
  have hqc (j : Fin 3) : Continuous (q j) := by
    apply Continuous.inv₀
    · exact Complex.continuous_normSq.comp (z.continuous.sub (a j).continuous)
    · intro t
      exact (Complex.normSq_pos.mpr (critical_gap z hz t j)).ne'
  have hQc : Continuous Q := continuous_finsetSum _ (fun j hj => hqc j)
  let w : Fin 3 → Alg := fun j => ⟨fun t => ((q j t / Q t : ℝ) : ℂ),
    Complex.continuous_ofReal.comp ((hqc j).div hQc (fun t => (hQpos t).ne'))⟩
  have hwunit (j : Fin 3) : IsUnit (w j) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero (w j)).mpr
    intro t
    exact Complex.ofReal_ne_zero.mpr (div_pos (hqpos j t) (hQpos t)).ne'
  let u : Fin 3 → Algˣ := fun j => (hwunit j).unit
  have huw (j : Fin 3) : (u j : Alg) = w j := (hwunit j).unit_spec
  refine ⟨u, ?_, ?_, ?_⟩
  · intro j
    rw [huw]
    apply ContinuousMap.le_def.mpr
    intro t
    change (0:ℂ) ≤ ((q j t / Q t : ℝ) : ℂ)
    simpa only [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im, and_true] using
      (le_of_lt (div_pos (hqpos j t) (hQpos t)))
  · simp only [huw]
    ext t
    change (∑ j, ((q j t / Q t : ℝ) : ℂ)) = 1
    rw [← Complex.ofReal_sum]
    rw [← Finset.sum_div]
    change ((Q t / Q t : ℝ) : ℂ) = 1
    rw [div_self (hQpos t).ne', Complex.ofReal_one]
  · simp only [huw]
    ext t
    change z t = ∑ j, ((q j t / Q t : ℝ) : ℂ) * a j t
    have hd := congrArg (fun f : Alg => f t) hz
    rw [ordered_deriv_apply] at hd
    have hg := scalar_root_ne_roots (c t) (z t) (cfun_ne_half t) hd
    have hr := scalar_weighted_residual (c t) (z t) hg.1 hg.2.1 hg.2.2 hd
    have hq : ((Q t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hQpos t).ne'
    have hr' : (Q t : ℂ) * z t = ∑ j, (q j t : ℂ) * a j t := by
      dsimp [Q, q]
      simp [Fin.sum_univ_succ, a]
      simp only [one_div, neg_div] at hr ⊢
      linear_combination hr
    simp only [Complex.ofReal_div, div_mul_eq_mul_div, ← Finset.sum_div]
    apply (eq_div_iff hq).mpr
    simpa only [mul_comm] using hr'

theorem critical_convex_form (z : Alg) (hz : CStarSchoenberg.orderedDeriv a z = 0) :
    IsConvexForm a z := by
  obtain ⟨u, hu, hs, hz'⟩ := critical_unit_convex_form z hz
  exact ⟨fun j => (u j : Alg), hu, hs, hz'⟩

end D5.S3.Quantum.Algebra.CStarSendov

namespace D5.S3.Quantum.Algebra.CStarSendov
noncomputable section
open D5.S3.Quantum.Algebra

theorem result : ¬ claimSendov := by
  intro h
  have hc : ∀ k, CStarSchoenberg.orderedDeriv a (bs k) = 0 := by
    intro k
    fin_cases k <;> simp only [bs, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact critical_both.1
    · exact critical_both.2
  have hd : ∀ k, bs k ∈ cstarDisc 0 1 := by
    intro k
    fin_cases k <;> simp only [bs, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact critical_in_disc.1
    · exact critical_in_disc.2
  have hf : ∀ k, IsConvexForm a (bs k) := fun k => critical_convex_form (bs k) (hc k)
  obtain ⟨z, hz, hdisc⟩ := h Alg 3 (by norm_num) a roots_in_disc bs hc hd hf 0
  exact no_critical_in_half_disc z hz (by simpa [a] using hdisc)

#print axioms result
#check result
end
end D5.S3.Quantum.Algebra.CStarSendov
