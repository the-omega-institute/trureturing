/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Constant-trace variational minimization on the original biased binary boundary. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H Edge)
open BiasedBoundaryTrace (G J M Omega cylinder indicator J_single)
open BiasedBoundaryPathSplit (S descendant constG prefixSum prefixes boundary_path_split)
open BiasedBoundaryConditionalLaw (pullback)
open BiasedBoundaryCentering (mean Pi C centered_suffix_residual pullback_const)
open BiasedBoundaryFreeRootForm (D K Sigma lift form energy free_root_least_energy)
open MeasureTheory InnerProductSpace
open scoped BigOperators

private def edge (c : Bool) : Edge := ⟨[c], by simp⟩
private def E (c : Bool) : H →L[ℝ] H := (S [c]).adjoint

private theorem suffix_root (c d : Bool) (a : ℝ) :
    S [c] (lp.single 2 (edge d) a) = 0 := by
  by_cases h : c = d
  · subst d
    exact BiasedBoundaryPathSplit.suffix_single_prefix [c] (edge c) a (by rfl)
  · exact BiasedBoundaryPathSplit.suffix_single_of_not_prefix [c] (edge d) a (by
      simpa [edge] using h)

private theorem suffix_branch (c d : Bool) (u : Edge) (a : ℝ) :
    S [c] (lp.single 2 (descendant [d] u) a) =
      if c = d then lp.single 2 u a else 0 := by
  by_cases h : c = d
  · subst d
    simpa using BiasedBoundaryPathSplit.suffix_single_descendant [c] u a
  · rw [if_neg h]
    exact BiasedBoundaryPathSplit.suffix_single_of_not_prefix [c] (descendant [d] u) a
      (by simpa [descendant] using h)

private theorem E_root (c d : Bool) (z : H) : E c z (edge d) = 0 := by
  classical
  have h := (S [c]).adjoint_inner_right (lp.single 2 (edge d) (1 : ℝ)) z
  rw [suffix_root, inner_zero_left, lp.inner_single_left] at h
  simpa [E, Real.inner_apply] using h

private theorem E_branch (c d : Bool) (z : H) (u : Edge) :
    E c z (descendant [d] u) = if c = d then z u else 0 := by
  classical
  have h := (S [c]).adjoint_inner_right
    (lp.single 2 (descendant [d] u) (1 : ℝ)) z
  rw [suffix_branch, lp.inner_single_left] at h
  by_cases he : c = d
  · simpa [E, he, lp.inner_single_left, Real.inner_apply] using h
  · simpa [E, he, Real.inner_apply] using h

private def graft (x y : ℝ) (z w : H) : H :=
  lp.single 2 (edge false) x + lp.single 2 (edge true) y + E false z + E true w

private theorem graft_root (x y : ℝ) (z w : H) (c : Bool) :
    graft x y z w (edge c) = if c then y else x := by
  classical
  simp only [graft, lp.coeFn_add, Pi.add_apply, E_root, add_zero]
  cases c <;> simp [edge, Pi.single_apply]

private theorem suffix_graft (x y : ℝ) (z w : H) (c : Bool) :
    S [c] (graft x y z w) = if c then w else z := by
  classical
  ext u
  rw [boundary_path_split.1]
  change (lp.single 2 (edge false) x : H) (descendant [c] u) +
    (lp.single 2 (edge true) y : H) (descendant [c] u) +
    E false z (descendant [c] u) + E true w (descendant [c] u) = _
  have hn (d : Bool) : descendant [c] u ≠ edge d := by
    intro h
    have he := congrArg (fun p : Edge => p.val.length) h
    have hu := List.length_pos_of_ne_nil u.property
    simp [descendant, edge] at he
    omega
  rw [lp.single_apply_ne (hn false), lp.single_apply_ne (hn true), E_branch, E_branch]
  cases c <;> simp

private theorem graft_pair (x y : ℝ) (z w v : H) :
    inner ℝ (graft x y z w) v = x * v (edge false) + y * v (edge true) +
      inner ℝ z (S [false] v) + inner ℝ w (S [true] v) := by
  classical
  simp only [graft, inner_add_left, lp.inner_single_left, Real.inner_apply]
  rw [show inner ℝ (E false z) v = inner ℝ z (S [false] v) from
      (S [false]).adjoint_inner_left z v,
    show inner ℝ (E true w) v = inner ℝ w (S [true] v) from
      (S [true]).adjoint_inner_left w v]
  ring

private theorem graft_norm (x y : ℝ) (z w : H) :
    ‖graft x y z w‖^2 = x^2 + y^2 + ‖z‖^2 + ‖w‖^2 := by
  rw [← real_inner_self_eq_norm_sq, graft_pair, graft_root, graft_root,
    suffix_graft, suffix_graft]
  simp only [Bool.false_eq_true, if_false, if_true, real_inner_self_eq_norm_sq]
  ring

private theorem graft_split (z : H) :
    graft (z (edge false)) (z (edge true)) (S [false] z) (S [true] z) = z := by
  classical
  ext p
  obtain ⟨p,hp⟩ := p
  cases p with
  | nil => exact (hp rfl).elim
  | cons c u =>
    cases u with
    | nil => exact graft_root _ _ _ _ c |>.trans (by cases c <;> rfl)
    | cons d v =>
      let q : Edge := ⟨d::v, by simp⟩
      change (lp.single 2 (edge false) (z (edge false)) : H) (descendant [c] q) +
        (lp.single 2 (edge true) (z (edge true)) : H) (descendant [c] q) +
        E false (S [false] z) (descendant [c] q) +
        E true (S [true] z) (descendant [c] q) = _
      simp only [lp.coeFn_single, Pi.single_apply, E_branch]
      have hn (b : Bool) : descendant [c] q ≠ edge b := by
        intro he
        have hh := congrArg (fun p : Edge => p.val.length) he
        simp [descendant, edge, q] at hh
      simp only [hn, if_false, zero_add]
      cases c <;> simp [boundary_path_split.1, descendant, q]

private theorem norm_split (z : H) :
    ‖z‖^2 = (z (edge false))^2 + (z (edge true))^2 +
      ‖S [false] z‖^2 + ‖S [true] z‖^2 := by
  rw [← graft_split z] at ⊢
  rw [graft_norm, graft_root, graft_root, suffix_graft, suffix_graft]
  rfl

private theorem prefix_one (c : Bool) (z : H) : prefixSum [c] z = z (edge c) := by
  classical
  simp [prefixSum, prefixes, List.inits, edge]

private theorem pullback_graft (x y : ℝ) (z w : H) (c : Bool) :
    pullback [c] (J (graft x y z w)) =
      constG (if c then y else x) + J (if c then w else z) := by
  rw [boundary_path_split.2.2.2.2, prefix_one, graft_root, suffix_graft]

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy
