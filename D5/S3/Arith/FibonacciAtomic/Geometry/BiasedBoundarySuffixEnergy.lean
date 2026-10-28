/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Lp.lpSpace]
   utility: none
   digest: Prefix-free strict suffixes have disjoint original edge energy. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering
import D5.S0.Computability.Coding.BiasedMassFrontier

/-! Disjoint strict-descendant energy in the original increment Hilbert space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (Edge H)
open BiasedBoundaryPathSplit (S descendant boundary_path_split)
open BiasedBoundaryCentering (C Pi centered_suffix_residual)
open BiasedBoundaryConditionalLaw (pullback)
open D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open scoped BigOperators ENNReal

private theorem joint_descendant_injective (A : Finset Address)
    (hA : IsPrefixFree (A : Set Address)) :
    Function.Injective (fun x : A × Edge => descendant x.1.val x.2) := by
  intro x y hxy
  have he : x.1.val ++ x.2.val = y.1.val ++ y.2.val := congrArg Subtype.val hxy
  have hx : x.1.val <+: y.1.val ++ y.2.val := by
    rw [← he]
    exact List.prefix_append _ _
  have hy : y.1.val <+: y.1.val ++ y.2.val := List.prefix_append _ _
  have hp : x.1.val = y.1.val := by
    rcases List.prefix_or_prefix_of_prefix hx hy with hp | hp
    · exact hA x.1.property y.1.property hp
    · exact (hA y.1.property x.1.property hp).symm
  apply Prod.ext
  · exact Subtype.ext hp
  · apply Subtype.ext
    rw [hp] at he
    exact List.append_cancel_left he

private theorem norm_sq_tsum (z : H) : ‖z‖ ^ 2 = ∑' u : Edge, ‖z u‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) z

/-- Strict descendants of distinct prefix-free addresses use disjoint original
edge coordinates, for every original square-summable increment vector. -/
theorem prefix_free_suffix_energy (A : Finset Address)
    (hA : IsPrefixFree (A : Set Address)) (z : H) :
    ∑ p ∈ A, ‖S p z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  classical
  let f : Edge → ℝ := fun u => ‖z u‖ ^ 2
  let j : A × Edge → Edge := fun x => descendant x.1.val x.2
  have hj : Function.Injective j := joint_descendant_injective A hA
  have hf : Summable f := by
    simpa [f] using (lp.memℓp z).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have hfj : Summable (f ∘ j) := hf.comp_injective hj
  calc
    ∑ p ∈ A, ‖S p z‖ ^ 2 = ∑ p : A, ∑' u : Edge, f (j (p, u)) := by
      rw [← Finset.sum_coe_sort A (fun p => ‖S p z‖ ^ 2)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_sq_tsum]
      apply tsum_congr
      intro u
      rw [boundary_path_split.1]
    _ = ∑' x : A × Edge, f (j x) := by
      simpa only [tsum_fintype, Function.comp_apply] using hfj.tsum_prod.symm
    _ ≤ ∑' u : Edge, f u :=
      tsum_comp_le_tsum_of_inj hf (fun u => sq_nonneg ‖z u‖) hj
    _ = ‖z‖ ^ 2 := (norm_sq_tsum z).symm

/-- Nonnegative weights at most t give the source's golden-ratio bound on the
sum of the actual centered strict-suffix norms. -/
theorem weighted_centered_suffix_energy (A : Finset Address)
    (hA : IsPrefixFree (A : Set Address)) (w : Address → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hw : ∀ p ∈ A, 0 ≤ w p ∧ w p ≤ t) (z : H) :
    ∑ p ∈ A, w p * ‖C (S p z)‖ ^ 2 ≤ Real.goldenRatio * t * ‖z‖ ^ 2 := by
  calc
    ∑ p ∈ A, w p * ‖C (S p z)‖ ^ 2
        ≤ ∑ p ∈ A, Real.goldenRatio * t * ‖S p z‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hc : ‖C (S p z)‖ ^ 2 ≤ Real.goldenRatio * ‖S p z‖ ^ 2 := by
        rw [← centered_suffix_residual.2.2.2.2.1 p z]
        exact centered_suffix_residual.2.2.2.2.2 p z
      calc
        w p * ‖C (S p z)‖ ^ 2 ≤ w p * (Real.goldenRatio * ‖S p z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hc (hw p hp).1
        _ ≤ t * (Real.goldenRatio * ‖S p z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hw p hp).2
            (mul_nonneg Real.goldenRatio_pos.le (sq_nonneg _))
        _ = Real.goldenRatio * t * ‖S p z‖ ^ 2 := by ring
    _ = Real.goldenRatio * t * (∑ p ∈ A, ‖S p z‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ Real.goldenRatio * t * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (prefix_free_suffix_energy A hA z)
        (mul_nonneg Real.goldenRatio_pos.le ht)

#print axioms prefix_free_suffix_energy
#print axioms weighted_centered_suffix_energy

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy
