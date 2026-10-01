/- GID: D5/S3/Observer/Linear/DerivativeLayerGramianPositivity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic]
   utility: none
   digest: The actual derivative layers have a jointly injective polynomial observation and a positive Gramian on the finite observable complement. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
The kernel filtration of the iterated readouts gives orthogonal layers without
discarding zero layers. A layer vector killed by its own readout lies in both
the next kernel and its orthogonal complement. Resolving the filtration from
the final kernel to the whole state space then makes the polynomial observation
injective on the final kernel's orthogonal complement.
Utility classification is none: the proof uses the symbolic kernel filtration
and orthogonal decomposition, not bounded enumeration, a checker, a numeric
reduction, or a certified finite instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.DerivativeLayerGramianPositivity

open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace InnerProduct

/-- The actual finite derivative filtration gives a strictly positive
factorially weighted polynomial Gramian on its observable complement. -/
theorem derivative_layer_gramian_pos
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) :
    let n := Module.finrank ℝ V
    let N : ℕ → Submodule ℝ V := fun j =>
      ⨅ k : Fin j, LinearMap.ker (C.comp (B ^ (k : ℕ)))
    let U : Submodule ℝ V := (N n)ᗮ
    let E : Fin n → Submodule ℝ V := fun j => N j ⊓ (N (j + 1))ᗮ
    let A : Fin n → U →L[ℝ] W := fun j =>
      ((C.comp (B ^ (j : ℕ))).comp
        ((E j).starProjection.toLinearMap.comp U.subtype)).toContinuousLinearMap
    let F : ℝ → U →L[ℝ] W := fun s =>
      ∑ j : Fin n, (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • A j
    let G : U →L[ℝ] U := ∫ s in (0 : ℝ)..1, (F s).adjoint.comp (F s)
    ∀ x : U, x ≠ 0 → 0 < ⟪x, G x⟫_ℝ := by
  classical
  intro n N U E A F G x hx
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hG : Continuous (fun s : ℝ => (F s).adjoint.comp (F s)) :=
    (ContinuousLinearMap.adjoint.continuous.comp hF).clm_comp hF
  have hGint : IntervalIntegrable
      (fun s : ℝ => (F s).adjoint.comp (F s)) volume 0 1 :=
    hG.intervalIntegrable _ _
  have henergy : ⟪x, G x⟫_ℝ =
      ∫ s in (0 : ℝ)..1, ‖F s x‖ ^ 2 := by
    have happly : G x =
        ∫ s in (0 : ℝ)..1, ((F s).adjoint.comp (F s)) x :=
      ContinuousLinearMap.intervalIntegral_apply hGint x
    have happlyInt : IntervalIntegrable
        (fun s : ℝ => ((F s).adjoint.comp (F s)) x) volume 0 1 :=
      ((ContinuousLinearMap.apply ℝ U x).continuous.comp hG).intervalIntegrable _ _
    rw [happly]
    change (innerSL ℝ x)
      (∫ s in (0 : ℝ)..1, ((F s).adjoint.comp (F s)) x) =
        ∫ s in (0 : ℝ)..1, ‖F s x‖ ^ 2
    rw [← (innerSL ℝ x).intervalIntegral_comp_comm happlyInt]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [ContinuousLinearMap.comp_apply]
    change ⟪x, (F s).adjoint (F s x)⟫_ℝ = ‖F s x‖ ^ 2
    exact ((F s).apply_norm_sq_eq_inner_adjoint_right x).symm
  have hnonneg : 0 ≤ ⟪x, G x⟫_ℝ := by
    rw [henergy]
    exact intervalIntegral.integral_nonneg_of_forall
      (by norm_num : (0 : ℝ) ≤ 1) (fun s => sq_nonneg ‖F s x‖)
  by_contra hpos
  have hz : ⟪x, G x⟫_ℝ = 0 :=
    le_antisymm (le_of_not_gt hpos) hnonneg
  have hcoeff : ∀ j : Fin n, A j x = 0 := by
    have hFx : Continuous (fun s : ℝ => F s x) :=
      (ContinuousLinearMap.apply ℝ W x).continuous.comp hF
    intro j
    have hnormint : IntervalIntegrable (fun s : ℝ => ‖F s x‖ ^ 2) volume 0 1 :=
      (hFx.norm.pow 2).intervalIntegrable _ _
    have hae : (fun s : ℝ => ‖F s x‖ ^ 2) =ᵐ[volume.restrict (Set.Ioc 0 1)] 0 :=
      (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
        (by norm_num : (0 : ℝ) ≤ 1)
        (Filter.Eventually.of_forall (fun s => sq_nonneg ‖F s x‖))
        hnormint).mp (henergy ▸ hz)
    have hzero_on : Set.EqOn (fun s : ℝ => ‖F s x‖ ^ 2) 0
        (Set.Ioc 0 1) :=
      MeasureTheory.Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae
        (hFx.norm.pow 2).continuousOn continuous_zero.continuousOn
    have hFzero : ∀ s ∈ Set.Ioc (0 : ℝ) 1, F s x = 0 := by
      intro s hs
      have hs0 := hzero_on hs
      have hn : ‖F s x‖ = 0 := by
        simpa only [Pi.zero_apply] using (sq_eq_zero_iff.mp hs0)
      exact norm_eq_zero.mp hn
    let q : Polynomial ℝ := ∑ i : Fin n,
      Polynomial.monomial (i : ℕ)
        (⟪A j x, A i x⟫_ℝ / (Nat.factorial (i : ℕ) : ℝ))
    have hqeval (s : ℝ) : q.eval s = ⟪A j x, F s x⟫_ℝ := by
      simp only [q, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
        F, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        inner_sum, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hq : q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.Ioc_infinite (by norm_num : (0 : ℝ) < 1)).mono
      intro s hs
      change q.eval s = 0
      rw [hqeval s, hFzero s hs]
      simp
    have hc := congrArg (fun p : Polynomial ℝ => p.coeff (j : ℕ)) hq
    have hj : (⟪A j x, A j x⟫_ℝ /
        (Nat.factorial (j : ℕ) : ℝ)) = 0 := by
      simpa only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
        Fin.val_eq_val, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Polynomial.coeff_zero] using hc
    have hself : ⟪A j x, A j x⟫_ℝ = 0 :=
      (div_eq_zero_iff).mp hj |>.resolve_right (by exact_mod_cast Nat.factorial_ne_zero (j : ℕ))
    rw [real_inner_self_eq_norm_sq] at hself
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hself)
  have hN (j : ℕ) (z : V) :
      z ∈ N j ↔ ∀ k : ℕ, k < j → C ((B ^ k) z) = 0 := by
    constructor
    · intro hz k hk
      have hzk := ((Submodule.mem_iInf _).mp hz) (⟨k, hk⟩ : Fin j)
      simpa only [N, LinearMap.mem_ker, LinearMap.comp_apply] using hzk
    · intro hz
      apply (Submodule.mem_iInf _).mpr
      intro k
      exact LinearMap.mem_ker.mpr (hz k k.isLt)
  have hNmono (j : ℕ) : N (j + 1) ≤ N j := by
    intro z hz
    exact (hN j z).2 (fun k hk => (hN (j + 1) z).1 hz k (by omega))
  have hNzero : N 0 = ⊤ := by
    apply top_unique
    intro z _
    exact (hN 0 z).2 (fun k hk => by omega)
  have hproj (j : Fin n) : (E j).starProjection (x : V) = 0 := by
    let y : V := (E j).starProjection (x : V)
    have hy : y ∈ E j := (E j).starProjection_apply_mem (x : V)
    have hyNext : y ∈ N ((j : ℕ) + 1) := by
      apply (hN ((j : ℕ) + 1) y).2
      intro k hk
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
      · exact (hN (j : ℕ) y).1 hy.1 k hlt
      · subst k
        have hAj := hcoeff j
        change C ((B ^ (j : ℕ)) y) = 0 at hAj
        exact hAj
    have hyOrth : y ∈ (N ((j : ℕ) + 1))ᗮ := hy.2
    have hself := (Submodule.mem_orthogonal (N ((j : ℕ) + 1)) y).mp hyOrth y hyNext
    rw [real_inner_self_eq_norm_sq] at hself
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hself)
  have hreverse : ∀ i : ℕ, i ≤ n → (x : V) ∈ (N (n - i))ᗮ := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa only [Nat.sub_zero, U] using x.property
    | succ i ih =>
        intro hi
        have hin : i ≤ n := by omega
        have hlt : n - (i + 1) < n := by omega
        let j : Fin n := ⟨n - (i + 1), hlt⟩
        have hnext : n - i = (j : ℕ) + 1 := by dsimp [j]; omega
        rw [show n - (i + 1) = (j : ℕ) by rfl]
        apply (Submodule.mem_orthogonal (N j) (x : V)).2
        intro z hz
        let p : V := (N ((j : ℕ) + 1)).starProjection z
        have hpNext : p ∈ N ((j : ℕ) + 1) :=
          (N ((j : ℕ) + 1)).starProjection_apply_mem z
        have hp : p ∈ N j := hNmono (j : ℕ) hpNext
        have hr : z - p ∈ E j := by
          constructor
          · exact (N j).sub_mem hz hp
          · exact Submodule.sub_starProjection_mem_orthogonal z
        have hxNext : (x : V) ∈ (N ((j : ℕ) + 1))ᗮ := by
          simpa only [hnext] using ih hin
        have hxLayer : (x : V) ∈ (E j)ᗮ :=
          (Submodule.starProjection_apply_eq_zero_iff (E j)).mp (hproj j)
        have hpZero := (Submodule.mem_orthogonal (N ((j : ℕ) + 1)) (x : V)).mp
          hxNext p hpNext
        have hrZero := (Submodule.mem_orthogonal (E j) (x : V)).mp
          hxLayer (z - p) hr
        calc
          ⟪z, (x : V)⟫_ℝ = ⟪p + (z - p), (x : V)⟫_ℝ := by congr 1; abel
          _ = 0 := by rw [inner_add_left, hpZero, hrZero, zero_add]
  have hxZero : x = 0 := by
    have hwhole : (x : V) ∈ (⊤ : Submodule ℝ V)ᗮ := by
      simpa only [Nat.sub_self, hNzero] using hreverse n le_rfl
    have hself := (Submodule.mem_orthogonal (⊤ : Submodule ℝ V) (x : V)).mp
      hwhole (x : V) (by trivial)
    have hnorm : ‖(x : V)‖ ^ 2 = 0 := by
      simpa only [real_inner_self_eq_norm_sq] using hself
    exact Subtype.ext (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  exact (hx hxZero).elim


end D5.S3.Observer.Linear.DerivativeLayerGramianPositivity
