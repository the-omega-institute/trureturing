/- GID: D5/S3/Geometry/ODE/UniformLocalGlobalPasting
   generality: G
   mirror-B: D5/B/S3/Geometry/ODE/UniformLocalGlobalPasting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.LocallyFinite]
   utility: none
   digest: Uniform two-sided local solution times give one solution on all real time. -/

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.LocallyFinite
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter
open scoped Topology

namespace D5.S3.Geometry.ODE.UniformLocalGlobalPasting

/-- Uniform two-sided local solution witnesses can be extended compatibly to one
solution on all real time, without continuity or uniqueness of the field. -/
theorem exists_global_solution_of_uniform_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) {T : ℝ} (hT : 0 < T)
    (hlocal : ∀ x : E, ∃ C : ℝ → E, C 0 = x ∧
      ∀ s ∈ Ioo (-T) T, HasDerivAt C (f (C s)) s)
    (x0 : E) :
    ∃ γ : ℝ → E, γ 0 = x0 ∧ ∀ t : ℝ, HasDerivAt γ (f (γ t)) t := by
  classical
  choose C hC0 hCd using hlocal
  let τ : ℝ := T / 2
  have hτ : 0 < τ := half_pos hT
  have hTτ : T = 2 * τ := by dsimp [τ]; ring
  let extend (q : ℝ) (g : ℝ → E) : ℝ → E := fun t =>
    if t < -q then C (g (-q)) (t + q)
    else if q < t then C (g q) (t - q)
    else g t
  have hextend (q : ℝ) (hq : 0 < q) (g : ℝ → E)
      (hg : ∀ t ∈ Ioo (-q - τ) (q + τ), HasDerivAt g (f (g t)) t) :
      ∀ t ∈ Ioo (-q - T) (q + T),
        HasDerivAt (extend q g) (f (extend q g t)) t := by
    have hL (t : ℝ) (ht : t + q ∈ Ioo (-T) T) :
        HasDerivAt (fun s => C (g (-q)) (s + q))
          (f (C (g (-q)) (t + q))) t :=
      (hCd (g (-q)) (t + q) ht).comp_add_const t q
    have hR (t : ℝ) (ht : t - q ∈ Ioo (-T) T) :
        HasDerivAt (fun s => C (g q) (s - q))
          (f (C (g q) (t - q))) t :=
      (hCd (g q) (t - q) ht).comp_sub_const t q
    have hneg : extend q g (-q) = g (-q) := by
      dsimp [extend]
      rw [if_neg (lt_irrefl _), if_neg (by linarith)]
    have hpos : extend q g q = g q := by
      dsimp [extend]
      rw [if_neg (by linarith), if_neg (lt_irrefl _)]
    intro t ht
    rcases lt_trichotomy t (-q) with hlt | heq | hgt
    · have hnear : extend q g =ᶠ[𝓝 t] (fun s => C (g (-q)) (s + q)) := by
        filter_upwards [Iio_mem_nhds hlt] with s hs
        exact if_pos hs
      rw [hnear.eq_of_nhds]
      exact (hL t ⟨by linarith [ht.1], by linarith⟩).congr_of_eventuallyEq hnear
    · subst t
      rw [hneg]
      have hleft : HasDerivWithinAt (extend q g) (f (g (-q))) (Iic (-q)) (-q) := by
        have hd : HasDerivAt (fun s => C (g (-q)) (s + q)) (f (g (-q))) (-q) := by
          simpa only [neg_add_cancel, hC0] using hL (-q) ⟨by linarith, by linarith⟩
        refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with s hs
          by_cases hslt : s < -q
          · exact if_pos hslt
          · have hseq : s = -q := le_antisymm hs (le_of_not_gt hslt)
            subst s
            simpa only [neg_add_cancel, hC0] using hneg
        · simpa only [neg_add_cancel, hC0] using hneg
      have hright : HasDerivWithinAt (extend q g) (f (g (-q))) (Ici (-q)) (-q) := by
        refine (hg (-q) ⟨by linarith, by linarith⟩).hasDerivWithinAt.congr_of_eventuallyEq ?_ hneg
        filter_upwards [Ico_mem_nhdsGE (show -q < q by linarith)] with s hs
        dsimp [extend]
        rw [if_neg (not_lt.mpr hs.1), if_neg (not_lt.mpr hs.2.le)]
      simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright
    · rcases lt_trichotomy t q with hltq | heqq | hgtq
      · have hnear : extend q g =ᶠ[𝓝 t] g := by
          filter_upwards [Ioo_mem_nhds hgt hltq] with s hs
          dsimp [extend]
          rw [if_neg (not_lt.mpr hs.1.le), if_neg (not_lt.mpr hs.2.le)]
        rw [hnear.eq_of_nhds]
        exact (hg t ⟨by linarith, by linarith⟩).congr_of_eventuallyEq hnear
      · subst t
        rw [hpos]
        have hleft : HasDerivWithinAt (extend q g) (f (g q)) (Iic q) q := by
          refine (hg q ⟨by linarith, by linarith⟩).hasDerivWithinAt.congr_of_eventuallyEq ?_ hpos
          filter_upwards [Ioc_mem_nhdsLE (show -q < q by linarith)] with s hs
          dsimp [extend]
          rw [if_neg (not_lt.mpr hs.1.le), if_neg (not_lt.mpr hs.2)]
        have hright : HasDerivWithinAt (extend q g) (f (g q)) (Ici q) q := by
          have hd : HasDerivAt (fun s => C (g q) (s - q)) (f (g q)) q := by
            simpa only [sub_self, hC0] using hR q ⟨by linarith, by linarith⟩
          refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [self_mem_nhdsWithin] with s hs
            by_cases hsqlt : q < s
            · dsimp [extend]
              rw [if_neg (by linarith), if_pos hsqlt]
            · have hseq : s = q := le_antisymm (le_of_not_gt hsqlt) hs
              subst s
              simpa only [sub_self, hC0] using hpos
          · simpa only [sub_self, hC0] using hpos
        simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright
      · have hnear : extend q g =ᶠ[𝓝 t] (fun s => C (g q) (s - q)) := by
          filter_upwards [Ioi_mem_nhds hgtq] with s hs
          change q < s at hs
          dsimp [extend]
          rw [if_neg (by linarith), if_pos hs]
        rw [hnear.eq_of_nhds]
        exact (hR t ⟨by linarith, by linarith [ht.2]⟩).congr_of_eventuallyEq hnear
  let u : ℕ → ℝ → E :=
    Nat.rec (C x0) (fun n g => extend (((n : ℝ) + 1) * τ) g)
  have hstep (n : ℕ) : u (n + 1) = extend (((n : ℝ) + 1) * τ) (u n) := rfl
  have hu (n : ℕ) : u n 0 = x0 ∧
      ∀ t ∈ Ioo (-((n : ℝ) + 2) * τ) (((n : ℝ) + 2) * τ),
        HasDerivAt (u n) (f (u n t)) t := by
    induction n with
    | zero =>
      refine ⟨hC0 x0, ?_⟩
      intro t ht
      apply hCd x0 t
      simp only [Nat.cast_zero, zero_add] at ht
      constructor <;> nlinarith [ht.1, ht.2]
    | succ n ih =>
      have hq : 0 < ((n : ℝ) + 1) * τ := by positivity
      refine ⟨?_, ?_⟩
      · rw [hstep]
        dsimp [extend]
        rw [if_neg (by linarith), if_neg (by linarith)]
        exact ih.1
      · intro t ht
        simp only [Nat.cast_succ] at ht
        rw [hstep]
        apply hextend (((n : ℝ) + 1) * τ) hq (u n)
        · intro s hs
          apply ih.2 s
          constructor <;> nlinarith [hs.1, hs.2]
        · constructor <;> nlinarith [ht.1, ht.2]
  have hstable (n : ℕ) (t : ℝ)
      (ht : |t| ≤ ((n : ℝ) + 1) * τ) : u (n + 1) t = u n t := by
    rw [hstep]
    dsimp [extend]
    have hb := abs_le.mp ht
    rw [if_neg (not_lt.mpr hb.1), if_neg (not_lt.mpr hb.2)]
  have hfinite : LocallyFinite (fun n => {t : ℝ | u (n + 1) t ≠ u n t}) := by
    intro t
    let R : ℝ := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (R / τ)
    have hNmul : R < (N : ℝ) * τ := (div_lt_iff₀ hτ).mp hN
    refine ⟨Ioo (-R) R, Ioo_mem_nhds ?_ ?_, (Set.finite_le_nat N).subset ?_⟩
    · dsimp [R]
      linarith [neg_abs_le t]
    · dsimp [R]
      linarith [le_abs_self t]
    · intro n hn
      by_contra hnN
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact Nat.cast_le.mpr (Nat.lt_of_not_ge hnN).le
      have hNnmul : (N : ℝ) * τ ≤ (n : ℝ) * τ :=
        mul_le_mul_of_nonneg_right hNn hτ.le
      obtain ⟨s, hschange, hs⟩ := hn
      have hsq : |s| ≤ ((n : ℝ) + 1) * τ := by
        have hsabs : |s| < R := abs_lt.mpr hs
        nlinarith
      exact hschange (hstable n s hsq)
  obtain ⟨γ, hγ⟩ := hfinite.exists_forall_eventually_atTop_eventuallyEq
  refine ⟨γ, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (hγ 0).exists
    exact (hn.eq_of_nhds).symm.trans (hu n).1
  · intro t
    obtain ⟨N, hN⟩ := exists_nat_gt (|t| / τ)
    have hNmul : |t| < (N : ℝ) * τ := (div_lt_iff₀ hτ).mp hN
    obtain ⟨n, hnN, hnear⟩ := ((eventually_ge_atTop N).and (hγ t)).exists
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact Nat.cast_le.mpr hnN
    have hNnmul : (N : ℝ) * τ ≤ (n : ℝ) * τ :=
      mul_le_mul_of_nonneg_right hNn hτ.le
    have ht : t ∈ Ioo (-((n : ℝ) + 2) * τ) (((n : ℝ) + 2) * τ) := by
      have hb : |t| < ((n : ℝ) + 2) * τ := by nlinarith
      simpa only [Set.mem_Ioo, neg_mul] using (abs_lt.mp hb)
    have hd := ((hu n).2 t ht).congr_of_eventuallyEq hnear.symm
    rw [hnear.eq_of_nhds] at hd
    exact hd


end D5.S3.Geometry.ODE.UniformLocalGlobalPasting
