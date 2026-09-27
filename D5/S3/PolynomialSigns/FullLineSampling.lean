/- GID: D5/S3/PolynomialSigns/FullLineSampling
   generality: G
   mirror-B: D5/B/S3/PolynomialSigns/FullLineSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Polynomial.Order, mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Polynomial]
   utility: none
   digest: Joint real polynomial signs are represented by two tails, product roots, or critical points. -/

import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial Filter Set
open scoped BigOperators

noncomputable section
namespace D5.S3.PolynomialSigns.FullLineSampling

/-- Negative, zero and positive real values have codes zero, one and two. -/
def ternary (a : ℝ) : Fin 3 := if a < 0 then 0 else if a = 0 then 1 else 2

/-- A joint sign vector is realized on the real line exactly when it occurs on
one tail, at a root of the product of nonzero members, or at a derivative root
of that product. Each root alternative uses one common point for every member. -/
theorem full_line_sampling {m : ℕ} (f : Fin m → ℝ[X]) (s : Fin m → Fin 3) :
    let p := ∏ i, if f i = 0 then 1 else f i
    (∃ y : ℝ, ∀ i, ternary ((f i).eval y) = s i) ↔
      (∀ i, ternary (f i).leadingCoeff = s i) ∨
      (∀ i, ternary ((f i).comp (-X)).leadingCoeff = s i) ∨
      (∃ r : p.roots.toFinset, ∀ i, ternary ((f i).eval r.val) = s i) ∨
      (∃ r : p.derivative.roots.toFinset, ∀ i, ternary ((f i).eval r.val) = s i) := by
  classical
  intro p
  have tailPositive (p : ℝ[X]) :
      ∀ᶠ y in atTop, ternary (p.eval y) = ternary p.leadingCoeff := by
    by_cases hd : p.natDegree = 0
    · have h := Polynomial.eq_C_of_natDegree_eq_zero hd
      rw [h]
      exact Filter.Eventually.of_forall (by intro y; simp)
    have hd' : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have hp : p ≠ 0 := Polynomial.ne_zero_of_degree_gt hd'
    have hl := Polynomial.leadingCoeff_ne_zero.mpr hp
    rcases lt_or_gt_of_ne hl with hn | hn
    · have h := (p.tendsto_atBot_of_leadingCoeff_nonpos hd' hn.le).eventually (eventually_lt_atBot 0)
      filter_upwards [h] with y hy
      simp [ternary,hy,hn,not_lt.mpr hy.le,not_lt.mpr hn.le]
    · have h := (p.tendsto_atTop_of_leadingCoeff_nonneg hd' hn.le).eventually (eventually_gt_atTop 0)
      filter_upwards [h] with y hy
      simp [ternary,not_lt.mpr hy.le,not_lt.mpr hn.le,ne_of_gt hy,ne_of_gt hn,hp]
  have tailNegative (p : ℝ[X]) :
      ∀ᶠ y in atBot, ternary (p.eval y) = ternary (p.comp (-X)).leadingCoeff := by
    have h := tailPositive (p.comp (-X))
    have h' := tendsto_neg_atBot_atTop.eventually h
    simpa only [Function.comp_apply, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X, neg_neg] using h'
  have hp : p ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    split_ifs with hi
    · exact one_ne_zero
    · exact hi
  have htop : ∀ᶠ y in atTop, ∀ i, ternary ((f i).eval y) = ternary (f i).leadingCoeff :=
    Filter.eventually_all.mpr (fun i => tailPositive (f i))
  have hbot : ∀ᶠ y in atBot, ∀ i, ternary ((f i).eval y) =
      ternary ((f i).comp (-X)).leadingCoeff :=
    Filter.eventually_all.mpr (fun i => tailNegative (f i))
  have hmem (z : ℝ) : z ∈ p.roots.toFinset ↔ p.IsRoot z := by
    rw [Multiset.mem_toFinset, mem_roots hp]
  have hroot (i : Fin m) (hi : f i ≠ 0) {z : ℝ} (hz : (f i).IsRoot z) : p.IsRoot z := by
    apply hz.dvd
    have hd := Finset.dvd_prod_of_mem (fun i => if f i = 0 then 1 else f i)
      (Finset.mem_univ i)
    simpa [hi] using hd
  have same {S : Set ℝ} (hS : IsPreconnected S) {u v : ℝ}
      (hu : u ∈ S) (hv : v ∈ S) (i : Fin m)
      (hn : ∀ z ∈ S, (f i).eval z ≠ 0) :
      ternary ((f i).eval u) = ternary ((f i).eval v) := by
    have hcross {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S)
        (ha0 : (f i).eval a < 0) (hb0 : 0 < (f i).eval b) : False := by
      obtain ⟨z,hz,he⟩ := hS.intermediate_value ha hb (f i).continuous.continuousOn
        (show (0 : ℝ) ∈ Icc ((f i).eval a) ((f i).eval b) from ⟨ha0.le,hb0.le⟩)
      exact hn z hz he
    rcases lt_or_gt_of_ne (hn u hu) with hnU | hpU <;>
      rcases lt_or_gt_of_ne (hn v hv) with hnV | hpV
    · simp [ternary,hnU,hnV,not_lt.mpr hnU.le,not_lt.mpr hnV.le]
    · exact (hcross hu hv hnU hpV).elim
    · exact (hcross hv hu hnV hpU).elim
    · simp [ternary,not_lt.mpr hpU.le,not_lt.mpr hpV.le,ne_of_gt hpU,ne_of_gt hpV]
  constructor
  · rintro ⟨x,hx⟩
    by_cases hx0 : p.IsRoot x
    · exact Or.inr (Or.inr (Or.inl ⟨⟨x,(hmem x).mpr hx0⟩,hx⟩))
    let L := p.roots.toFinset.filter (· < x)
    let U := p.roots.toFinset.filter (x < ·)
    by_cases hL : L.Nonempty
    · by_cases hU : U.Nonempty
      · let a := L.max' hL
        let b := U.min' hU
        have ha := Finset.mem_filter.mp (L.max'_mem hL)
        have hb := Finset.mem_filter.mp (U.min'_mem hU)
        have hab : a < b := ha.2.trans hb.2
        have ha0 : p.eval a = 0 := (hmem _).mp ha.1
        have hb0 : p.eval b = 0 := (hmem _).mp hb.1
        have hnone : ∀ z ∈ Ioo a b, ¬ p.IsRoot z := by
          intro z hz hz0
          rcases lt_trichotomy z x with hzx | rfl | hxz
          · have hzL : z ∈ L := Finset.mem_filter.mpr ⟨(hmem _).mpr hz0,hzx⟩
            exact (not_le_of_gt hz.1) (L.le_max' z hzL)
          · exact hx0 hz0
          · have hzU : z ∈ U := Finset.mem_filter.mpr ⟨(hmem _).mpr hz0,hxz⟩
            exact (not_le_of_gt hz.2) (U.min'_le z hzU)
        obtain ⟨y,hy,hdy⟩ := exists_deriv_eq_zero hab p.continuous.continuousOn (ha0.trans hb0.symm)
        have hd : p.derivative ≠ 0 := by
          intro hd
          have hc := eq_C_of_derivative_eq_zero hd
          have hc0 : p.coeff 0 = 0 := by
            have h := ha0
            rw [hc,eval_C] at h
            exact h
          exact hp (by rw [hc,hc0,C_0])
        have hyr : y ∈ p.derivative.roots.toFinset := by
          rw [Multiset.mem_toFinset,mem_roots hd,IsRoot,← p.deriv]
          exact hdy
        refine Or.inr (Or.inr (Or.inr ⟨⟨y,hyr⟩,fun i => ?_⟩))
        by_cases hi : f i = 0
        · simpa only [hi,eval_zero] using hx i
        · exact (same isPreconnected_Ioo hy ⟨ha.2,hb.2⟩ i
            (fun z hz he => hnone z hz (hroot i hi he))).trans (hx i)
      · obtain ⟨y,hy,hyx⟩ := (htop.and (eventually_ge_atTop x)).exists
        refine Or.inl (fun i => ?_)
        rw [← hy i]
        by_cases hi : f i = 0
        · simpa only [hi,eval_zero] using hx i
        apply Eq.trans (same isPreconnected_Ici hyx (le_refl x) i ?_) (hx i)
        intro z hz he
        have hz0 := hroot i hi he
        rcases eq_or_lt_of_le (show x ≤ z from hz) with rfl | hlt
        · exact hx0 hz0
        · exact hU ⟨z,Finset.mem_filter.mpr ⟨(hmem _).mpr hz0,hlt⟩⟩
    · obtain ⟨y,hy,hyx⟩ := (hbot.and (eventually_le_atBot x)).exists
      refine Or.inr (Or.inl (fun i => ?_))
      rw [← hy i]
      by_cases hi : f i = 0
      · simpa only [hi,eval_zero] using hx i
      apply Eq.trans (same isPreconnected_Iic hyx (le_refl x) i ?_) (hx i)
      intro z hz he
      have hz0 := hroot i hi he
      rcases eq_or_lt_of_le (show z ≤ x from hz) with rfl | hlt
      · exact hx0 hz0
      · exact hL ⟨z,Finset.mem_filter.mpr ⟨(hmem _).mpr hz0,hlt⟩⟩
  · rintro (ht | hb | ⟨r,hr⟩ | ⟨r,hr⟩)
    · obtain ⟨y,hy⟩ := htop.exists
      exact ⟨y,fun i => (hy i).trans (ht i)⟩
    · obtain ⟨y,hy⟩ := hbot.exists
      exact ⟨y,fun i => (hy i).trans (hb i)⟩
    · exact ⟨r.val,hr⟩
    · exact ⟨r.val,hr⟩
#print axioms full_line_sampling

end D5.S3.PolynomialSigns.FullLineSampling
