/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive
   mirror-E: none(waiver:coefficient-asymptotics)
   anchors: [mathlib/module/Mathlib.Analysis.Asymptotics.SpecificAsymptotics]
   utility: none
   digest: Coefficient limits for the finite geometric convolutions in D-prime. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Real.Pi.Wallis

/-! Normalized coefficient limits, with all arithmetic progressions retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive

open Finset Filter Asymptotics PowerSeries AndrewsElBachraouiDefs
open AndrewsElBachraouiFiveReduction AndrewsElBachraouiFiveConstants
open scoped Topology BigOperators

private theorem shifted_power_sum_limit (p : ℕ) :
    Tendsto (fun n : ℕ => (∑ i ∈ range n, ((i : ℝ) + 1) ^ p) / (n : ℝ) ^ (p + 1))
      atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  have hmono (n : ℕ) : MonotoneOn (fun x : ℝ => x ^ p) (Set.Icc 0 (0 + n)) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ hx.1 hxy p
  have hbounds (n : ℕ) :
      (n : ℝ) ^ (p + 1) / (p + 1 : ℝ) ≤ ∑ i ∈ range n, ((i : ℝ) + 1) ^ p ∧
      (∑ i ∈ range n, ((i : ℝ) + 1) ^ p) ≤
        (n : ℝ) ^ (p + 1) / (p + 1 : ℝ) + (n : ℝ) ^ p := by
    have hlo := (hmono n).integral_le_sum
    have hhi := (hmono n).sum_le_integral
    simp only [zero_add, _root_.integral_pow, zero_pow (by omega : p + 1 ≠ 0),
      sub_zero, Nat.cast_add, Nat.cast_one] at hlo hhi
    have hshift := sum_range_succ' (fun i : ℕ => (i : ℝ) ^ p) n
    rw [sum_range_succ] at hshift
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hshift
    exact ⟨hlo, by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 0) p]⟩
  have hupper : Tendsto (fun n : ℕ => 1 / (p + 1 : ℝ) + 1 / (n : ℝ))
      atTop (𝓝 (1 / (p + 1 : ℝ))) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := 1 / (p + 1 : ℝ))).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ (pow_pos hnR _)]
    simpa only [one_div_mul_eq_div] using (hbounds n).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ (pow_pos hnR _)]
    calc
      _ ≤ (n : ℝ) ^ (p + 1) / (p + 1 : ℝ) + (n : ℝ) ^ p := (hbounds n).2
      _ = _ := by rw [pow_succ]; field_simp

private theorem partial_sum_limit (a : ℕ → ℝ) (p : ℕ) (A : ℝ)
    (ha : Tendsto (fun n => a n / (n : ℝ) ^ p) atTop (𝓝 A)) :
    Tendsto (fun n : ℕ => (∑ i ∈ range n, a i) / (n : ℝ) ^ (p + 1))
      atTop (𝓝 (A / (p + 1 : ℝ))) := by
  let g (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ p
  let S (n : ℕ) : ℝ := ∑ i ∈ range n, g i
  have hg (n : ℕ) : 1 ≤ g n := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hS : Tendsto S atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) _ tendsto_natCast_atTop_atTop
    intro n
    simpa only [S, sum_const, card_range, nsmul_eq_mul, mul_one] using
      (sum_le_sum (s := range n) (fun i _ => hg i))
  have hratio : Tendsto (fun n => a n / g n) atTop (𝓝 A) := by
    have h := ha.mul ((tendsto_natCast_div_add_atTop (1 : ℝ)).pow p)
    simp only [one_pow, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp [g]
    rw [div_pow]
    field_simp
  have he : (fun n => a n - A * g n) =o[atTop] g := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · have h := hratio.sub (tendsto_const_nhds (x := A))
      simp only [sub_self] at h
      apply h.congr'
      exact Eventually.of_forall fun n => by
        dsimp only
        rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (hg n)))]
    · exact Eventually.of_forall fun n hn => (ne_of_gt (lt_of_lt_of_le zero_lt_one (hg n)) hn).elim
  have herror := (he.sum_range (fun n => (hg n).trans' zero_le_one) hS).tendsto_div_nhds_zero
  have hlim := shifted_power_sum_limit p
  change Tendsto (fun n => S n / (n : ℝ) ^ (p + 1)) atTop _ at hlim
  have herr := herror.mul hlim
  simp only [zero_mul] at herr
  have htotal := (hlim.const_mul A).add herr
  simp only [mul_one_div, add_zero] at htotal
  apply htotal.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hSn : S n ≠ 0 := by
    have hle : (n : ℝ) ≤ S n := by
      simpa only [S, sum_const, card_range, nsmul_eq_mul, mul_one] using
        (sum_le_sum (s := range n) (fun i _ => hg i))
    linarith
  simp only [sum_sub_distrib, ← mul_sum]
  change A * (S n / (n : ℝ) ^ (p + 1)) +
    ((∑ i ∈ range n, a i) - A * S n) / S n *
      (S n / (n : ℝ) ^ (p + 1)) = _
  field_simp [hSn]
  <;> ring

private theorem tendsto_of_residue_limits (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℝ) (L : ℝ)
    (h : ∀ r : Fin d, Tendsto (fun j : ℕ => f (d * j + r)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  classical
  rw [Filter.tendsto_def]
  intro U hU
  have hr (r : Fin d) : ∃ J : ℕ, ∀ j ≥ J, f (d * j + r) ∈ U :=
    eventually_atTop.mp ((h r).eventually hU)
  choose J hJ using hr
  rw [mem_atTop_sets]
  refine ⟨d * (univ.sup J), ?_⟩
  intro n hn
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hj : J r ≤ n / d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    calc J r * d ≤ (univ.sup J) * d := Nat.mul_le_mul_right d (le_sup (mem_univ r))
         _ ≤ n := by simpa [Nat.mul_comm] using hn
  simpa [r, Nat.mul_comm, Nat.div_add_mod] using hJ r (n / d) hj

private theorem progression_sum_limit (a : ℕ → ℝ) (p d : ℕ) (A : ℝ)
    (hd : 0 < d) (ha : Tendsto (fun n => a n / (n : ℝ) ^ p) atTop (𝓝 A)) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ range (n / d + 1), a (d * i + n % d)) / (n : ℝ) ^ (p + 1))
      atTop (𝓝 (A / ((d : ℝ) * (p + 1)))) := by
  apply tendsto_of_residue_limits d hd
  intro r
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have htop : Tendsto (fun j : ℕ => d * j + (r : ℕ)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun j : ℕ => j) _ tendsto_id
    intro j
    have := Nat.mul_le_mul_right j hd
    omega
  have hscale : Tendsto (fun j : ℕ => ((d * j + (r : ℕ) : ℕ) : ℝ) / j)
      atTop (𝓝 (d : ℝ)) := by
    have h := (tendsto_const_nhds (x := (d : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (r : ℝ))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    push_cast
    field_simp
  have hsub : Tendsto (fun j : ℕ => a (d * j + r) / (j : ℝ) ^ p)
      atTop (𝓝 (A * (d : ℝ) ^ p)) := by
    have h := (ha.comp htop).mul (hscale.pow p)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    have hxR : (0 : ℝ) < (d * j + (r : ℕ) : ℕ) := by
      exact_mod_cast (show 0 < d * j + (r : ℕ) from by nlinarith)
    dsimp only [Function.comp_apply]
    rw [div_pow]
    field_simp
  have hsum := partial_sum_limit (fun j => a (d * j + r)) p (A * (d : ℝ)^p) hsub
  have hjtop : Tendsto (fun j : ℕ => j + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hscale' : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) /
      ((d * j + (r : ℕ) : ℕ) : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
    have hnum := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [add_zero] at hnum
    have h := hnum.div hscale (ne_of_gt hdR)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    change (1 + 1 / (j : ℝ)) / (((d * j + (r : ℕ) : ℕ) : ℝ) / j) = _
    push_cast
    field_simp
  have h := (hsum.comp hjtop).mul (hscale'.pow (p + 1))
  have hconstant : A * (d : ℝ)^p / (p + 1 : ℝ) * (1 / (d : ℝ))^(p+1) =
      A / ((d : ℝ) * (p + 1)) := by
    rw [pow_succ, div_pow]
    field_simp
    <;> simp
  rw [hconstant] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hjR : (0 : ℝ) < j + 1 := by positivity
  have hxR : (0 : ℝ) < (d * j + (r : ℕ) : ℕ) := by
    exact_mod_cast (show 0 < d * j + (r : ℕ) from by nlinarith)
  have hdiv : (d * j + (r : ℕ)) / d = j := by
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt r.isLt, Nat.add_zero]
  have hmod : (d * j + (r : ℕ)) % d = r := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt]
  simp only [hdiv, hmod, Function.comp_apply]
  rw [div_pow]
  field_simp

private theorem coeff_mul_geom_progression (F : PowerSeries ℤ) (d n : ℕ) (hd : 0 < d) :
    PowerSeries.coeff n (F * AndrewsElBachraouiDefs.geom d) =
      ∑ i ∈ range (n / d + 1), PowerSeries.coeff (d*i+n%d) F := by
  have hg : geom d = 1 + X^d * geom d := by
    have h := AndrewsElBachraouiFiveReduction.geom_mul_one_sub d hd
    calc geom d = geom d * (1-X^d) + X^d*geom d := by ring
         _ = _ := by rw [h]
  have hF : F * geom d = F + X^d * (F * geom d) := by
    calc F*geom d = F*(1+X^d*geom d) := congrArg (F * ·) hg
         _ = _ := by ring
  have hres (j r : ℕ) (hr : r < d) :
      coeff (d*j+r) (F*geom d) = ∑ i ∈ range (j+1), coeff (d*i+r) F := by
    induction j with
    | zero =>
      have h := congrArg (coeff r) hF
      rw [map_add, coeff_X_pow_mul', if_neg (by omega), add_zero] at h
      simpa using h
    | succ j ih =>
      have h := congrArg (coeff (d*(j+1)+r)) hF
      have hle : d ≤ d*(j+1)+r := by rw [Nat.mul_add, Nat.mul_one]; omega
      have hsub : d*(j+1)+r-d = d*j+r := by rw [Nat.mul_add, Nat.mul_one]; omega
      rw [map_add, coeff_X_pow_mul', if_pos hle, hsub, ih] at h
      rw [sum_range_succ]
      exact h.trans (add_comm _ _)
  have h := hres (n/d) (n%d) (Nat.mod_lt n hd)
  simpa [Nat.mul_comm, Nat.div_add_mod] using h

private theorem coeff_geom_limit (F : PowerSeries ℤ) (p d : ℕ) (A : ℝ)
    (hd : 0 < d)
    (ha : Tendsto (fun n => ((PowerSeries.coeff n F : ℤ) : ℝ) / (n : ℝ)^p)
      atTop (𝓝 A)) :
    Tendsto (fun n => ((PowerSeries.coeff n (F * AndrewsElBachraouiDefs.geom d) : ℤ) : ℝ) /
      (n : ℝ)^(p+1)) atTop (𝓝 (A / ((d : ℝ)*(p+1)))) := by
  have h := progression_sum_limit (fun n => ((PowerSeries.coeff n F : ℤ) : ℝ)) p d A hd ha
  apply h.congr
  intro n
  rw [coeff_mul_geom_progression F d n hd, Int.cast_sum]

private theorem finite_geom_limit {α : Type} [DecidableEq α] (s : Finset α) (d : α → ℕ)
    (hd : ∀ i ∈ s, 0 < d i) :
    Tendsto (fun n =>
      ((PowerSeries.coeff n (AndrewsElBachraouiDefs.geom 1 *
        ∏ i ∈ s, AndrewsElBachraouiDefs.geom (d i)) : ℤ) : ℝ) / (n : ℝ)^s.card)
      atTop (𝓝 (1 / ((s.card.factorial : ℝ) * ∏ i ∈ s, (d i : ℝ)))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [AndrewsElBachraouiDefs.geom, PowerSeries.coeff_mk] using
      (tendsto_const_nhds (x := (1 : ℝ)) : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | @insert i s hi ih =>
    have hdi := hd i (mem_insert_self i s)
    have hds : ∀ j ∈ s, 0 < d j := fun j hj => hd j (mem_insert_of_mem hj)
    have h := coeff_geom_limit (AndrewsElBachraouiDefs.geom 1 *
      ∏ j ∈ s, AndrewsElBachraouiDefs.geom (d j)) s.card (d i)
      (1 / ((s.card.factorial : ℝ) * ∏ j ∈ s, (d j : ℝ))) hdi (ih hds)
    have heq : AndrewsElBachraouiDefs.geom 1 *
        (∏ j ∈ insert i s, AndrewsElBachraouiDefs.geom (d j)) =
        (AndrewsElBachraouiDefs.geom 1 * ∏ j ∈ s, AndrewsElBachraouiDefs.geom (d j)) *
          AndrewsElBachraouiDefs.geom (d i) := by rw [prod_insert hi]; ring
    rw [heq, card_insert_of_notMem hi]
    convert h using 1
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, prod_insert hi, div_div]
    congr 1
    ring

private theorem shifted_coeff_limit (F : PowerSeries ℤ) (p b : ℕ) (A : ℝ)
    (ha : Tendsto (fun n => ((coeff n F : ℤ) : ℝ)/(n : ℝ)^p) atTop (𝓝 A)) :
    Tendsto (fun n => ((coeff n (X^b*F) : ℤ) : ℝ)/(n : ℝ)^p) atTop (𝓝 A) := by
  have htop : Tendsto (fun n : ℕ => n-b) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [eventually_ge_atTop (c+b)] with n hn
    omega
  have hscale : Tendsto (fun n : ℕ => ((n-b : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (b : ℝ))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (b+1)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_sub (by omega)]
    field_simp
  have h := (ha.comp htop).mul (hscale.pow p)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (b+1)] with n hn
  have ht : (0 : ℝ) < ((n-b : ℕ) : ℝ) := by exact_mod_cast (show 0<n-b by omega)
  rw [coeff_X_pow_mul', ite_eq_left (by omega)]
  dsimp only [Function.comp_apply]
  rw [div_pow]
  field_simp

private theorem rational_limit (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) :
    Tendsto (fun n : ℕ => ((coeff n (rationalSeries k m) : ℤ) : ℝ) /
      (n : ℝ)^(k-1)) atTop (𝓝 (rationalConstant (k-1))) := by
  classical
  let h := k-1
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hs : (offsetIndices k m).card = h-1 := by
    simp only [offsetIndices, card_disjSum, card_range]
    dsimp [h]
    omega
  let O : PowerSeries ℤ := ∏ i ∈ range h, geom (2*i+1)
  have hO : O = geom 1 * ∏ i ∈ range (h-1), geom (2*i+3) := by
    have heq := prod_range_succ' (fun i : ℕ => geom (2*i+1)) (h-1)
    rw [show h-1+1=h by omega] at heq
    simp only [show ∀ i : ℕ, 2*(i+1)+1=2*i+3 by omega,
      Nat.mul_zero, Nat.zero_add] at heq
    exact heq.trans (mul_comm _ _)
  have hodd : (∏ i ∈ range (h-1), (2*(i : ℝ)+3)) = oddProd h := by
    have heq := prod_range_succ' (fun i : ℕ => (2*(i : ℝ)+1)) (h-1)
    rw [show h-1+1=h by omega] at heq
    simpa [oddProd, Nat.cast_add, Nat.cast_one, mul_add, add_assoc, show (2 : ℝ)+1=3 by norm_num] using heq.symm
  have hbase := finite_geom_limit (range (h-1)) (fun i => 2*i+3)
    (fun i _ => by omega)
  rw [← hO] at hbase
  have hbase' : Tendsto (fun n => ((coeff n O : ℤ) : ℝ)/(n : ℝ)^(h-1)) atTop
      (𝓝 (1 / (((h-1).factorial : ℝ)*oddProd h))) := by
    simpa only [card_range, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hodd] using hbase
  have hterm (S : Finset (ℕ ⊕ ℕ)) :
      Tendsto (fun n => ((coeff n
        (C ((-1 : ℤ)^S.card)*X^(∑ i ∈ S, offset m i)*geom (2*S.card+1)*O) : ℤ) : ℝ)/
          (n : ℝ)^h) atTop
      (𝓝 (((-1 : ℝ)^S.card) / ((h.factorial : ℝ)*oddProd h*(2*S.card+1)))) := by
    have hlim := coeff_geom_limit O (h-1) (2*S.card+1)
      (1 / (((h-1).factorial : ℝ)*oddProd h)) (by omega) hbase'
    rw [show h-1+1=h by omega] at hlim
    have hc : (1 / (((h-1).factorial : ℝ)*oddProd h)) /
        (((2*S.card+1 : ℕ) : ℝ) * (((h-1 : ℕ) : ℝ)+1)) =
        1 / ((h.factorial : ℝ)*oddProd h*(2*S.card+1)) := by
      have hfac : (h.factorial : ℝ) = (h : ℝ)*((h-1).factorial : ℝ) := by
        conv_lhs => rw [show h=(h-1)+1 by omega, Nat.factorial_succ]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        congr 1
        rw [Nat.cast_sub hh]; norm_num
      rw [hfac]
      have hcast : ((h-1 : ℕ) : ℝ)+1=(h : ℝ) := by exact_mod_cast (show h-1+1=h by omega)
      rw [hcast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      rw [div_div]
      congr 1
      ring
    rw [hc] at hlim
    have hshift := shifted_coeff_limit (O*geom (2*S.card+1)) h
      (∑ i ∈ S, offset m i) _ hlim
    have hscaled := hshift.const_mul ((-1 : ℝ)^S.card)
    simp only [mul_one_div] at hscaled
    convert hscaled using 1
    · funext n
      rw [show C ((-1 : ℤ)^S.card)*X^(∑ i ∈ S, offset m i)*geom (2*S.card+1)*O =
          C ((-1 : ℤ)^S.card)*(X^(∑ i ∈ S, offset m i)*(O*geom (2*S.card+1))) by ring,
        coeff_C_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
      ring
  have hsum := tendsto_finsetSum (offsetIndices k m).powerset (fun S _ => hterm S)
  have hexpr (n : ℕ) : ((coeff n (rationalSeries k m) : ℤ) : ℝ)/(n : ℝ)^h =
      ∑ S ∈ (offsetIndices k m).powerset,
        ((coeff n (C ((-1 : ℤ)^S.card)*X^(∑ i ∈ S, offset m i)*geom (2*S.card+1)*O) : ℤ) : ℝ)/
          (n : ℝ)^h := by
    simp only [rationalSeries, sum_mul, map_sum, Int.cast_sum, sum_div]
    rfl
  have hconstant : (∑ S ∈ (offsetIndices k m).powerset,
      (-1 : ℝ)^S.card / ((h.factorial : ℝ)*oddProd h*(2*S.card+1))) =
        rationalConstant h := by
    simp_rw [show ∀ S : Finset (ℕ ⊕ ℕ), (-1 : ℝ)^S.card /
        ((h.factorial : ℝ)*oddProd h*(2*S.card+1)) =
        ((-1 : ℝ)^S.card / (2*S.card+1)) / ((h.factorial : ℝ)*oddProd h) by
      intro S; rw [div_div]; congr 1; ring]
    rw [← sum_div, subset_constant, hs]
    rfl
  rw [hconstant] at hsum
  exact hsum.congr (fun n => (hexpr n).symm)

private noncomputable def gaussUpper (n : ℕ) : ℝ :=
  Real.pi/4*n + 5/4*Real.sqrt (2*(n : ℝ)+1/2) + Real.pi/16+3/8

private theorem gauss_upper_limit :
    Tendsto (fun n : ℕ => gaussUpper n/(n : ℝ)) atTop (𝓝 (Real.pi/4)) := by
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.const_mul (1/2 : ℝ))
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hsmall
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (2*(n : ℝ)+1/2)/(n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    have h := hsmall.sqrt
    simp only [Real.sqrt_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hid : (2 : ℝ)/n + (1/2)*(1/(n : ℝ))^2 =
        (2*(n : ℝ)+1/2)/(n : ℝ)^2 := by field_simp
    rw [hid, Real.sqrt_div (by positivity), Real.sqrt_sq (le_of_lt hnR)]
  have h := (((tendsto_const_nhds (x := Real.pi/4)).add (hsqrt.const_mul (5/4 : ℝ))).add
    (tendsto_const_div_atTop_nhds_zero_nat (Real.pi/16))).add
      (tendsto_const_div_atTop_nhds_zero_nat (3/8 : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [gaussUpper]
  field_simp
  <;> ring

private noncomputable def evenUpper : ℕ → ℕ → ℝ
  | 0 => gaussUpper
  | r+1 => fun n => ∑ i ∈ range (n/(2*r+4)+1), evenUpper r ((2*r+4)*i+n%(2*r+4))

private theorem even_upper_limit (r : ℕ) :
    Tendsto (fun n : ℕ => evenUpper r n/(n : ℝ)^(r+1))
      atTop (𝓝 (productConstant (r+1))) := by
  induction r with
  | zero =>
    convert gauss_upper_limit using 1 <;> norm_num [evenUpper, productConstant]
  | succ r ih =>
    have h := progression_sum_limit (evenUpper r) (r+1) (2*r+4)
      (productConstant (r+1)) (by omega) ih
    change Tendsto (fun n => evenUpper (r+1) n/(n : ℝ)^(r+1+1)) atTop _ at h
    convert h using 1
    congr 1
    simp only [productConstant, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat, pow_add, pow_one]
    rw [div_div]
    congr 1
    ring

private theorem product_upper (r n : ℕ) :
    ((coeff n (gaussSeries * ∏ i ∈ range r, geom (2*i+4)) : ℤ) : ℝ) ≤ evenUpper r n := by
  induction r generalizing n with
  | zero =>
    simpa only [prod_range_zero, mul_one, gaussSeries, coeff_mk, evenUpper, gaussUpper] using
      AndrewsElBachraouiFiveGauss.gauss_coefficient_upper n
  | succ r ih =>
    rw [prod_range_succ, ← mul_assoc,
      coeff_mul_geom_progression _ (2*r+4) n (by omega), Int.cast_sum]
    exact sum_le_sum (fun i _ => ih _)

/-- Andrews–El Bachraoui Conjecture 5 on the original coefficient family, with all parameters. -/
theorem result : ∀ k m : ℕ, 1 ≤ m → m < k →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ dCoeff k m n := by
  intro k m hm hmk
  have hh : 1 ≤ k-1 := by omega
  have hU := even_upper_limit (k-2)
  have he : k-2+1=k-1 := by omega
  rw [he] at hU
  have hlim := (rational_limit k m hm hmk).sub hU
  have hpos := hlim.eventually_const_lt (leading_gap_pos (k-1) hh)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 1 ≤ n by omega)
  have ht := hN n (by omega)
  have hP := product_upper (k-2) n
  change ((coeff n (productSeries k) : ℤ) : ℝ) ≤ evenUpper (k-2) n at hP
  have hdiv := (div_le_div_of_nonneg_right hP (le_of_lt (pow_pos hnR (k-1))))
  have hcoeff : (0 : ℝ) < ((dCoeff k m n : ℤ) : ℝ)/(n : ℝ)^(k-1) := by
    rw [source_coefficient_expansion k m n hm hmk, Int.cast_sub, sub_div]
    linarith
  have hreal : (0 : ℝ) ≤ ((dCoeff k m n : ℤ) : ℝ) :=
    le_of_lt ((div_pos_iff_of_pos_right (pow_pos hnR _)).mp hcoeff)
  exact_mod_cast hreal

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive
