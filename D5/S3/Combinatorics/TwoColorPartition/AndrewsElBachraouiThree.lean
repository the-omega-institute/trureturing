/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiThree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiThree
   mirror-E: none(waiver:external-partition-conjecture)
   anchors: [mathlib/module/Mathlib.Tactic.Abel]
   utility: none
   digest: Heine transformation and triangular counting prove Conjecture Three. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiHeine
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiLambert
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiThree

open PowerSeries AndrewsElBachraouiDefs AndrewsElBachraouiHeine
open AndrewsElBachraouiLambert AndrewsElBachraouiBounds
open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks the finite coefficient blocks and the q-series reductions.
/-- Andrews and El Bachraoui's Conjecture Three: every D'(2,2,n) is nonnegative. -/
theorem result : AndrewsElBachraouiDefs.conjectureThree := by
  classical
  have hC (n : ℕ) : cCoeff 2 2 n =
      coeff n (X ^ 2 * geom 1 ^ 2 -
        ∑ r ∈ Finset.range (n + 1), X ^ (3 * r + 4) * geom (2 * r + 3)) := by
    classical
    have hheine {R : Type} [CommRing R] (q : R) (N : ℕ) (hN : 0 < N) (hq : q ^ N = 0) :
        (∑ j ∈ Finset.range N, q ^ (4 * j + 2) *
          ∏ i ∈ Finset.range N,
            (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 4 + 2 * i)) *
              Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2) =
        ∑ r ∈ Finset.range N, q ^ (r + 2) * (1 - q ^ (2 * r + 2)) *
          Ring.inverse (1 - q) * Ring.inverse (1 - q ^ (2 * r + 3)) := by
      classical
      have hunit (e : ℕ) (he : 0 < e) : IsUnit (1 - q ^ e) := by
        apply IsNilpotent.isUnit_one_sub
        refine ⟨N, ?_⟩
        rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
      let E (i : ℕ) : Rˣ := (hunit (2 * i + 2) (by omega)).unit
      let O (i : ℕ) : Rˣ := (hunit (2 * i + 1) (by omega)).unit
      have hE (i : ℕ) : (E i : R) = 1 - q ^ (2 * i + 2) :=
        (hunit (2 * i + 2) (by omega)).unit_spec
      have hO (i : ℕ) : (O i : R) = 1 - q ^ (2 * i + 1) :=
        (hunit (2 * i + 1) (by omega)).unit_spec
      have hqzero (e : ℕ) (he : N ≤ e) : q ^ e = 0 := by
        rw [show e = N + (e - N) by omega, pow_add, hq, zero_mul]
      have hlargeE (i : ℕ) (hi : N ≤ i) : E i = 1 := by
        apply Units.ext
        change (E i : R) = 1
        rw [hE, hqzero _ (by omega), sub_zero]
      have hlargeO (i : ℕ) (hi : N ≤ i) : O i = 1 := by
        apply Units.ext
        change (O i : R) = 1
        rw [hO, hqzero _ (by omega), sub_zero]
      let pre (f : ℕ → Rˣ) (j : ℕ) := ∏ i ∈ Finset.range j, f i
      let tail (f : ℕ → Rˣ) (j : ℕ) := ∏ i ∈ Finset.range N, f (j + i)
      have htail (f : ℕ → Rˣ) (hf : ∀ i, N ≤ i → f i = 1) (j : ℕ) :
          tail f j = pre f N * (pre f j)⁻¹ := by
        induction j with
        | zero => simp [tail, pre]
        | succ j ih =>
            have hfirst := Finset.prod_range_succ' (fun i => f (j + i)) N
            have hlast := Finset.prod_range_succ (fun i => f (j + i)) N
            rw [hf _ (by omega), mul_one] at hlast
            rw [hlast] at hfirst
            have hstep : tail f j = tail f (j + 1) * f j := by
              have heq : (fun i => f (j + (i + 1))) = (fun i => f (j + 1 + i)) := by
                funext i
                congr 1
                omega
              rw [heq] at hfirst
              simpa only [tail, Nat.add_zero] using hfirst
            have hp : pre f (j + 1) = pre f j * f j := Finset.prod_range_succ _ _
            rw [hp]
            apply mul_right_cancel (b := f j)
            rw [← hstep, ih]
            apply Additive.ofMul.injective
            simp only [ofMul_mul, ofMul_inv]
            abel
      let A (r : ℕ) := pre O r * (pre E r)⁻¹
      let B (r : ℕ) := (∏ i ∈ Finset.range r, O (i + 1)) * (pre E r)⁻¹
      let P (j : ℕ) := tail E j * (tail O j)⁻¹
      let K := pre E N * (pre O N)⁻¹
      have hP (j : ℕ) : P j = K * A j := by
        dsimp only [P, K, A]
        rw [htail E hlargeE, htail O hlargeO]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      have hbase : (q ^ 2) ^ N = 0 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by decide)]
      have harg (e : ℕ) (he : 0 < e) : (q ^ e) ^ N = 0 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
      have hfirst (j : ℕ) :
          ((tail E (j + 1) * (tail O j)⁻¹ : Rˣ) : R) =
            ∑ r ∈ Finset.range N, q ^ ((2 * j + 1) * r) * (B r : R) := by
        have hb := nilpotent_q_binomial (q ^ 3) (q ^ 2) (q ^ (2 * j + 1)) N
          hbase (harg _ (by omega))
        have hprod : ((tail E (j + 1) * (tail O j)⁻¹ : Rˣ) : R) =
            ∏ i ∈ Finset.range N, (1 - q ^ (2 * (j + 1 + i) + 2)) *
              Ring.inverse (1 - q ^ (2 * (j + i) + 1)) := by
          dsimp only [tail]
          rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
          simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
        rw [hprod]
        have hB (r : ℕ) : (B r : R) =
            ∏ i ∈ Finset.range r, (1 - q ^ (2 * (i + 1) + 1)) *
              Ring.inverse (1 - q ^ (2 * i + 2)) := by
          dsimp only [B, pre]
          rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
          simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
        simp_rw [hB]
        simp only [← pow_mul, ← pow_add] at hb
        have hi1 (i : ℕ) : 2 * (j + 1 + i) + 2 = 3 + (2 * j + 1) + 2 * i := by omega
        have hi2 (i : ℕ) : 2 * (j + i) + 1 = (2 * j + 1) + 2 * i := by omega
        have hi3 (i : ℕ) : 2 * (i + 1) + 1 = 3 + 2 * i := by omega
        have hi4 (i : ℕ) : 2 * i + 2 = 2 * (i + 1) := by omega
        simp_rw [hi1, hi2, hi3, hi4]
        exact hb
      have hsecond (r : ℕ) :
          (∑ j ∈ Finset.range N, q ^ ((2 * r + 4) * j) * (A j : R)) =
            ((tail O (r + 2) * (tail E (r + 1))⁻¹ : Rˣ) : R) := by
        have hb := nilpotent_q_binomial (q ^ 1) (q ^ 2) (q ^ (2 * r + 4)) N
          hbase (harg _ (by omega))
        have hprod : ((tail O (r + 2) * (tail E (r + 1))⁻¹ : Rˣ) : R) =
            ∏ i ∈ Finset.range N, (1 - q ^ (2 * (r + 2 + i) + 1)) *
              Ring.inverse (1 - q ^ (2 * (r + 1 + i) + 2)) := by
          dsimp only [tail]
          rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
          simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
        rw [hprod]
        have hA (j : ℕ) : (A j : R) =
            ∏ i ∈ Finset.range j, (1 - q ^ (2 * i + 1)) *
              Ring.inverse (1 - q ^ (2 * i + 2)) := by
          dsimp only [A, pre]
          rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
          simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
        simp_rw [hA]
        simp only [← pow_mul, ← pow_add] at hb
        have hi1 (i : ℕ) : 2 * (r + 2 + i) + 1 = 1 + (2 * r + 4) + 2 * i := by omega
        have hi2 (i : ℕ) : 2 * (r + 1 + i) + 2 = (2 * r + 4) + 2 * i := by omega
        have hi3 (i : ℕ) : 2 * i + 1 = 1 + 2 * i := by omega
        have hi4 (i : ℕ) : 2 * i + 2 = 2 * (i + 1) := by omega
        simp_rw [hi1, hi2, hi3, hi4]
        exact hb.symm
      have hcollapse (r : ℕ) :
          K * B r * tail O (r + 2) * (tail E (r + 1))⁻¹ =
            E r * (O 0)⁻¹ * (O (r + 1))⁻¹ := by
        dsimp only [K, B]
        rw [htail O hlargeO, htail E hlargeE]
        have hOshift : (∏ i ∈ Finset.range r, O (i + 1)) * O 0 = pre O (r + 1) := by
          exact (Finset.prod_range_succ' O r).symm
        have hOstep : pre O (r + 2) = pre O (r + 1) * O (r + 1) :=
          Finset.prod_range_succ _ _
        have hEstep : pre E (r + 1) = pre E r * E r := Finset.prod_range_succ _ _
        rw [hOstep, hEstep]
        have hOshift' : (∏ i ∈ Finset.range r, O (i + 1)) =
            pre O (r + 1) * (O 0)⁻¹ := by
          rw [← hOshift]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [hOshift']
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      have hprod (j : ℕ) :
          (∏ i ∈ Finset.range N,
            (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 4 + 2 * i)) *
              Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2) =
          (P j : R) * ((tail E (j + 1) * (tail O j)⁻¹ : Rˣ) : R) := by
        have hp : P j * (tail E (j + 1) * (tail O j)⁻¹) =
            ∏ i ∈ Finset.range N, E (j + i) * E (j + 1 + i) * ((O (j + i))⁻¹) ^ 2 := by
          dsimp only [P, tail]
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow, Finset.prod_inv_distrib, pow_two]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [← Units.val_mul, hp, Units.coe_prod]
        apply Finset.prod_congr rfl
        intro i _
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← Ring.inverse_unit, hE, hO]
        rw [show 2 * (j + i) + 2 = 2 * j + 2 + 2 * i by omega,
          show 2 * (j + 1 + i) + 2 = 2 * j + 4 + 2 * i by omega,
          show 2 * (j + i) + 1 = 2 * j + 1 + 2 * i by omega]
      calc
        _ = ∑ j ∈ Finset.range N, q ^ (4 * j + 2) * (K : R) * (A j : R) *
            (∑ r ∈ Finset.range N, q ^ ((2 * j + 1) * r) * (B r : R)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hprod, hfirst, hP, Units.val_mul]
          ring
        _ = ∑ r ∈ Finset.range N, q ^ (r + 2) * (K : R) * (B r : R) *
            (∑ j ∈ Finset.range N, q ^ ((2 * r + 4) * j) * (A j : R)) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro j _
          have hexp : 4 * j + 2 + (2 * j + 1) * r = r + 2 + (2 * r + 4) * j := by
            ring
          calc
            _ = q ^ (4 * j + 2 + (2 * j + 1) * r) * (K : R) * (A j : R) *
                (B r : R) := by rw [pow_add]; ring
            _ = _ := by rw [hexp, pow_add]; ring
        _ = ∑ r ∈ Finset.range N, q ^ (r + 2) *
            ((E r * (O 0)⁻¹ * (O (r + 1))⁻¹ : Rˣ) : R) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hsecond]
          have hc := congrArg (fun u : Rˣ => (u : R)) (hcollapse r)
          simp only [Units.val_mul] at hc
          calc
            _ = q ^ (r + 2) *
                ((K : R) * (B r : R) * (tail O (r + 2) : R) *
                  (((tail E (r + 1))⁻¹ : Rˣ) : R)) := by
                    simp only [Units.val_mul]
                    ring
            _ = _ := by rw [hc]; simp only [Units.val_mul]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r _
          simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
          simp only [Nat.mul_zero, zero_add, pow_one,
            show 2 * (r + 1) + 1 = 2 * r + 3 by omega]
          ring
    have hgeom (e : ℕ) (he : 0 < e) : geom e * (1 - X ^ e) = 1 := by
      apply PowerSeries.ext
      intro t
      rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
      simp only [geom, coeff_mk]
      by_cases het : e ≤ t
      · rw [if_pos het]
        have hdvd : e ∣ t - e ↔ e ∣ t := by
          constructor
          · intro h
            have := dvd_add h (dvd_refl e)
            simpa [Nat.sub_add_cancel het] using this
          · intro h
            exact Nat.dvd_sub h (dvd_refl e)
        have ht : t ≠ 0 := by omega
        simp [hdvd, coeff_one, ht]
      · rw [if_neg het]
        by_cases ht : t = 0
        · simp [ht]
        · have hnot : ¬ e ∣ t := by
            intro h
            have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht) h
            omega
          simp [hnot, coeff_one, ht]
    let I := Ideal.span {(X ^ (n + 1) : PowerSeries ℤ)}
    let F := Ideal.Quotient.mk I
    let q := F X
    have hq : q ^ (n + 1) = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hinv (e : ℕ) (he : 0 < e) : F (geom e) = Ring.inverse (1 - q ^ e) := by
      have hmul := congrArg F (hgeom e he)
      simp only [map_mul, map_sub, map_one, map_pow] at hmul
      have hu : IsUnit (1 - F X ^ e) := by
        exact isUnit_iff_exists_inv.mpr ⟨F (geom e), by simpa [mul_comm] using hmul⟩
      apply hu.mul_right_cancel
      rw [Ring.inverse_mul_cancel _ hu]
      exact hmul
    have hfg : F (cTrunc 2 2 n) =
        F (∑ r ∈ Finset.range (n + 1), X ^ (r + 2) * (1 - X ^ (2 * r + 2)) *
          geom 1 * geom (2 * r + 3)) := by
      simp only [cTrunc, map_sum, map_mul, map_pow, map_prod, map_sub, map_one]
      have hh := hheine q (n + 1) (by omega) hq
      calc
        _ = ∑ j ∈ Finset.range (n + 1), q ^ (4 * j + 2) *
            ∏ i ∈ Finset.range (n + 1),
              (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 4 + 2 * i)) *
                Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show 2 * (2 * j + 1) = 4 * j + 2 by omega]
          congr 1
          apply Finset.prod_congr rfl
          intro i _
          rw [hinv _ (by omega)]
        _ = _ := by
          rw [hh]
          apply Finset.sum_congr rfl
          intro r _
          rw [hinv 1 (by omega), hinv _ (by omega)]
          simp only [pow_one]
          rfl
    have hmem := Ideal.Quotient.eq.mp hfg
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hmem
    have hc := congrArg (coeff n) hp
    rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at hc
    have htrans : cCoeff 2 2 n =
        coeff n (∑ r ∈ Finset.range (n + 1), X ^ (r + 2) * (1 - X ^ (2 * r + 2)) *
      geom 1 * geom (2 * r + 3)) := sub_eq_zero.mp hc
    have hpf {R : Type} [CommRing R] (q : R) (N : ℕ) (hq : q ^ N = 0) :
        (∑ r ∈ Finset.range N, q ^ (r + 2) * (1 - q ^ (2 * r + 2)) *
          Ring.inverse (1 - q) * Ring.inverse (1 - q ^ (2 * r + 3))) =
        q ^ 2 * Ring.inverse (1 - q) ^ 2 -
          ∑ r ∈ Finset.range N, q ^ (3 * r + 4) * Ring.inverse (1 - q ^ (2 * r + 3)) := by
      classical
      have hunit (e : ℕ) (he : 0 < e) : IsUnit (1 - q ^ e) := by
        apply IsNilpotent.isUnit_one_sub
        refine ⟨N, ?_⟩
        rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
      have h1 : (1 - q) * Ring.inverse (1 - q) = 1 :=
        Ring.mul_inverse_cancel _ (by simpa using hunit 1 (by decide))
      have hterm (r : ℕ) : q ^ (r + 2) * (1 - q ^ (2 * r + 2)) *
          Ring.inverse (1 - q) * Ring.inverse (1 - q ^ (2 * r + 3)) =
          q ^ (r + 2) * Ring.inverse (1 - q) -
            q ^ (3 * r + 4) * Ring.inverse (1 - q ^ (2 * r + 3)) := by
        have ho := Ring.mul_inverse_cancel _ (hunit (2 * r + 3) (by omega))
        have hn : 1 - q ^ (2 * r + 2) =
            (1 - q ^ (2 * r + 3)) - q ^ (2 * r + 2) * (1 - q) := by
          rw [show 2 * r + 3 = (2 * r + 2) + 1 by omega, pow_succ q (2 * r + 2)]
          ring
        rw [hn]
        calc
          _ = q ^ (r + 2) * Ring.inverse (1 - q) *
                ((1 - q ^ (2 * r + 3)) * Ring.inverse (1 - q ^ (2 * r + 3))) -
              q ^ ((r + 2) + (2 * r + 2)) *
                ((1 - q) * Ring.inverse (1 - q)) *
                Ring.inverse (1 - q ^ (2 * r + 3)) := by rw [pow_add]; ring
          _ = _ := by rw [ho, h1, show r + 2 + (2 * r + 2) = 3 * r + 4 by omega]; ring
      have hsum : (∑ r ∈ Finset.range N, q ^ r) = Ring.inverse (1 - q) := by
        apply (by simpa using hunit 1 (by decide) : IsUnit (1 - q)).mul_left_cancel
        rw [h1]
        have hgeo := mul_geom_sum q N
        rw [hq] at hgeo
        linear_combination -hgeo
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib]
      congr 1
      calc
        _ = q ^ 2 * Ring.inverse (1 - q) * (∑ r ∈ Finset.range N, q ^ r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [pow_add]
          ring
        _ = _ := by rw [hsum]; ring
    have hfg2 :
        F (∑ r ∈ Finset.range (n + 1), X ^ (r + 2) * (1 - X ^ (2 * r + 2)) *
          geom 1 * geom (2 * r + 3)) =
        F (X ^ 2 * geom 1 ^ 2 -
          ∑ r ∈ Finset.range (n + 1), X ^ (3 * r + 4) * geom (2 * r + 3)) := by
      simp only [map_sum, map_mul, map_pow, map_sub, map_one]
      rw [hinv 1 (by omega)]
      simp_rw [show ∀ r, F (geom (2 * r + 3)) =
        Ring.inverse (1 - q ^ (2 * r + 3)) from fun r => hinv _ (by omega)]
      simpa only [pow_one] using hpf q (n + 1) hq
    have hmem2 := Ideal.Quotient.eq.mp hfg2
    obtain ⟨p2, hp2⟩ := Ideal.mem_span_singleton.mp hmem2
    have hc2 := congrArg (coeff n) hp2
    rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at hc2
    exact htrans.trans (sub_eq_zero.mp hc2)
  have hshift (n : ℕ) :
      cCoeff 2 2 (n + 2) = dCoeff 2 2 n +
        coeff n (∏ i ∈ Finset.range (n + 1),
          ((1 - X ^ (2 + 2 * i)) * (1 - X ^ (4 + 2 * i)) * geom (1 + 2 * i) ^ 2)) := by
    classical
    have hgeom (e : ℕ) (he : 0 < e) : geom e * (1 - X ^ e) = 1 := by
      apply PowerSeries.ext
      intro t
      rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
      simp only [geom, coeff_mk]
      by_cases het : e ≤ t
      · rw [if_pos het]
        have hdvd : e ∣ t - e ↔ e ∣ t := by
          constructor
          · intro h
            have := dvd_add h (dvd_refl e)
            simpa [Nat.sub_add_cancel het] using this
          · intro h
            exact Nat.dvd_sub h (dvd_refl e)
        have ht : t ≠ 0 := by omega
        simp [hdvd, coeff_one, ht]
      · rw [if_neg het]
        by_cases ht : t = 0
        · simp [ht]
        · have hnot : ¬ e ∣ t := by
            intro h
            have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht) h
            omega
          simp [hnot, coeff_one, ht]
    have hremove (P : PowerSeries ℤ) (e t : ℕ) (het : t < e) :
        coeff t (P * geom e) = coeff t P := by
      have h := congrArg (coeff t) (congrArg (P * ·) (hgeom e (by omega)))
      rw [← mul_assoc, mul_sub, mul_one, map_sub, coeff_mul_X_pow',
        if_neg (by omega), sub_zero, mul_one] at h
      exact h
    have hfactor (P : PowerSeries ℤ) (a b e t : ℕ)
        (ha : t < a) (hb : t < b) (he : t < e) :
        coeff t (P * ((1 - X ^ a) * (1 - X ^ b) * geom e ^ 2)) = coeff t P := by
      rw [pow_two, ← mul_assoc, ← mul_assoc, ← mul_assoc, hremove _ e t he,
        hremove _ e t he, mul_sub, mul_one, map_sub, coeff_mul_X_pow',
        if_neg (by omega), sub_zero, mul_sub, mul_one, map_sub, coeff_mul_X_pow',
        if_neg (by omega), sub_zero]
    have hproduct (j B : ℕ) (hnB : n ≤ B) (t : ℕ) (ht : t ≤ n) :
        coeff t (∏ i ∈ Finset.range (B + 1),
          ((1 - X ^ (2 * j + 4 + 2 * i)) * (1 - X ^ (2 * j + 6 + 2 * i)) *
            geom (2 * j + 3 + 2 * i) ^ 2)) =
        coeff t (∏ i ∈ Finset.range (n + 1),
          ((1 - X ^ (2 * j + 4 + 2 * i)) * (1 - X ^ (2 * j + 6 + 2 * i)) *
            geom (2 * j + 3 + 2 * i) ^ 2)) := by
      induction B, hnB using Nat.le_induction with
      | base => rfl
      | succ B hnB ih =>
          rw [Finset.prod_range_succ, hfactor _ _ _ _ t (by omega) (by omega) (by omega)]
          exact ih
    have hstable : coeff n (dTrunc 2 2 (n + 2)) = dCoeff 2 2 n := by
      unfold dCoeff dTrunc
      rw [map_sum, map_sum]
      simp only [Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
      trans ∑ j ∈ Finset.range (n + 3), coeff n
        (X ^ (2 * (2 * j + 2)) * ∏ i ∈ Finset.range (n + 1),
          ((1 - X ^ (2 * j + 4 + 2 * i)) * (1 - X ^ (2 * j + 6 + 2 * i)) *
            geom (2 * j + 3 + 2 * i) ^ 2))
      · simp only [Nat.add_assoc]
        apply Finset.sum_congr rfl
        intro j _
        rw [coeff_X_pow_mul', coeff_X_pow_mul']
        split_ifs with hshift
        · simpa only [Nat.add_assoc, Nat.reduceAdd] using
            hproduct j (n + 2) (by omega) (n - 2 * (2 * j + 2)) (by omega)
        · rfl
      · simp only [Nat.add_assoc]
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hjN
        have : n + 1 ≤ j := by simpa using hjN
        rw [coeff_X_pow_mul', if_neg (by omega)]
    let P (j : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range (n + 3),
      ((1 - X ^ (2 * j + 2 + 2 * i)) * (1 - X ^ (2 * j + 4 + 2 * i)) *
        geom (2 * j + 1 + 2 * i) ^ 2)
    have hterm (j : ℕ) :
        coeff (n + 2) (X ^ (2 * (2 * j + 1)) * P j) =
          coeff n (X ^ (4 * j) * P j) := by
      rw [show 2 * (2 * j + 1) = 4 * j + 2 by omega, pow_add, mul_right_comm, coeff_mul_X_pow]
    have hsucc (j : ℕ) : X ^ (4 * (j + 1)) * P (j + 1) =
        X ^ (2 * (2 * j + 2)) * ∏ i ∈ Finset.range (n + 3),
          ((1 - X ^ (2 * j + 4 + 2 * i)) * (1 - X ^ (2 * j + 6 + 2 * i)) *
            geom (2 * j + 3 + 2 * i) ^ 2) := by
      dsimp [P]
      congr 1
      · congr 1; omega
    have hprod0 (B : ℕ) (hB : n ≤ B) :
        coeff n (∏ i ∈ Finset.range (B + 1),
          ((1 - X ^ (2 + 2 * i)) * (1 - X ^ (4 + 2 * i)) * geom (1 + 2 * i) ^ 2)) =
        coeff n (∏ i ∈ Finset.range (n + 1),
          ((1 - X ^ (2 + 2 * i)) * (1 - X ^ (4 + 2 * i)) * geom (1 + 2 * i) ^ 2)) := by
      induction B, hB using Nat.le_induction with
      | base => rfl
      | succ B hB ih =>
          rw [Finset.prod_range_succ, hfactor _ _ _ _ n (by omega) (by omega) (by omega)]
          exact ih
    have hP0 : coeff n (P 0) = coeff n (∏ i ∈ Finset.range (n + 1),
        ((1 - X ^ (2 + 2 * i)) * (1 - X ^ (4 + 2 * i)) * geom (1 + 2 * i) ^ 2)) := by
      simpa only [P, Nat.mul_zero, Nat.zero_add] using hprod0 (n + 2) (by omega)
    have hdterm : coeff n (X ^ (4 * (n + 3)) * P (n + 3)) = 0 := by
      rw [coeff_X_pow_mul', if_neg (by omega)]
    unfold cCoeff cTrunc
    change coeff (n + 2) (∑ j ∈ Finset.range (n + 3), X ^ (2 * (2 * j + 1)) * P j) = _
    rw [map_sum]
    simp_rw [hterm]
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, one_mul]
    change (∑ j ∈ Finset.range (n + 2), coeff n (X ^ (4 * (j + 1)) * P (j + 1))) +
      coeff n (P 0) = _
    have hadd := Finset.sum_range_succ
      (fun j => coeff n (X ^ (4 * (j + 1)) * P (j + 1))) (n + 2)
    rw [hdterm, add_zero] at hadd
    rw [← hadd]
    simp_rw [hsucc]
    have hd := hstable
    unfold dTrunc at hd
    rw [map_sum] at hd
    rw [← hP0]
    simpa only [P, Nat.mul_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
      using congrArg (· + coeff n (P 0)) hd
  have hcc (n : ℕ) :
      cCoeff 2 2 (n + 2) = (n : ℤ) + 3 - ((2 * n + 5).divisors.card : ℤ) := by
    classical
    have hc := hC (n + 2)
    rw [hc, map_sub, coeff_X_pow_mul]
    have hgeom : coeff n (geom 1 ^ 2) = (n : ℤ) + 1 := by
      simp [pow_two, coeff_mul, geom, coeff_mk]
    rw [hgeom, map_sum]
    have hterm (j : ℕ) : coeff (n + 2) (X ^ (3 * j + 4) * geom (2 * j + 3)) =
        coeff n (X ^ (3 * j + 2) * geom (2 * j + 3)) := by
      rw [show 3 * j + 4 = (3 * j + 2) + 2 by omega, pow_add,
        mul_right_comm, coeff_mul_X_pow]
    simp_rw [hterm]
    have hpad : (∑ j ∈ Finset.range (n + 3),
        coeff n (X ^ (3 * j + 2) * geom (2 * j + 3))) =
        ∑ j ∈ Finset.range (n + 1),
          coeff n (X ^ (3 * j + 2) * geom (2 * j + 3)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hout
      have : n + 1 ≤ j := by simpa using hout
      rw [coeff_X_pow_mul', if_neg (by omega)]
    rw [hpad]
    have hl := lambert_divisor_coefficient n
    rw [map_sum] at hl
    omega
  have hlarge (n : ℕ) (hn : 172 ≤ n) (p : ℤ)
      (hp : (p : ℝ) ≤ 97 / 120 * (n : ℝ) +
        27 / 32 * Real.sqrt (2 * (n : ℝ) + 1 / 2) + 13 / 25) :
      (p : ℝ) + ((2 * n + 5).divisors.card : ℝ) ≤ (n : ℝ) + 3 := by
    have hnR : (172 : ℝ) ≤ n := by exact_mod_cast hn
    have htN := odd_divisors_card_le (2 * n + 5) (by exact ⟨n + 2, by omega⟩)
    have htR : ((2 * n + 5).divisors.card : ℝ) ≤ Real.sqrt (2 * (n : ℝ) + 5) + 1 := by
      have hcast : ((2 * n + 5).divisors.card : ℝ) ≤ (Nat.sqrt (2 * n + 5) : ℝ) + 1 := by
        exact_mod_cast htN
      have hsqrt := Real.nat_sqrt_le_real_sqrt (a := 2 * n + 5)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hsqrt
      linarith
    have hsqrt : Real.sqrt (2 * (n : ℝ) + 1 / 2) ≤ Real.sqrt (2 * (n : ℝ) + 5) :=
      Real.sqrt_le_sqrt (by linarith)
    let R := Real.sqrt (2 * (n : ℝ) + 5)
    have hRpos : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R ^ 2 = 2 * (n : ℝ) + 5 := Real.sq_sqrt (by positivity)
    have hpoly : (59 / 32 : ℝ) ^ 2 * (2 * (n : ℝ) + 5) ≤
        (23 / 120 * (n : ℝ) + 37 / 25) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 172)]
    have hthresh : (59 / 32 : ℝ) * R ≤ 23 / 120 * (n : ℝ) + 37 / 25 := by
      nlinarith
    dsimp [R] at hthresh
    nlinarith
  have hcounter (n : ℕ) (hn : n < 172) :
      ((range (n + 1)).product (range (n + 1))).filter (fun p =>
        (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
        ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2) =
      ((range 19).product (range 19)).filter (fun p =>
        (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
        ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2) := by
    have hsmall (a : ℕ) (ha : (a + 1).choose 2 ≤ n) : a < 19 := by
      by_contra h
      have hchoose := Nat.choose_le_choose 2 (show 20 ≤ a + 1 by omega)
      have h20 : (20 : ℕ).choose 2 = 190 := by decide
      rw [h20] at hchoose
      omega
    have hlower (a : ℕ) : a ≤ (a + 1).choose 2 := by
      induction a with
      | zero => simp
      | succ a ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; omega
    ext p
    simp only [mem_filter, product_eq_sprod, mem_product, mem_range]
    constructor
    · intro h
      exact ⟨⟨hsmall p.1 (by omega), hsmall p.2 (by omega)⟩, h.2⟩
    · intro h
      have ha := hlower p.1
      have hb := hlower p.2
      exact ⟨⟨by omega, by omega⟩, h.2⟩
  have hfinite0 : ∀ n : ℕ, n ∈ Finset.range 50 →
      (0 : ℤ) ≤ (n : ℤ) + 3 -
        ((((Finset.range 19).product (Finset.range 19)).filter fun p =>
            (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
            ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2).card : ℤ) -
          ((2 * n + 5).divisors.card : ℤ) := by decide
  have hfinite1 : ∀ n : ℕ, n ∈ Finset.Ico 50 100 →
      (0 : ℤ) ≤ (n : ℤ) + 3 -
        ((((Finset.range 19).product (Finset.range 19)).filter fun p =>
            (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
            ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2).card : ℤ) -
          ((2 * n + 5).divisors.card : ℤ) := by decide
  have hfinite2 : ∀ n : ℕ, n ∈ Finset.Ico 100 150 →
      (0 : ℤ) ≤ (n : ℤ) + 3 -
        ((((Finset.range 19).product (Finset.range 19)).filter fun p =>
            (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
            ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2).card : ℤ) -
          ((2 * n + 5).divisors.card : ℤ) := by decide
  have hfinite3 : ∀ n : ℕ, n ∈ Finset.Ico 150 172 →
      (0 : ℤ) ≤ (n : ℤ) + 3 -
        ((((Finset.range 19).product (Finset.range 19)).filter fun p =>
            (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
            ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2).card : ℤ) -
          ((2 * n + 5).divisors.card : ℤ) := by decide
  intro n
  let P : PowerSeries ℤ := ∏ i ∈ Finset.range (n + 1),
    ((1 - X ^ (2 + 2 * i)) * (1 - X ^ (4 + 2 * i)) * geom (1 + 2 * i) ^ 2)
  have hc := hcc n
  have hs := hshift n
  have hd : dCoeff 2 2 n = (n : ℤ) + 3 - coeff n P -
      ((2 * n + 5).divisors.card : ℤ) := by
    change cCoeff 2 2 (n + 2) = dCoeff 2 2 n + coeff n P at hs
    omega
  by_cases hn : 172 ≤ n
  · have hp := (gauss_product_coefficient_count_bound n).2 (by omega)
    have hhigh := hlarge n hn (coeff n P) hp
    have hdR : (dCoeff 2 2 n : ℝ) = (n : ℝ) + 3 - ((coeff n P : ℤ) : ℝ) -
        ((2 * n + 5).divisors.card : ℝ) := by exact_mod_cast hd
    have : (0 : ℝ) ≤ dCoeff 2 2 n := by linarith
    exact_mod_cast this
  · have hnlt : n < 172 := by omega
    have hp := (gauss_product_coefficient_count_bound n).1
    change coeff n P = ((((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
      (fun p => (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
        ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2)).card : ℤ) at hp
    rw [hcounter n hnlt] at hp
    have hf : (0 : ℤ) ≤ (n : ℤ) + 3 -
        ((((Finset.range 19).product (Finset.range 19)).filter fun p =>
            (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
            ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2).card : ℤ) -
          ((2 * n + 5).divisors.card : ℤ) := by
      by_cases h50 : n < 50
      · exact hfinite0 n (Finset.mem_range.mpr h50)
      · by_cases h100 : n < 100
        · exact hfinite1 n (Finset.mem_Ico.mpr ⟨by omega, h100⟩)
        · by_cases h150 : n < 150
          · exact hfinite2 n (Finset.mem_Ico.mpr ⟨by omega, h150⟩)
          · exact hfinite3 n (Finset.mem_Ico.mpr ⟨by omega, hnlt⟩)
    rw [hd, hp]
    exact hf

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiThree
