/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour
   mirror-E: none(waiver:external-partition-conjecture)
   anchors: [mathlib/module/Mathlib.Tactic.Abel]
   utility: none
   digest: Heine reduction and a signed hyperbola bound prove Conjecture Four. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiHeine
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiCharacter
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFour

open PowerSeries Finset AndrewsElBachraouiDefs AndrewsElBachraouiHeine
open AndrewsElBachraouiBounds AndrewsElBachraouiCharacter

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel computes the finite coefficient blocks and nilpotent q-series reductions.
/-- Andrews and El Bachraoui's Conjecture Four has exactly two negative coefficients. -/
theorem result : AndrewsElBachraouiDefs.conjectureFour := by
  classical
  have hgeom (e : ℕ) (he : 0 < e) : geom e * (1 - X ^ e) = 1 := by
    apply PowerSeries.ext; intro t
    rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']; simp only [geom, coeff_mk]
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
  have hcc (n : ℕ) : cCoeff 2 3 (n+3) =
    (n : ℤ)+5+(if 2 ∣ n then 1 else 0)-((2*n+9).divisors.card : ℤ)-
      2*∑ i ∈ Finset.range (n+3), (-1 : ℤ)^(n+2-i)*((2*i+1).divisors.card : ℤ) := by
    have hH3 (n : ℕ) : cCoeff 2 3 n =
      coeff (n + 1) ((1 + X + X ^ 2 - X ^ 3) * geom 1 * geom 2 -
        (1 + X + 2 * X ^ 2) * ((1 - X) * geom 2) *
          (∑ j ∈ Finset.range (n + 2), X ^ j * geom (2 * j + 1))) := by
      classical
      have hC (n : ℕ) : cCoeff 2 3 n =
          coeff n (∑ r ∈ Finset.range (n + 1),
            X ^ (r + 3) * (1 - X ^ (2 * r + 2)) * (1 - X ^ (2 * r + 4)) *
            geom 1 * geom (2 * r + 3) * geom (2 * r + 5)) := by
        classical
        have hheine {R : Type} [CommRing R] (q : R) (N : ℕ) (hN : 0 < N) (hq : q ^ N = 0) :
            (∑ j ∈ Finset.range N, q ^ (6 * j + 3) *
              ∏ i ∈ Finset.range N,
                (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 4 + 2 * i)) *
                  Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2) =
            ∑ r ∈ Finset.range N, q ^ (r + 3) * (1 - q ^ (2 * r + 2)) * (1 - q ^ (2 * r + 4)) *
              Ring.inverse (1 - q) * Ring.inverse (1 - q ^ (2 * r + 3)) *
              Ring.inverse (1 - q ^ (2 * r + 5)) := by
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
                rw [hf _ (by omega), mul_one] at hlast; rw [hlast] at hfirst
                have hstep : tail f j = tail f (j + 1) * f j := by
                  have heq : (fun i => f (j + (i + 1))) = (fun i => f (j + 1 + i)) := by
                    funext i
                    congr 1
                    omega
                  rw [heq] at hfirst
                  simpa only [tail, Nat.add_zero] using hfirst
                have hp : pre f (j + 1) = pre f j * f j := Finset.prod_range_succ _ _
                rw [hp]; apply mul_right_cancel (b := f j)
                rw [← hstep, ih]; apply Additive.ofMul.injective
                simp only [ofMul_mul, ofMul_inv]
                abel
          let A (r : ℕ) := pre O r * (pre E r)⁻¹
          let B (r : ℕ) := (∏ i ∈ Finset.range r, O (i + 1)) * (pre E r)⁻¹
          let P (j : ℕ) := tail E j * (tail O j)⁻¹
          let K := pre E N * (pre O N)⁻¹
          have hP (j : ℕ) : P j = K * A j := by
            dsimp only [P, K, A]
            rw [htail E hlargeE, htail O hlargeO]; apply Additive.ofMul.injective
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
              (∑ j ∈ Finset.range N, q ^ ((2 * r + 6) * j) * (A j : R)) =
                ((tail O (r + 3) * (tail E (r + 2))⁻¹ : Rˣ) : R) := by
            have hb := nilpotent_q_binomial (q ^ 1) (q ^ 2) (q ^ (2 * r + 6)) N
              hbase (harg _ (by omega))
            have hprod : ((tail O (r + 3) * (tail E (r + 2))⁻¹ : Rˣ) : R) =
                ∏ i ∈ Finset.range N, (1 - q ^ (2 * (r + 3 + i) + 1)) *
                  Ring.inverse (1 - q ^ (2 * (r + 2 + i) + 2)) := by
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
            have hi1 (i : ℕ) : 2 * (r + 3 + i) + 1 = 1 + (2 * r + 6) + 2 * i := by omega
            have hi2 (i : ℕ) : 2 * (r + 2 + i) + 2 = (2 * r + 6) + 2 * i := by omega
            have hi3 (i : ℕ) : 2 * i + 1 = 1 + 2 * i := by omega
            have hi4 (i : ℕ) : 2 * i + 2 = 2 * (i + 1) := by omega
            simp_rw [hi1, hi2, hi3, hi4]
            exact hb.symm
          have hcollapse (r : ℕ) :
              K * B r * tail O (r + 3) * (tail E (r + 2))⁻¹ =
                E r * E (r + 1) * (O 0)⁻¹ * (O (r + 1))⁻¹ * (O (r + 2))⁻¹ := by
            dsimp only [K, B]
            rw [htail O hlargeO, htail E hlargeE]
            have hOshift : (∏ i ∈ Finset.range r, O (i + 1)) * O 0 = pre O (r + 1) := by
              exact (Finset.prod_range_succ' O r).symm
            have hpre (f : ℕ → Rˣ) (s : ℕ) : pre f (s + 1) = pre f s * f s :=
              Finset.prod_range_succ _ _
            have hOstep : pre O (r + 3) = pre O (r + 1) * O (r + 1) * O (r + 2) := by
              rw [show r + 3 = (r + 2) + 1 by omega, hpre]
              rw [show r + 2 = (r + 1) + 1 by omega, hpre]
            have hEstep : pre E (r + 2) = pre E r * E r * E (r + 1) := by
              rw [show r + 2 = (r + 1) + 1 by omega, hpre, hpre]
            rw [hOstep, hEstep]
            have hOshift' : (∏ i ∈ Finset.range r, O (i + 1)) =
                pre O (r + 1) * (O 0)⁻¹ := by
              rw [← hOshift]; apply Additive.ofMul.injective
              simp only [ofMul_mul, ofMul_inv]
              abel
            rw [hOshift']; apply Additive.ofMul.injective
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
              apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]
              abel
            rw [← Units.val_mul, hp, Units.coe_prod]; apply Finset.prod_congr rfl
            intro i _
            simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← Ring.inverse_unit, hE, hO]
            rw [show 2 * (j + i) + 2 = 2 * j + 2 + 2 * i by omega,
              show 2 * (j + 1 + i) + 2 = 2 * j + 4 + 2 * i by omega,
              show 2 * (j + i) + 1 = 2 * j + 1 + 2 * i by omega]
          calc
            _ = ∑ j ∈ Finset.range N, q ^ (6 * j + 3) * (K : R) * (A j : R) *
                (∑ r ∈ Finset.range N, q ^ ((2 * j + 1) * r) * (B r : R)) := by
              apply Finset.sum_congr rfl; intro j _
              rw [hprod, hfirst, hP, Units.val_mul]; ring
            _ = ∑ r ∈ Finset.range N, q ^ (r + 3) * (K : R) * (B r : R) *
                (∑ j ∈ Finset.range N, q ^ ((2 * r + 6) * j) * (A j : R)) := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]; apply Finset.sum_congr rfl
              intro r _; apply Finset.sum_congr rfl
              intro j _
              have hexp : 6 * j + 3 + (2 * j + 1) * r = r + 3 + (2 * r + 6) * j := by
                ring
              calc
                _ = q ^ (6 * j + 3 + (2 * j + 1) * r) * (K : R) * (A j : R) *
                    (B r : R) := by rw [pow_add]; ring
                _ = _ := by rw [hexp, pow_add]; ring
            _ = ∑ r ∈ Finset.range N, q ^ (r + 3) *
                ((E r * E (r + 1) * (O 0)⁻¹ * (O (r + 1))⁻¹ * (O (r + 2))⁻¹ : Rˣ) : R) := by
              apply Finset.sum_congr rfl; intro r _
              rw [hsecond]
              have hc := congrArg (fun u : Rˣ => (u : R)) (hcollapse r)
              simp only [Units.val_mul] at hc
              calc
                _ = q ^ (r + 3) *
                    ((K : R) * (B r : R) * (tail O (r + 3) : R) *
                      (((tail E (r + 2))⁻¹ : Rˣ) : R)) := by
                        simp only [Units.val_mul]; ring
                _ = _ := by rw [hc]; simp only [Units.val_mul]
            _ = _ := by
              apply Finset.sum_congr rfl; intro r _
              simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
              simp only [Nat.mul_zero, zero_add, pow_one,
                show 2 * (r + 1) + 1 = 2 * r + 3 by omega,
                show 2 * (r + 2) + 1 = 2 * r + 5 by omega,
                show 2 * (r + 1) + 2 = 2 * r + 4 by omega]
              ring
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
          apply hu.mul_right_cancel; rw [Ring.inverse_mul_cancel _ hu]
          exact hmul
        have hfg : F (cTrunc 2 3 n) =
            F (∑ r ∈ Finset.range (n + 1),
              X ^ (r + 3) * (1 - X ^ (2 * r + 2)) * (1 - X ^ (2 * r + 4)) *
              geom 1 * geom (2 * r + 3) * geom (2 * r + 5)) := by
          simp only [cTrunc, map_sum, map_mul, map_pow, map_prod, map_sub, map_one]
          have hh := hheine q (n + 1) (by omega) hq
          calc
            _ = ∑ j ∈ Finset.range (n + 1), q ^ (6 * j + 3) *
                ∏ i ∈ Finset.range (n + 1),
                  (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 4 + 2 * i)) *
                    Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2 := by
              apply Finset.sum_congr rfl; intro j _
              rw [show 3 * (2 * j + 1) = 6 * j + 3 by omega]
              congr 1
              apply Finset.prod_congr rfl; intro i _
              rw [hinv _ (by omega)]
            _ = _ := by
              rw [hh]; apply Finset.sum_congr rfl
              intro r _; rw [hinv 1 (by omega), hinv _ (by omega), hinv _ (by omega)]
              simp only [pow_one]; rfl
        have hmem := Ideal.Quotient.eq.mp hfg
        obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hmem
        have hc := congrArg (coeff n) hp
        rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at hc; exact (sub_eq_zero.mp hc)
      have hpf {R : Type} [CommRing R] (q : R) (N : ℕ) (hq : q ^ N = 0) :
          (∑ r ∈ Finset.range N, q ^ (r + 4) * (1 - q ^ (2 * r + 2)) *
            (1 - q ^ (2 * r + 4)) * Ring.inverse (1 - q) *
            Ring.inverse (1 - q ^ (2 * r + 3)) * Ring.inverse (1 - q ^ (2 * r + 5))) =
          (1 + q + q ^ 2 - q ^ 3) * Ring.inverse (1 - q) * Ring.inverse (1 - q ^ 2) -
            (1 + q + 2 * q ^ 2) * Ring.inverse (1 + q) *
              (∑ j ∈ Finset.range N, q ^ j * Ring.inverse (1 - q ^ (2 * j + 1))) := by
        classical
        have hterm {R : Type} [CommRing R] (q x : R) (h1 : IsUnit (1 - q))
            (hp : IsUnit (1 + q)) (hA : IsUnit (1 - q ^ 2 * x))
            (hB : IsUnit (1 - q ^ 4 * x)) :
            q ^ 4 * (1 - q * x) * (1 - q ^ 3 * x) * Ring.inverse (1 - q) *
                Ring.inverse (1 - q ^ 2 * x) * Ring.inverse (1 - q ^ 4 * x) =
              q ^ 2 * Ring.inverse (1 - q) -
                q ^ 3 * Ring.inverse (1 + q) * Ring.inverse (1 - q ^ 2 * x) -
                q ^ 2 * (1 + q + q ^ 2) * Ring.inverse (1 + q) *
                  Ring.inverse (1 - q ^ 4 * x) := by
          apply ((h1.mul hp).mul (hA.mul hB)).mul_left_cancel
          have hi1 := Ring.mul_inverse_cancel _ h1
          have hip := Ring.mul_inverse_cancel _ hp
          have hiA := Ring.mul_inverse_cancel _ hA
          have hiB := Ring.mul_inverse_cancel _ hB
          calc
            _ = q ^ 4 * (1 - q * x) * (1 - q ^ 3 * x) * (1 + q) *
                ((1 - q) * Ring.inverse (1 - q)) *
                ((1 - q ^ 2 * x) * Ring.inverse (1 - q ^ 2 * x)) *
                ((1 - q ^ 4 * x) * Ring.inverse (1 - q ^ 4 * x)) := by ring
            _ = q ^ 4 * (1 - q * x) * (1 - q ^ 3 * x) * (1 + q) := by
              rw [hi1, hiA, hiB]; ring
            _ = q ^ 2 * (1 + q) * (1 - q ^ 2 * x) * (1 - q ^ 4 * x) -
                q ^ 3 * (1 - q) * (1 - q ^ 4 * x) -
                q ^ 2 * (1 + q + q ^ 2) * (1 - q) * (1 - q ^ 2 * x) := by ring
            _ = q ^ 2 * (1 + q) * (1 - q ^ 2 * x) * (1 - q ^ 4 * x) *
                  ((1 - q) * Ring.inverse (1 - q)) -
                q ^ 3 * (1 - q) * (1 - q ^ 4 * x) *
                  ((1 + q) * Ring.inverse (1 + q)) *
                  ((1 - q ^ 2 * x) * Ring.inverse (1 - q ^ 2 * x)) -
                q ^ 2 * (1 + q + q ^ 2) * (1 - q) * (1 - q ^ 2 * x) *
                  ((1 + q) * Ring.inverse (1 + q)) *
                  ((1 - q ^ 4 * x) * Ring.inverse (1 - q ^ 4 * x)) := by
              rw [hi1, hip, hiA, hiB]; ring
            _ = _ := by ring
        have hunit (e : ℕ) (he : 0 < e) : IsUnit (1 - q ^ e) := by
          apply IsNilpotent.isUnit_one_sub
          refine ⟨N, ?_⟩
          rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
        have hu : IsUnit (1 - q) := by simpa using hunit 1 (by decide)
        have hv : IsUnit (1 + q) := by
          simpa only [neg_neg, sub_neg_eq_add] using
            (IsNilpotent.isUnit_one_sub (IsNilpotent.neg ⟨N, hq⟩))
        let u := Ring.inverse (1 - q)
        let v := Ring.inverse (1 + q)
        let T := ∑ j ∈ Finset.range N, q ^ j * Ring.inverse (1 - q ^ (2 * j + 1))
        let L (s : ℕ) := ∑ j ∈ Finset.range N,
          q ^ j * Ring.inverse (1 - q ^ (2 * j + 2 * s + 1))
        have hiu : (1 - q) * u = 1 := Ring.mul_inverse_cancel _ hu
        have hiv : (1 + q) * v = 1 := Ring.mul_inverse_cancel _ hv
        have hs (s : ℕ) : q ^ s * L s = q ^ s * Ring.inverse (1 - q ^ (2 * s + 1)) +
            q ^ (s + 1) * L (s + 1) := by
          let f (j : ℕ) := q ^ (j + s) * Ring.inverse (1 - q ^ (2 * (j + s) + 1))
          have hfirst := Finset.sum_range_succ' f N
          have hlast := Finset.sum_range_succ f N
          have hend : f N = 0 := by simp [f, pow_add, hq]
          rw [hend, add_zero] at hlast; rw [hlast] at hfirst
          dsimp only [L]
          rw [Finset.mul_sum, Finset.mul_sum]
          have hleft : (∑ j ∈ Finset.range N, q ^ s *
              (q ^ j * Ring.inverse (1 - q ^ (2 * j + 2 * s + 1)))) =
              ∑ j ∈ Finset.range N, f j := by
            apply Finset.sum_congr rfl; intro j _
            dsimp [f]; rw [pow_add]
            rw [show 2 * (j + s) + 1 = 2 * j + 2 * s + 1 by omega]
            ring
          rw [hleft, hfirst]
          dsimp only [f]
          rw [Nat.zero_add]; rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl; intro j _
          rw [show j + 1 + s = j + (s + 1) by omega, pow_add]
          rw [show 2 * (j + (s + 1)) + 1 = 2 * j + 2 * (s + 1) + 1 by omega]
          ring
        have hs1 : q * L 1 = T - u := by
          have h := hs 0
          have h0 : L 0 = T := by simp only [L, T, Nat.mul_zero, Nat.add_zero]
          simp only [pow_zero, one_mul, pow_one, Nat.zero_add, Nat.mul_zero] at h; rw [h0] at h
          change T = u + q * L 1 at h
          linear_combination -h
        have hs2 : q ^ 2 * L 2 = T - u - q * Ring.inverse (1 - q ^ 3) := by
          have h := hs 1
          simp only [pow_one] at h; rw [hs1] at h
          linear_combination -h
        have hsum : (∑ r ∈ Finset.range N, q ^ r) = u := by
          apply hu.mul_left_cancel; rw [hiu]
          have hgeo := mul_geom_sum q N
          rw [hq] at hgeo
          linear_combination -hgeo
        have hrewrite (r : ℕ) :
            q ^ (r + 4) * (1 - q ^ (2 * r + 2)) * (1 - q ^ (2 * r + 4)) * u *
              Ring.inverse (1 - q ^ (2 * r + 3)) * Ring.inverse (1 - q ^ (2 * r + 5)) =
            q ^ r * (q ^ 2 * u - q ^ 3 * v * Ring.inverse (1 - q ^ (2 * r + 3)) -
              q ^ 2 * (1 + q + q ^ 2) * v * Ring.inverse (1 - q ^ (2 * r + 5))) := by
          have h := hterm q (q ^ (2 * r + 1)) hu hv
            (by rw [← pow_add, show 2 + (2 * r + 1) = 2 * r + 3 by omega]
                exact hunit _ (by omega))
            (by rw [← pow_add, show 4 + (2 * r + 1) = 2 * r + 5 by omega]
                exact hunit _ (by omega))
          have hi (a : ℕ) : q ^ a * q ^ (2 * r + 1) = q ^ (2 * r + a + 1) := by
            rw [← pow_add, show a + (2 * r + 1) = 2 * r + a + 1 by omega]
          have hi1 : q * q ^ (2 * r + 1) = q ^ (2 * r + 2) := by
            rw [← pow_succ', show 2 * r + 1 + 1 = 2 * r + 2 by omega]
          simp_rw [hi, hi1] at h
          rw [pow_add q r 4]
          simpa only [u, v, mul_assoc] using congrArg (q ^ r * ·) h
        have hS : (1 + q + q ^ 2) * Ring.inverse (1 - q ^ 3) = u := by
          apply hu.mul_left_cancel; rw [hiu]
          calc
            _ = ((1 - q) * (1 + q + q ^ 2)) * Ring.inverse (1 - q ^ 3) := by ring
            _ = (1 - q ^ 3) * Ring.inverse (1 - q ^ 3) := by congr 1; ring
            _ = 1 := Ring.mul_inverse_cancel _ (hunit 3 (by decide))
        have htwo : Ring.inverse (1 - q ^ 2) = u * v := by
          apply (hunit 2 (by decide)).mul_left_cancel
          rw [Ring.mul_inverse_cancel _ (hunit 2 (by decide))]
          symm
          calc
            _ = ((1 - q) * u) * ((1 + q) * v) := by ring
            _ = 1 := by rw [hiu, hiv]; ring
        have hrem : q ^ 2 * u ^ 2 + v * (1 + q + 2 * q ^ 2) * u +
            v * q * (1 + q + q ^ 2) * Ring.inverse (1 - q ^ 3) =
            (1 + q + q ^ 2 - q ^ 3) * u * Ring.inverse (1 - q ^ 2) := by
          rw [show v * q * (1 + q + q ^ 2) * Ring.inverse (1 - q ^ 3) =
              v * q * ((1 + q + q ^ 2) * Ring.inverse (1 - q ^ 3)) by ring, hS, htwo]
          calc
            _ = q ^ 2 * u ^ 2 * ((1 + q) * v) +
                v * (1 + 2 * q + 2 * q ^ 2) * u * ((1 - q) * u) := by
              rw [hiu, hiv]; ring
            _ = _ := by ring
        change (∑ r ∈ Finset.range N, q ^ (r + 4) * (1 - q ^ (2 * r + 2)) *
          (1 - q ^ (2 * r + 4)) * u * Ring.inverse (1 - q ^ (2 * r + 3)) *
            Ring.inverse (1 - q ^ (2 * r + 5))) =
          (1 + q + q ^ 2 - q ^ 3) * u * Ring.inverse (1 - q ^ 2) -
            (1 + q + 2 * q ^ 2) * v * T
        simp_rw [hrewrite]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        have hx : (∑ r ∈ Finset.range N, q ^ r * (q ^ 2 * u)) = q ^ 2 * u ^ 2 := by
          rw [← Finset.sum_mul, hsum]; ring
        have hy : (∑ r ∈ Finset.range N,
            q ^ r * (q ^ 3 * v * Ring.inverse (1 - q ^ (2 * r + 3)))) =
            v * q ^ 2 * (q * L 1) := by
          dsimp only [L]
          simp only [Finset.mul_sum, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd]
          apply Finset.sum_congr rfl; intro r _
          ring
        have hz : (∑ r ∈ Finset.range N,
            q ^ r * (q ^ 2 * (1 + q + q ^ 2) * v * Ring.inverse (1 - q ^ (2 * r + 5)))) =
            v * (1 + q + q ^ 2) * (q ^ 2 * L 2) := by
          dsimp only [L]
          simp only [Finset.mul_sum, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd]
          apply Finset.sum_congr rfl; intro r _
          ring
        rw [hx, hy, hz, hs1, hs2]
        change _ = (1 + q + q ^ 2 - q ^ 3) * u * Ring.inverse (1 - q ^ 2) -
          (1 + q + 2 * q ^ 2) * v * T
        rw [← hrem]; ring
      let F := Ideal.Quotient.mk (Ideal.span {(X ^ (n + 2) : PowerSeries ℤ)})
      let q := F X
      have hq : q ^ (n + 2) = 0 := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span (Set.mem_singleton _)
      have hinv (e : ℕ) (he : 0 < e) : F (geom e) = Ring.inverse (1 - q ^ e) := by
        have hmul := congrArg F (hgeom e he)
        simp only [map_mul, map_sub, map_one, map_pow] at hmul
        have hu : IsUnit (1 - q ^ e) := by
          exact isUnit_iff_exists_inv.mpr ⟨F (geom e), by simpa [q, mul_comm] using hmul⟩
        apply hu.mul_right_cancel; rw [Ring.inverse_mul_cancel _ hu]
        exact hmul
      have hplus : ((1 - X) * geom 2) * (1 + X) = 1 := by
        calc
          _ = geom 2 * (1 - X ^ 2) := by ring
          _ = 1 := hgeom 2 (by decide)
      have hinvp : F ((1 - X) * geom 2) = Ring.inverse (1 + q) := by
        have hm := congrArg F hplus
        simp only [map_mul, map_add, map_one] at hm
        have hu : IsUnit (1 + q) :=
          isUnit_iff_exists_inv.mpr ⟨F ((1 - X) * geom 2), by simpa [q, mul_comm] using hm⟩
        apply hu.mul_right_cancel; rw [Ring.inverse_mul_cancel _ hu]
        exact hm
      let S : PowerSeries ℤ := ∑ r ∈ Finset.range (n + 2),
        X ^ (r + 4) * (1 - X ^ (2 * r + 2)) * (1 - X ^ (2 * r + 4)) *
          geom 1 * geom (2 * r + 3) * geom (2 * r + 5)
      let R : PowerSeries ℤ := (1 + X + X ^ 2 - X ^ 3) * geom 1 * geom 2 -
        (1 + X + 2 * X ^ 2) * ((1 - X) * geom 2) *
          (∑ j ∈ Finset.range (n + 2), X ^ j * geom (2 * j + 1))
      have hfg : F S = F R := by
        dsimp only [S, R]
        rw [map_sub, map_mul, map_mul, map_mul, map_mul, hinvp]
        simp only [map_sum, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]
        rw [hinv 1 (by omega), hinv 2 (by omega)]
        simp_rw [show ∀ r, F (geom (2 * r + 3)) =
          Ring.inverse (1 - q ^ (2 * r + 3)) from fun r => hinv _ (by omega),
          show ∀ r, F (geom (2 * r + 5)) =
            Ring.inverse (1 - q ^ (2 * r + 5)) from fun r => hinv _ (by omega),
          show ∀ j, F (geom (2 * j + 1)) =
            Ring.inverse (1 - q ^ (2 * j + 1)) from fun j => hinv _ (by omega)]
        simpa only [q, pow_one] using hpf q (n + 2) hq
      have hlow : coeff (n + 1) S = coeff (n + 1) R := by
        have hmem := Ideal.Quotient.eq.mp hfg
        obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hmem
        have hc := congrArg (coeff (n + 1)) hp
        rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at hc; exact sub_eq_zero.mp hc
      have hleft : coeff (n + 1) S = cCoeff 2 3 n := by
        dsimp only [S]
        rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ, map_add]
        have hlast : coeff (n + 1)
            (X ^ (n + 1 + 4) * (1 - X ^ (2 * (n + 1) + 2)) *
              (1 - X ^ (2 * (n + 1) + 4)) * geom 1 * geom (2 * (n + 1) + 3) *
              geom (2 * (n + 1) + 5)) = 0 := by
          simp only [mul_assoc]; rw [coeff_X_pow_mul', if_neg (by omega)]
        rw [hlast, add_zero, hC, map_sum, map_sum]; apply Finset.sum_congr rfl
        intro r _
        have hterm : X ^ (r + 4) * (1 - X ^ (2 * r + 2)) * (1 - X ^ (2 * r + 4)) *
            geom 1 * geom (2 * r + 3) * geom (2 * r + 5) =
          X * (X ^ (r + 3) * (1 - X ^ (2 * r + 2)) * (1 - X ^ (2 * r + 4)) *
            geom 1 * geom (2 * r + 3) * geom (2 * r + 5)) := by
          rw [show r + 4 = (r + 3) + 1 by omega, pow_add, pow_one]
          ring
        rw [hterm, coeff_succ_X_mul]
      exact hleft.symm.trans hlow
    have hP (n : ℕ) :
      coeff (n + 4) ((1 + X + X ^ 2 - X ^ 3) * geom 1 * geom 2) =
        (n : ℤ) + 5 + if 2 ∣ n then 1 else 0 := by
      have hu : IsUnit (1 - X : PowerSeries ℤ) :=
        isUnit_iff_exists_inv.mpr ⟨geom 1, by simpa [mul_comm] using hgeom 1 (by decide)⟩
      have hrel : (1 + X) * geom 2 = geom 1 := by
        apply hu.mul_left_cancel
        calc
          _ = geom 2 * (1 - X ^ 2) := by ring
          _ = 1 := hgeom 2 (by decide)
          _ = (1 - X) * geom 1 := by simpa [mul_comm] using (hgeom 1 (by decide)).symm
      have hpoly : (1 + X + X ^ 2 - X ^ 3) * geom 1 * geom 2 =
          geom 1 ^ 2 + X ^ 2 * geom 2 := by
        calc
          _ = geom 1 * ((1 + X) * geom 2) + X ^ 2 * (geom 1 * (1 - X)) * geom 2 := by
            ring
          _ = _ := by rw [hrel, show geom 1 * (1 - X) = 1 by simpa using hgeom 1 (by decide)]; ring
      rw [hpoly, map_add, coeff_X_pow_mul', if_pos (by omega)]; rw [show n + 4 - 2 = n + 2 by omega]
      have hgg : coeff (n + 4) (geom 1 ^ 2) = (n : ℤ) + 5 := by
        simp [pow_two, coeff_mul, geom, coeff_mk]
        omega
      rw [hgg]; simp only [geom, coeff_mk]
      have hd : 2 ∣ n + 2 ↔ 2 ∣ n := by omega
      simp only [hd]
    have hConv (n : ℕ) :
      coeff (n+4) ((1+X+2*X^2) * ((1-X)*geom 2) *
        (∑ j ∈ Finset.range (n+5), X^j*geom (2*j+1))) =
        ((2*n+9).divisors.card : ℤ) +
          2 * ∑ i ∈ Finset.range (n+3),
            (-1 : ℤ)^(n+2-i) * ((2*i+1).divisors.card : ℤ) := by
      classical
      have hAlt (d : ℕ) : coeff d ((1 - X) * geom 2) = (-1 : ℤ) ^ d := by
        rw [sub_mul, one_mul, map_sub]
        cases d with
        | zero => simp [geom, coeff_mk]
        | succ d =>
            rw [coeff_succ_X_mul]; rw [neg_one_pow_eq_pow_mod_two]
            simp only [geom, coeff_mk]
            rcases (show d % 2 = 0 ∨ d % 2 = 1 by omega) with h | h
            · have hs : (d + 1) % 2 = 1 := by omega
              simp [Nat.dvd_iff_mod_eq_zero, h, hs]
            · have hs : (d + 1) % 2 = 0 := by omega
              simp [Nat.dvd_iff_mod_eq_zero, h, hs]
      have hT (n N : ℕ) (hn : n≤N) :
        coeff n (∑ j ∈ Finset.range (N+1),
          (X^j*geom (2*j+1) : PowerSeries ℤ)) = ((2*n+1).divisors.card : ℤ) := by
        classical
        have hpad : (∑ j ∈ range (N+1), coeff n (X^j*geom (2*j+1))) =
            ∑ j ∈ range (n+1), coeff n (X^j*geom (2*j+1)) := by
          symm
          apply sum_subset (range_mono (by omega))
          intro j _ hout
          have hlarge : n < j := by simpa using hout
          rw [coeff_X_pow_mul', if_neg (by omega)]
        rw [map_sum, hpad, ← map_sum]
        rcases n with _ | _ | n
        · simp [geom, coeff_mk]
        · simp [sum_range_succ, geom, coeff_mk]
          decide
        have hterm (j : ℕ) : X^(j+1)*geom (2*j+3) =
            X^(j+1)+X^2*(X^(3*j+2)*geom (2*j+3)) := by
          have hg : geom (2*j+3) = 1 + X^(2*j+3)*geom (2*j+3) := by
            have hh := hgeom (2*j+3) (by omega)
            calc
              _ = (geom (2*j+3)*(1-X^(2*j+3)))+X^(2*j+3)*geom (2*j+3) := by ring
              _ = _ := by rw [hh]
          rw [hg, mul_add, mul_one]
          congr 1
          rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
          congr 1
          congr 1
          omega
        have hmono : coeff (n+2) (∑ j ∈ range (n+2), (X^(j+1) : PowerSeries ℤ)) = 1 := by
          rw [map_sum]
          rw [sum_eq_single (n+1)]
          · simp
          · intro b hb hne
            have hb' := mem_range.mp hb
            simp [coeff_X_pow, show n+2 ≠ b+1 by omega]
          · intro h
            exact False.elim (h (mem_range.mpr (by omega)))
        have hshort : coeff n (∑ j ∈ range (n+2),
            (X^(3*j+2)*geom (2*j+3) : PowerSeries ℤ)) =
            coeff n (∑ j ∈ range (n+1), (X^(3*j+2)*geom (2*j+3) : PowerSeries ℤ)) := by
          rw [show n+2=(n+1)+1 by omega, sum_range_succ, map_add,
            coeff_X_pow_mul', if_neg (by omega), add_zero]
        rw [show n+1+1+1 = (n+2)+1 by omega, sum_range_succ']
        simp only [Nat.mul_zero, pow_zero, one_mul, Nat.zero_add]
        have hsum : (∑ j ∈ range (n+2), X^(j+1)*geom (2*(j+1)+1)) =
            (∑ j ∈ range (n+2), X^(j+1))+
            X^2*(∑ j ∈ range (n+2), X^(3*j+2)*geom (2*j+3)) := by
          simp_rw [show ∀ j : ℕ, 2*(j+1)+1=2*j+3 by intro j; omega, hterm]
          rw [sum_add_distrib, mul_sum]
        rw [hsum, map_add, map_add, hmono, coeff_X_pow_mul', if_pos (by omega)]
        simp only [show n+1+1-2=n by omega]
        rw [show coeff (n+1+1) (geom 1) = 1 by simp [geom, coeff_mk]]
        rw [hshort]
        have h := AndrewsElBachraouiLambert.lambert_divisor_coefficient n
        simp only [show 2*(n+1+1)+1=2*n+5 by omega]
        linarith
      let T : PowerSeries ℤ := ∑ j ∈ Finset.range (n+5), X^j*geom (2*j+1)
      let U : PowerSeries ℤ := ((1-X)*geom 2)*T
      have hU (d : ℕ) (hd : d≤n+4) : coeff d U =
          ∑ i ∈ Finset.range (d+1),
            (-1 : ℤ)^(d-i) * ((2*i+1).divisors.card : ℤ) := by
        dsimp [U]; rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl; intro i hi
        have hi : i≤d := by simpa using hi
        rw [show coeff i T = ((2*i+1).divisors.card : ℤ) by
          dsimp [T]; exact hT i (n+4) (by omega), hAlt, mul_comm]
      have hrec : (1+X)*U=T := by
        dsimp [U]
        calc
          _ = (geom 2*(1-X^2))*T := by ring
          _ = T := by rw [hgeom 2 (by decide),one_mul]
      have hd := congrArg (coeff (n+4)) hrec
      rw [add_mul,one_mul,map_add,show n+4=(n+3)+1 by omega,
        coeff_succ_X_mul] at hd
      have hread : coeff (n+4) T = ((2*n+9).divisors.card : ℤ) := by
        dsimp [T]
        simpa only [show 2*(n+4)+1=2*n+9 by omega] using hT (n+4) (n+4) (by rfl)
      have hpoly : (1+X+2*X^2)*((1-X)*geom 2)*T = U+X*U+2*(X^2*U) := by
        dsimp [U]; ring
      rw [hpoly,map_add,map_add,show n+4=(n+3)+1 by omega,coeff_succ_X_mul]
      rw [show 2*(X^2*U)=(2 : ℕ) • (X^2*U) by simp [nsmul_eq_mul],map_nsmul]
      rw [coeff_X_pow_mul',if_pos (by omega),show n+3+1-2=n+2 by omega]
      rw [hU (n+2) (by omega)]; rw [←show n+4=(n+3)+1 by omega] at hd
      rw [hread] at hd
      simp only [nsmul_eq_mul, Nat.cast_ofNat,
        show n+3+1=n+4 by omega, show n+2+1=n+3 by omega] at ⊢
      linarith
    have hc := hH3 (n+3)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hc; rw [hc,map_sub,hP n,hConv n]
    ring
  have hshift (n : ℕ) :
    cCoeff 2 3 (n + 3) = dCoeff 2 3 n +
      coeff n (∏ i ∈ Finset.range (n + 1),
        ((1 - X ^ (2 + 2 * i)) * (1 - X ^ (4 + 2 * i)) * geom (1 + 2 * i) ^ 2)) := by
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
    have hstable : coeff n (dTrunc 2 3 (n + 3)) = dCoeff 2 3 n := by
      unfold dCoeff dTrunc
      rw [map_sum, map_sum]
      simp only [Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
      trans ∑ j ∈ Finset.range (n + 4), coeff n
        (X ^ (3 * (2 * j + 2)) * ∏ i ∈ Finset.range (n + 1),
          ((1 - X ^ (2 * j + 4 + 2 * i)) * (1 - X ^ (2 * j + 6 + 2 * i)) *
            geom (2 * j + 3 + 2 * i) ^ 2))
      · simp only [Nat.add_assoc]
        apply Finset.sum_congr rfl
        intro j _
        rw [coeff_X_pow_mul', coeff_X_pow_mul']
        split_ifs with hshift
        · simpa only [Nat.add_assoc, Nat.reduceAdd] using
            hproduct j (n + 3) (by omega) (n - 3 * (2 * j + 2)) (by omega)
        · rfl
      · simp only [Nat.add_assoc]
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hjN
        have : n + 1 ≤ j := by simpa using hjN
        rw [coeff_X_pow_mul', if_neg (by omega)]
    let P (j : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range (n + 4),
      ((1 - X ^ (2 * j + 2 + 2 * i)) * (1 - X ^ (2 * j + 4 + 2 * i)) *
        geom (2 * j + 1 + 2 * i) ^ 2)
    have hterm (j : ℕ) :
        coeff (n + 3) (X ^ (3 * (2 * j + 1)) * P j) =
          coeff n (X ^ (6 * j) * P j) := by
      rw [show 3 * (2 * j + 1) = 6 * j + 3 by omega, pow_add, mul_right_comm, coeff_mul_X_pow]
    have hsucc (j : ℕ) : X ^ (6 * (j + 1)) * P (j + 1) =
        X ^ (3 * (2 * j + 2)) * ∏ i ∈ Finset.range (n + 4),
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
      simpa only [P, Nat.mul_zero, Nat.zero_add] using hprod0 (n + 3) (by omega)
    have hdterm : coeff n (X ^ (6 * (n + 4)) * P (n + 4)) = 0 := by
      rw [coeff_X_pow_mul', if_neg (by omega)]
    unfold cCoeff cTrunc
    change coeff (n + 3) (∑ j ∈ Finset.range (n + 4), X ^ (3 * (2 * j + 1)) * P j) = _
    rw [map_sum]
    simp_rw [hterm]
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, one_mul]
    change (∑ j ∈ Finset.range (n + 3), coeff n (X ^ (6 * (j + 1)) * P (j + 1))) +
      coeff n (P 0) = _
    have hadd := Finset.sum_range_succ
      (fun j => coeff n (X ^ (6 * (j + 1)) * P (j + 1))) (n + 3)
    rw [hdterm, add_zero] at hadd
    rw [← hadd]
    simp_rw [hsucc]
    have hd := hstable
    unfold dTrunc at hd
    rw [map_sum] at hd
    rw [← hP0]
    simpa only [P, Nat.mul_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
      using congrArg (· + coeff n (P 0)) hd
  have hlarge (n : ℕ) (hn : 419 ≤ n) (p u : ℤ)
    (hp : (p : ℝ) ≤ 97/120*(n : ℝ)+
      27/32*Real.sqrt (2*(n : ℝ)+1/2)+13/25)
    (hu : |u| ≤ (((Nat.sqrt (2*n+5)+1)/2 : ℕ):ℤ)) :
    (p : ℝ)+((2*n+9).divisors.card : ℝ)+2*(u : ℝ) ≤ (n : ℝ)+5 := by
    have hnR : (419 : ℝ) ≤ n := by exact_mod_cast hn
    have htN := odd_divisors_card_le (2*n+9) (by exact ⟨n+4, by omega⟩)
    have htR : ((2*n+9).divisors.card : ℝ) ≤ Real.sqrt (2*(n : ℝ)+9)+1 := by
      have hcast : ((2*n+9).divisors.card : ℝ) ≤ (Nat.sqrt (2*n+9) : ℝ)+1 := by
        exact_mod_cast htN
      have hsqrt := Real.nat_sqrt_le_real_sqrt (a := 2*n+9)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hsqrt
      linarith
    have huR : 2*(u : ℝ) ≤ Real.sqrt (2*(n : ℝ)+5)+1 := by
      have h1 := le_abs_self u
      have h2 := Nat.div_mul_le_self (Nat.sqrt (2*n+5)+1) 2
      have hcast : (2 : ℝ)*(((Nat.sqrt (2*n+5)+1)/2 : ℕ) : ℝ) ≤
          (Nat.sqrt (2*n+5) : ℝ)+1 := by
        exact_mod_cast (by omega : 2*((Nat.sqrt (2*n+5)+1)/2) ≤ Nat.sqrt (2*n+5)+1)
      have hucast : (u : ℝ) ≤ (((Nat.sqrt (2*n+5)+1)/2 : ℕ):ℝ) := by
        have hiInt := h1.trans hu
        simpa only [Int.cast_natCast] using (Int.cast_le (R := ℝ)).mpr hiInt
      have hsqrt := Real.nat_sqrt_le_real_sqrt (a := 2*n+5)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hsqrt
      linarith
    have hsqrt1 : Real.sqrt (2*(n : ℝ)+1/2) ≤ Real.sqrt (2*(n : ℝ)+9) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt2 : Real.sqrt (2*(n : ℝ)+5) ≤ Real.sqrt (2*(n : ℝ)+9) :=
      Real.sqrt_le_sqrt (by linarith)
    let R := Real.sqrt (2*(n : ℝ)+9)
    have hRpos : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R^2 = 2*(n : ℝ)+9 := Real.sq_sqrt (by positivity)
    have hpoly : (91/32 : ℝ)^2*(2*(n : ℝ)+9) ≤
        (23/120*(n : ℝ)+62/25)^2 := by
      nlinarith [sq_nonneg ((n : ℝ)-419)]
    have hthresh : (91/32 : ℝ)*R ≤ 23/120*(n : ℝ)+62/25 := by nlinarith
    dsimp [R] at hthresh
    nlinarith
  have hcounter (n : ℕ) (hn : n < 419) :
    ((range (n + 1)).product (range (n + 1))).filter (fun p =>
      (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
      ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2) =
    ((range 29).product (range 29)).filter (fun p =>
      (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
      ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2) := by
    have hsmall (a : ℕ) (ha : (a + 1).choose 2 ≤ n) : a < 29 := by
      by_contra h
      have hchoose := Nat.choose_le_choose 2 (show 30 ≤ a + 1 by omega)
      have h30 : (30 : ℕ).choose 2 = 435 := by decide
      rw [h30] at hchoose
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
  have hfinite (n : ℕ) (hn : n < 419) :
    ((n : ℤ)+5+(if n%2=0 then 1 else 0) -
      ((((range 29).product (range 29)).filter fun p =>
        ((p.1+1)*p.1/2) + ((p.2+1)*p.2/2) ≤ n ∧
        (((p.1+1)*p.1/2) + ((p.2+1)*p.2/2))%2 = n%2).card : ℤ) -
      ((2*n+9).divisors.card : ℤ) -
      2*(∑ i ∈ range (n+3), (-1 : ℤ)^(n+2-i)*((2*i+1).divisors.card : ℤ)) < 0 ↔
        n=10 ∨ n=22) := by
    let tau := fun m : ℕ => (m.primeFactors.prod (fun p => m.factorization p+1) : ℤ)
    have htau (m : ℕ) (hm : m≠0) : tau m = (m.divisors.card : ℤ) := by
      dsimp [tau]; exact_mod_cast (Nat.card_divisors hm).symm
    let step := fun (s : ℤ) i => tau (2*i+1)-s
    let us := (List.range 422).scanl step 0
    have hfold (k : ℕ) : (List.range k).foldl step 0 =
        ∑ i ∈ range k, (-1 : ℤ)^(k-1-i)*((2*i+1).divisors.card : ℤ) := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [List.range_succ, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          rw [ih, sum_range_succ]
          simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
          dsimp only [step]
          rw [htau (2*k+1) (by omega)]
          have hsum : (∑ i ∈ range k, (-1 : ℤ)^(k-i)*((2*i+1).divisors.card : ℤ)) =
              -(∑ i ∈ range k, (-1 : ℤ)^(k-1-i)*((2*i+1).divisors.card : ℤ)) := by
            rw [← sum_neg_distrib]
            apply sum_congr rfl
            intro i hi
            have hiK := mem_range.mp hi
            rw [show k-i = (k-1-i)+1 by omega, pow_succ]
            ring
          rw [hsum]
          ring
    have hget (k : ℕ) (hk : k < 423) : us[k]'(by simp [us]; omega) =
        ∑ i ∈ range k, (-1 : ℤ)^(k-1-i)*((2*i+1).divisors.card : ℤ) := by
      rw [List.getElem_scanl, List.take_range, Nat.min_eq_left (by omega), hfold]
    let pairs := (List.range 419).zip (us.drop 3)
    let good := fun (p : ℕ × ℤ) =>
        decide (((p.1 : ℤ)+5+(if p.1%2=0 then 1 else 0) -
          ((((range 29).product (range 29)).filter fun t =>
            ((t.1+1)*t.1/2) + ((t.2+1)*t.2/2) ≤ p.1 ∧
            (((t.1+1)*t.1/2) + ((t.2+1)*t.2/2))%2 = p.1%2).card : ℤ) -
          tau (2*p.1+9) - 2*p.2 < 0 ↔
            p.1=10 ∨ p.1=22))
    have cert0 : (pairs.take 50).all good = true := by decide +kernel
    have cert1 : ((pairs.drop 50).take 50).all good = true := by decide +kernel
    have cert2 : ((pairs.drop 100).take 50).all good = true := by decide +kernel
    have cert3 : ((pairs.drop 150).take 50).all good = true := by decide +kernel
    have cert4 : ((pairs.drop 200).take 50).all good = true := by decide +kernel
    have cert5 : ((pairs.drop 250).take 50).all good = true := by decide +kernel
    have cert6 : ((pairs.drop 300).take 50).all good = true := by decide +kernel
    have cert7 : ((pairs.drop 350).take 50).all good = true := by decide +kernel
    have cert8 : (pairs.drop 400).all good = true := by decide +kernel
    have hall (xs : List (ℕ × ℤ)) :
        xs.all good = ((xs.take 50).all good && (xs.drop 50).all good) := by
      rw [← List.all_append, List.take_append_drop]
    have cert : pairs.all good = true := by
      rw [hall, cert0, Bool.true_and]
      rw [hall, cert1, Bool.true_and, List.drop_drop]
      rw [hall, cert2, Bool.true_and, List.drop_drop]
      rw [hall, cert3, Bool.true_and, List.drop_drop]
      rw [hall, cert4, Bool.true_and, List.drop_drop]
      rw [hall, cert5, Bool.true_and, List.drop_drop]
      rw [hall, cert6, Bool.true_and, List.drop_drop]
      rw [hall, cert7, Bool.true_and, List.drop_drop]
      exact cert8
    have hnLen : n < pairs.length := by simp [pairs,us]; omega
    have hmem := List.getElem_mem hnLen
    have hc := List.all_eq_true.mp cert _ hmem
    have hpair : pairs[n]'hnLen = (n, ∑ i ∈ range (n+3),
        (-1 : ℤ)^(n+2-i)*((2*i+1).divisors.card : ℤ)) := by
      simp only [pairs, List.getElem_zip, List.getElem_range, List.getElem_drop]
      rw [hget (3+n) (by omega)]
      simp only [show 3+n = n+3 by omega, show n+3-1 = n+2 by omega]
    rw [hpair] at hc
    dsimp only [good] at hc
    have hread := of_decide_eq_true hc
    rw [htau (2*n+9) (by omega)] at hread
    exact hread
  intro n
  let P : PowerSeries ℤ := ∏ i ∈ range (n+1),
    (1-X^(2+2*i))*(1-X^(4+2*i))*geom (1+2*i)^2
  let u : ℤ := ∑ i ∈ range (n+3), (-1 : ℤ)^(n+2-i)*((2*i+1).divisors.card : ℤ)
  have hc := hcc n
  have hs := hshift n
  change cCoeff 2 3 (n+3) = dCoeff 2 3 n + coeff n P at hs
  have hd : dCoeff 2 3 n = (n : ℤ)+5+(if 2 ∣ n then 1 else 0)-coeff n P-
      ((2*n+9).divisors.card : ℤ)-2*u := by dsimp [u]; linarith
  by_cases hn : 419 ≤ n
  · have hp := (gauss_product_coefficient_count_bound n).2 (by omega)
    have hu := alternating_odd_divisor_sum_bound (n+2)
    change |u| ≤ (((Nat.sqrt (2*(n+2)+1)+1)/2 : ℕ):ℤ) at hu
    rw [show 2*(n+2)+1=2*n+5 by omega] at hu
    have hh := hlarge n hn (coeff n P) u hp hu
    have hdR : (dCoeff 2 3 n : ℝ) = (n : ℝ)+5+
        ((if 2 ∣ n then (1 : ℤ) else 0):ℝ)-((coeff n P : ℤ):ℝ)-
        ((2*n+9).divisors.card : ℝ)-2*(u : ℝ) := by exact_mod_cast hd
    have he : (0 : ℝ) ≤ ((if 2 ∣ n then (1 : ℤ) else 0):ℝ) := by
      split_ifs <;> norm_num
    have hd0 : 0 ≤ dCoeff 2 3 n := by
      have : (0 : ℝ) ≤ dCoeff 2 3 n := by linarith
      exact_mod_cast this
    have hne : ¬(n=10 ∨ n=22) := by omega
    simp [not_lt.mpr hd0, hne]
  · have hnlt : n < 419 := by omega
    have hp := (gauss_product_coefficient_count_bound n).1
    change coeff n P = _ at hp
    have heq := hcounter n hnlt
    simp only [Finset.product_eq_sprod] at heq
    rw [heq] at hp
    simp only [Nat.choose_two_right, Nat.add_sub_cancel] at hp
    have hf := hfinite n hnlt
    rw [hd, hp]
    dsimp [u]
    simpa only [Nat.dvd_iff_mod_eq_zero, Finset.product_eq_sprod] using hf
end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFour
