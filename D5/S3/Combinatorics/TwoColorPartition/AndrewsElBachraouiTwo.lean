/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo
   mirror-E: none(waiver:external-partition-conjecture)
   anchors: [mathlib/module/Mathlib.NumberTheory.AlmostPrime,mathlib/module/Mathlib.Tactic.Abel]
   utility: none
   digest: Heine reduction and signed divisor bounds prove Conjecture Two. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiHeine
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiWeighted
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiTwo

open PowerSeries Finset AndrewsElBachraouiDefs AndrewsElBachraouiHeine
open AndrewsElBachraouiBounds AndrewsElBachraouiCharacter AndrewsElBachraouiWeighted
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Andrews and El Bachraoui's Conjecture Two has nonnegative coefficients. -/
theorem result : AndrewsElBachraouiDefs.conjectureTwo := by
  classical
  have hformula (n : ℕ) : cCoeff 2 4 n =
      (4*((n+2 : ℕ) : ℤ)+9+(-1 : ℤ)^(n+2)*(2*((n+2 : ℕ) : ℤ)-3)+
        2*(-1 : ℤ)^((n+2)/2))/4-
      3*((2*n+1).divisors.card : ℤ)+2*((2*n+3).divisors.card : ℤ)-
      4*((2*n+5).divisors.card : ℤ)-
      (∑ t ∈ Finset.range ((n+2)/2+1),(-1 : ℤ)^t*
        ((2*(n+2-2*t)+1).divisors.card : ℤ))+
      6*(∑ i ∈ Finset.range (n+3),(-1 : ℤ)^(n+2-i)*
        ((2*i+1).divisors.card : ℤ))-
      2*(∑ i ∈ Finset.range (n+3),(-1 : ℤ)^(n+2-i)*
        ((n+2-i : ℕ)+1)*((2*i+1).divisors.card : ℤ)) := by
    classical
    have hgeom (e : ℕ) (he : 0 < e) : geom e * (1 - X ^ e) = 1 := by
      apply PowerSeries.ext; intro t; rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
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
            intro h; have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht) h; omega
          simp [hnot, coeff_one, ht]
    have hpf (q g j k : PowerSeries ℤ)
        (hg : (1-q)*g=1) (hj : (1+q)*j=1) (hk : (1+q^2)*k=1) :
        4*(1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7)*g^2*j^2*k =
          -8*q-4+2*(1+q)*k-5*j+2*j^2+5*g+4*g^2 ∧
        (1+q+q^2)*(1+q+2*q^2+q^3+3*q^4)*j^2*k =
          3*q^2-2*q+4+k-6*j+2*j^2 := by
      have huG : IsUnit (1-q) := isUnit_iff_exists_inv.mpr ⟨g,hg⟩
      have huJ : IsUnit (1+q) := isUnit_iff_exists_inv.mpr ⟨j,hj⟩
      have huK : IsUnit (1+q^2) := isUnit_iff_exists_inv.mpr ⟨k,hk⟩
      constructor
      · let D:=(1-q)^2*(1+q)^2*(1+q^2)
        apply ((huG.pow 2).mul (huJ.pow 2) |>.mul huK).mul_left_cancel
        change D*(4*(1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7)*g^2*j^2*k)=
          D*(-8*q-4+2*(1+q)*k-5*j+2*j^2+5*g+4*g^2)
        calc
          _ = 4*(1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7)*
              ((1-q)*g)^2*((1+q)*j)^2*((1+q^2)*k) := by dsimp [D];ring
          _ = 4*(1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7) := by rw [hg,hj,hk];ring
          _ = (-8*q-4)*D+2*(1+q)*(1-q)^2*(1+q)^2-
              5*(1-q)^2*(1+q)*(1+q^2)+2*(1-q)^2*(1+q^2)+
              5*(1-q)*(1+q)^2*(1+q^2)+4*(1+q)^2*(1+q^2) := by dsimp [D];ring
          _ = (-8*q-4)*D+2*(1+q)*(1-q)^2*(1+q)^2*((1+q^2)*k)-
              5*(1-q)^2*(1+q)*(1+q^2)*((1+q)*j)+
              2*(1-q)^2*(1+q^2)*((1+q)*j)^2+
              5*(1-q)*(1+q)^2*(1+q^2)*((1-q)*g)+
              4*(1+q)^2*(1+q^2)*((1-q)*g)^2 := by rw [hg,hj,hk];ring
          _ = _ := by dsimp [D];ring
      · let W:=(1+q)^2*(1+q^2)
        apply ((huJ.pow 2).mul huK).mul_left_cancel
        change W*((1+q+q^2)*(1+q+2*q^2+q^3+3*q^4)*j^2*k)=
          W*(3*q^2-2*q+4+k-6*j+2*j^2)
        calc
          _ = (1+q+q^2)*(1+q+2*q^2+q^3+3*q^4)*
              ((1+q)*j)^2*((1+q^2)*k) := by dsimp [W];ring
          _ = (1+q+q^2)*(1+q+2*q^2+q^3+3*q^4) := by rw [hj,hk];ring
          _ = (3*q^2-2*q+4)*W+(1+q)^2-6*(1+q)*(1+q^2)+2*(1+q^2) := by
            dsimp [W];ring
          _ = (3*q^2-2*q+4)*W+(1+q)^2*((1+q^2)*k)-
              6*(1+q)*(1+q^2)*((1+q)*j)+2*(1+q^2)*((1+q)*j)^2 := by
            rw [hj,hk];ring
          _ = _ := by dsimp [W];ring
    let G:=geom 1
    let J:=PowerSeries.rescale (-1 : ℤ) G
    let K:=(1-X^2)*geom 4
    have hg : (1-X)*G=1 := by simpa [G,mul_comm] using hgeom 1 (by decide)
    have hj : (1+X)*J=1 := by
      have hh:=congrArg (PowerSeries.rescale (-1 : ℤ)) hg
      simpa [J,map_mul,map_sub,PowerSeries.rescale_X] using hh
    have hk : (1+X^2)*K=1 := by
      calc
        _ = geom 4*(1-X^4) := by dsimp [K];ring
        _ = 1 := hgeom 4 (by decide)
    have hG (d : ℕ) : coeff d G=1 := by simp [G,geom,coeff_mk]
    have hG2 (d : ℕ) : coeff d (G^2)=(d : ℤ)+1 := by
      rw [pow_two,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; simp [hG]
    have hJ (d : ℕ) : coeff d J=(-1 : ℤ)^d := by simp [J,hG]
    have hJ2 (d : ℕ) : coeff d (J^2)=(-1 : ℤ)^d*((d : ℤ)+1) := by
      rw [show J^2=PowerSeries.rescale (-1 : ℤ) (G^2) by simp [J],
        coeff_rescale,hG2]
    have hK (d : ℕ) : coeff d K=if 2∣d then (-1 : ℤ)^(d/2) else 0 := by
      dsimp [K]; rw [sub_mul,one_mul,map_sub,coeff_X_pow_mul']; simp only [geom,coeff_mk]
      rw [neg_one_pow_eq_pow_mod_two]
      by_cases hd : 2≤d
      · have hsub : (d-2)%4=(d%4+2)%4 := by omega
        have hhalf : d/2%2=d%4/2 := by omega
        rw [if_pos hd,hhalf]
        rcases (show d%4=0 ∨ d%4=1 ∨ d%4=2 ∨ d%4=3 by omega) with h|h|h|h <;>
          norm_num [Nat.dvd_iff_mod_eq_zero,hsub,h,show d%2=d%4%2 by omega]
      · rcases (show d=0 ∨ d=1 by omega) with h|h <;> subst d <;> norm_num
    have htrans (n : ℕ) : cCoeff 2 4 n =
        coeff n (∑ r ∈ Finset.range (n + 1), X ^ (r + 4) * (1 - X ^ (2 * r + 2)) * (1 - X ^ (2 *
          r + 4)) * (1 - X ^ (2 * r + 6)) *
          geom 1 * geom (2 * r + 3) * geom (2 * r + 5) * geom (2 * r + 7)) := by
      classical
      have hheine {R : Type} [CommRing R] (q : R) (N : ℕ) (hN : 0 < N) (hq : q ^ N = 0) :
          (∑ j ∈ Finset.range N, q ^ (8 * j + 4) *
            ∏ i ∈ Finset.range N,
              (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 4 + 2 * i)) *
                Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2) =
          ∑ r ∈ Finset.range N, q ^ (r + 4) * (1 - q ^ (2 * r + 2)) * (1 - q ^ (2 * r + 4)) *
            (1 - q ^ (2 * r + 6)) *
            Ring.inverse (1 - q) * Ring.inverse (1 - q ^ (2 * r + 3)) *
            Ring.inverse (1 - q ^ (2 * r + 5)) * Ring.inverse (1 - q ^ (2 * r + 7)) := by
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
          apply Units.ext; change (E i : R) = 1; rw [hE, hqzero _ (by omega), sub_zero]
        have hlargeO (i : ℕ) (hi : N ≤ i) : O i = 1 := by
          apply Units.ext; change (O i : R) = 1; rw [hO, hqzero _ (by omega), sub_zero]
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
              have hp : pre f (j + 1) = pre f j * f j := Finset.prod_range_succ _ _; rw [hp]
              apply mul_right_cancel (b := f j); rw [← hstep, ih]; apply Additive.ofMul.injective
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
          rw [hprod]; have hB (r : ℕ) : (B r : R) =
              ∏ i ∈ Finset.range r, (1 - q ^ (2 * (i + 1) + 1)) *
                Ring.inverse (1 - q ^ (2 * i + 2)) := by
            dsimp only [B, pre]
            rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
            simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
          simp_rw [hB]; simp only [← pow_mul, ← pow_add] at hb
          have hi1 (i : ℕ) : 2 * (j + 1 + i) + 2 = 3 + (2 * j + 1) + 2 * i := by omega
          have hi2 (i : ℕ) : 2 * (j + i) + 1 = (2 * j + 1) + 2 * i := by omega
          have hi3 (i : ℕ) : 2 * (i + 1) + 1 = 3 + 2 * i := by omega
          have hi4 (i : ℕ) : 2 * i + 2 = 2 * (i + 1) := by omega
          simp_rw [hi1, hi2, hi3, hi4]; exact hb
        have hsecond (r : ℕ) :
            (∑ j ∈ Finset.range N, q ^ ((2 * r + 8) * j) * (A j : R)) =
              ((tail O (r + 4) * (tail E (r + 3))⁻¹ : Rˣ) : R) := by
          have hb := nilpotent_q_binomial (q ^ 1) (q ^ 2) (q ^ (2 * r + 8)) N
            hbase (harg _ (by omega))
          have hprod : ((tail O (r + 4) * (tail E (r + 3))⁻¹ : Rˣ) : R) =
              ∏ i ∈ Finset.range N, (1 - q ^ (2 * (r + 4 + i) + 1)) *
                Ring.inverse (1 - q ^ (2 * (r + 3 + i) + 2)) := by
            dsimp only [tail]
            rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
            simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
          rw [hprod]; have hA (j : ℕ) : (A j : R) =
              ∏ i ∈ Finset.range j, (1 - q ^ (2 * i + 1)) *
                Ring.inverse (1 - q ^ (2 * i + 2)) := by
            dsimp only [A, pre]
            rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
            simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
          simp_rw [hA]; simp only [← pow_mul, ← pow_add] at hb
          have hi1 (i : ℕ) : 2 * (r + 4 + i) + 1 = 1 + (2 * r + 8) + 2 * i := by omega
          have hi2 (i : ℕ) : 2 * (r + 3 + i) + 2 = (2 * r + 8) + 2 * i := by omega
          have hi3 (i : ℕ) : 2 * i + 1 = 1 + 2 * i := by omega
          have hi4 (i : ℕ) : 2 * i + 2 = 2 * (i + 1) := by omega
          simp_rw [hi1, hi2, hi3, hi4]; exact hb.symm
        have hcollapse (r : ℕ) :
            K * B r * tail O (r + 4) * (tail E (r + 3))⁻¹ =
              E r * E (r + 1) * E (r + 2) * (O 0)⁻¹ *
                (O (r + 1))⁻¹ * (O (r + 2))⁻¹ * (O (r + 3))⁻¹ := by
          dsimp only [K, B]; rw [htail O hlargeO, htail E hlargeE]
          have hOshift : (∏ i ∈ Finset.range r, O (i + 1)) * O 0 = pre O (r + 1) := by
            exact (Finset.prod_range_succ' O r).symm
          have hpre (f : ℕ → Rˣ) (k : ℕ) : pre f (k+1)=pre f k*f k :=
            Finset.prod_range_succ _ _
          have hOstep : pre O (r + 4) =
              pre O (r + 1) * O (r + 1) * O (r + 2) * O (r + 3) := by
            rw [show r + 4 = (r + 3) + 1 by omega, hpre,
              show r + 3 = (r + 2) + 1 by omega, hpre,
              show r + 2 = (r + 1) + 1 by omega, hpre]
          have hEstep : pre E (r + 3) = pre E r * E r * E (r + 1) * E (r + 2) := by
            rw [show r + 3 = (r + 2) + 1 by omega, hpre,
              show r + 2 = (r + 1) + 1 by omega, hpre,
              hpre]
          rw [hOstep, hEstep]; have hOshift' : (∏ i ∈ Finset.range r, O (i + 1)) =
              pre O (r + 1) * (O 0)⁻¹ := by
            rw [← hOshift]; apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]
            abel
          rw [hOshift']; apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]
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
          rw [← Units.val_mul, hp, Units.coe_prod]; apply Finset.prod_congr rfl; intro i _
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← Ring.inverse_unit, hE, hO]
          rw [show 2 * (j + i) + 2 = 2 * j + 2 + 2 * i by omega,
            show 2 * (j + 1 + i) + 2 = 2 * j + 4 + 2 * i by omega,
            show 2 * (j + i) + 1 = 2 * j + 1 + 2 * i by omega]
        calc
          _ = ∑ j ∈ Finset.range N, q ^ (8 * j + 4) * (K : R) * (A j : R) *
              (∑ r ∈ Finset.range N, q ^ ((2 * j + 1) * r) * (B r : R)) := by
            apply Finset.sum_congr rfl; intro j _; rw [hprod, hfirst, hP, Units.val_mul]; ring
          _ = ∑ r ∈ Finset.range N, q ^ (r + 4) * (K : R) * (B r : R) *
              (∑ j ∈ Finset.range N, q ^ ((2 * r + 8) * j) * (A j : R)) := by
            simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r _
            apply Finset.sum_congr rfl; intro j _
            have hexp : 8 * j + 4 + (2 * j + 1) * r = r + 4 + (2 * r + 8) * j := by
              ring
            calc
              _ = q ^ (8 * j + 4 + (2 * j + 1) * r) * (K : R) * (A j : R) *
                  (B r : R) := by rw [pow_add]; ring
              _ = _ := by rw [hexp, pow_add]; ring
          _ = ∑ r ∈ Finset.range N, q ^ (r + 4) *
              ((E r * E (r + 1) * E (r + 2) * (O 0)⁻¹ *
                (O (r + 1))⁻¹ * (O (r + 2))⁻¹ * (O (r + 3))⁻¹ : Rˣ) : R) := by
            apply Finset.sum_congr rfl; intro r _; rw [hsecond]
            have hc := congrArg (fun u : Rˣ => (u : R)) (hcollapse r)
            simp only [Units.val_mul] at hc
            calc
              _ = q ^ (r + 4) *
                  ((K : R) * (B r : R) * (tail O (r + 4) : R) *
                    (((tail E (r + 3))⁻¹ : Rˣ) : R)) := by
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
        have hmul := congrArg F (hgeom e he); simp only [map_mul, map_sub, map_one, map_pow] at hmul
        have hu : IsUnit (1 - F X ^ e) := by
          exact isUnit_iff_exists_inv.mpr ⟨F (geom e), by simpa [mul_comm] using hmul⟩
        apply hu.mul_right_cancel; rw [Ring.inverse_mul_cancel _ hu]; exact hmul
      have hfg : F (cTrunc 2 4 n) =
          F (∑ r ∈ Finset.range (n + 1), X ^ (r + 4) * (1 - X ^ (2 * r + 2)) * (1 - X ^ (2 *
            r + 4)) * (1 - X ^ (2 * r + 6)) *
            geom 1 * geom (2 * r + 3) * geom (2 * r + 5) * geom (2 * r + 7)) := by
        simp only [cTrunc, map_sum, map_mul, map_pow, map_prod, map_sub, map_one]
        have hh := hheine q (n + 1) (by omega) hq
        calc
          _ = ∑ j ∈ Finset.range (n + 1), q ^ (8 * j + 4) *
              ∏ i ∈ Finset.range (n + 1),
                (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 4 + 2 * i)) *
                  Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2 := by
            apply Finset.sum_congr rfl; intro j _; rw [show 4 * (2 * j + 1) = 8 * j + 4 by omega]
            congr 1
            apply Finset.prod_congr rfl; intro i _; rw [hinv _ (by omega)]
          _ = _ := by
            rw [hh]; apply Finset.sum_congr rfl; intro r _
            rw [hinv 1 (by omega), hinv _ (by omega), hinv _ (by omega), hinv _ (by omega)]
            simp only [pow_one]; rfl
      have hmem := Ideal.Quotient.eq.mp hfg
      obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hmem
      have hc := congrArg (coeff n) hp; rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at hc
      exact (sub_eq_zero.mp hc)
    have hgen (n : ℕ) :
        coeff n (∑ r ∈ Finset.range (n+1), X^(r+4)*(1-X^(2*r+2))*
          (1-X^(2*r+4))*(1-X^(2*r+6))*geom 1*geom (2*r+3)*
            geom (2*r+5)*geom (2*r+7)) =
        coeff (n+2) (
          (1+2*X+3*X^2+2*X^3+3*X^4-X^6-2*X^7)*(geom 1)^2*
            (PowerSeries.rescale (-1 : ℤ) (geom 1))^2*((1-X^2)*geom 4)-
          (1+X+X^2)*(1+X+2*X^2+X^3+3*X^4)*
            (PowerSeries.rescale (-1 : ℤ) (geom 1))^2*((1-X^2)*geom 4)*
            (∑ j ∈ Finset.range (n+3),X^j*geom (2*j+1))) := by
      classical
      have hgf {R : Type} [CommRing R] (q : R) (N : ℕ) (hN : 0<N) (hq : q^N=0) :
          q^2*(∑ r ∈ Finset.range N, q^(r+4)*(1-q^(2*r+2))*(1-q^(2*r+4))*
            (1-q^(2*r+6))*Ring.inverse (1-q)*Ring.inverse (1-q^(2*r+3))*
              Ring.inverse (1-q^(2*r+5))*Ring.inverse (1-q^(2*r+7))) =
          (1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7)*Ring.inverse (1-q)^2*
            Ring.inverse ((1+q)^2*(1+q^2))-
          (1+q+q^2)*(1+q+2*q^2+q^3+3*q^4)*Ring.inverse ((1+q)^2*(1+q^2))*
            (∑ j ∈ Finset.range N, q^j*Ring.inverse (1-q^(2*j+1))) := by
        classical
        have hpf (q : R) (N r : ℕ) (hq : q^N=0) :
            q^(r+6)*(1-q^(2*r+2))*(1-q^(2*r+4))*(1-q^(2*r+6))*
              Ring.inverse (1-q)*Ring.inverse (1-q^(2*r+3))*Ring.inverse (1-q^(2*r+5))*
                Ring.inverse (1-q^(2*r+7)) =
            q^(r+3)*Ring.inverse (1-q) -
              (1+q+q^2)*Ring.inverse ((1+q)^2*(1+q^2))*
                (q^(r+5)*Ring.inverse (1-q^(2*r+3))+
                  q^(r+4)*(1+q^2)*Ring.inverse (1-q^(2*r+5))+
                  q^(r+3)*(1+q+q^2+q^3+q^4)*Ring.inverse (1-q^(2*r+7))) := by
          have hnil (e : ℕ) (he : 0<e) : IsNilpotent (q^e) := by
            refine ⟨N,?_⟩
            rw [←pow_mul,Nat.mul_comm,pow_mul,hq,zero_pow (by omega)]
          have hu (e : ℕ) (he : 0<e) : IsUnit (1-q^e) :=
            (hnil e he).isUnit_one_sub
          have hw : IsUnit ((1+q)^2*(1+q^2)) :=
            (IsNilpotent.isUnit_one_add (by simpa using hnil 1 (by omega))).pow 2 |>.mul
              (IsNilpotent.isUnit_one_add (hnil 2 (by omega)))
          let a:=1-q^(2*r+3)
          let b:=1-q^(2*r+5)
          let c:=1-q^(2*r+7)
          let W:=(1+q)^2*(1+q^2)
          let D:=(1-q)*W*a*b*c
          have hD : IsUnit D := by
            dsimp only [D,a,b,c,W]; have hu1 : IsUnit (1-q) := by simpa using hu 1 (by omega)
            exact hu1.mul hw |>.mul (hu _ (by omega)) |>.mul
              (hu _ (by omega)) |>.mul (hu _ (by omega))
          have hj : (1-q)*Ring.inverse (1-q)=1 := by
            exact Ring.mul_inverse_cancel _ (by simpa using hu 1 (by omega))
          have ha : a*Ring.inverse a=1 := Ring.mul_inverse_cancel _ (hu _ (by omega))
          have hb : b*Ring.inverse b=1 := Ring.mul_inverse_cancel _ (hu _ (by omega))
          have hc : c*Ring.inverse c=1 := Ring.mul_inverse_cancel _ (hu _ (by omega))
          have hW : W*Ring.inverse W=1 := Ring.mul_inverse_cancel _ hw; apply hD.mul_left_cancel
          change D*(q^(r+6)*(1-q^(2*r+2))*(1-q^(2*r+4))*(1-q^(2*r+6))*
              Ring.inverse (1-q)*Ring.inverse a*Ring.inverse b*Ring.inverse c) =
            D*(q^(r+3)*Ring.inverse (1-q)-(1+q+q^2)*Ring.inverse W*
              (q^(r+5)*Ring.inverse a+q^(r+4)*(1+q^2)*Ring.inverse b+
                q^(r+3)*(1+q+q^2+q^3+q^4)*Ring.inverse c))
          calc
            _ = q^(r+6)*W*(1-q^(2*r+2))*(1-q^(2*r+4))*(1-q^(2*r+6))*
                ((1-q)*Ring.inverse (1-q))*(a*Ring.inverse a)*(b*Ring.inverse b)*
                  (c*Ring.inverse c) := by dsimp [D];ring
            _ = q^(r+6)*W*(1-q^(2*r+2))*(1-q^(2*r+4))*(1-q^(2*r+6)) := by
              rw [hj,ha,hb,hc];ring
            _ = q^(r+3)*W*a*b*c-(1+q+q^2)*
                (q^(r+5)*(1-q)*b*c+q^(r+4)*(1+q^2)*(1-q)*a*c+
                  q^(r+3)*(1+q+q^2+q^3+q^4)*(1-q)*a*b) := by
              dsimp [W,a,b,c]; simp_rw [pow_add]; ring
            _ = q^(r+3)*W*a*b*c*((1-q)*Ring.inverse (1-q))-(1+q+q^2)*
                ((W*Ring.inverse W)*
                  (q^(r+5)*(1-q)*b*c*(a*Ring.inverse a)+
                    q^(r+4)*(1+q^2)*(1-q)*a*c*(b*Ring.inverse b)+
                    q^(r+3)*(1+q+q^2+q^3+q^4)*(1-q)*a*b*(c*Ring.inverse c))) := by
              rw [hj,ha,hb,hc,hW];ring
            _ = _ := by dsimp [D];ring
        have hnil (e : ℕ) (he : 0<e) : IsNilpotent (q^e) := by
          refine ⟨N,?_⟩
          rw [←pow_mul,Nat.mul_comm,pow_mul,hq,zero_pow (by omega)]
        have hu (e : ℕ) (he : 0<e) : IsUnit (1-q^e) := (hnil e he).isUnit_one_sub
        have hu1 : IsUnit (1-q) := by simpa using hu 1 (by omega)
        have hw : IsUnit ((1+q)^2*(1+q^2)) :=
          (IsNilpotent.isUnit_one_add (by simpa using hnil 1 (by omega))).pow 2 |>.mul
            (IsNilpotent.isUnit_one_add (hnil 2 (by omega)))
        let g (e : ℕ) := Ring.inverse (1-q^e)
        let W:=(1+q)^2*(1+q^2)
        let w:=Ring.inverse W
        let a:=1+q+q^2
        let b:=1+q+q^2+q^3+q^4
        let T:=∑ j ∈ Finset.range N, q^j*g (2*j+1)
        have hg (e : ℕ) (he : 0<e) : (1-q^e)*g e=1 := Ring.mul_inverse_cancel _ (hu e he)
        have hg1 : (1-q)*g 1=1 := by simpa using hg 1 (by omega)
        have hw1 : W*w=1 := Ring.mul_inverse_cancel _ hw
        have hzero (e : ℕ) (he : N≤e) : q^e=0 := by
          rw [show e=N+(e-N) by omega,pow_add,hq,zero_mul]
        have hqsum : (∑ j ∈ Finset.range N, q^j)=g 1 := by
          apply hu1.mul_left_cancel; rw [hg1]; have hs:=mul_geom_sum q N; rw [hq] at hs
          calc
            _ = -((q-1)*(∑ j ∈ range N,q^j)) := by ring
            _ = 1 := by rw [hs];ring
        have hshift (i : ℕ) :
            (∑ r ∈ Finset.range N, q^(r+i)*g (2*r+2*i+1)) =
            T-(∑ j ∈ Finset.range i, q^j*g (2*j+1)) := by
          let f (j : ℕ):=q^j*g (2*j+1)
          have hl:=Finset.sum_range_add f i N; have hr:=Finset.sum_range_add f N i
          have hz : (∑ j ∈ Finset.range i, f (N+j))=0 := by
            apply Finset.sum_eq_zero; intro j _; simp only [f,hzero (N+j) (by omega),zero_mul]
          rw [hz,add_zero] at hr; rw [show i+N=N+i by omega,hr] at hl
          have hs : (∑ r ∈ Finset.range N, q^(r+i)*g (2*r+2*i+1)) =
              ∑ r ∈ Finset.range N, f (i+r) := by
            apply Finset.sum_congr rfl; intro r _; dsimp [f]
            congr 2 <;> omega
          rw [hs]; dsimp only [T,f] at *
          linear_combination -hl
        have hlead : (∑ r ∈ Finset.range N, q^(r+3)*g 1)=q^3*g 1^2 := by
          rw [show (∑ r ∈ Finset.range N, q^(r+3)*g 1)=
            q^3*g 1*(∑ r ∈ Finset.range N,q^r) by
              rw [Finset.mul_sum];apply Finset.sum_congr rfl
              intro r _;rw [pow_add];ring,hqsum]
          ring
        have hsh1 : (∑ r ∈ Finset.range N,q^(r+5)*g (2*r+3))=q^4*(T-g 1) := by
          have hs:=hshift 1
          simp only [Nat.mul_one,Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,
            zero_add,Nat.mul_zero,one_mul] at hs
          rw [show (∑ r ∈ Finset.range N,q^(r+5)*g (2*r+3))=
            q^4*(∑ r ∈ Finset.range N,q^(r+1)*g (2*r+3)) by
              rw [Finset.mul_sum];apply Finset.sum_congr rfl
              intro r _;rw [show r+5=4+(r+1) by omega,pow_add];ring,hs]
        have hsh2 : (∑ r ∈ Finset.range N,q^(r+4)*g (2*r+5))=
            q^2*(T-(g 1+q*g 3)) := by
          have hs:=hshift 2; norm_num [Finset.sum_range_succ] at hs
          rw [show (∑ r ∈ Finset.range N,q^(r+4)*g (2*r+5))=
            q^2*(∑ r ∈ Finset.range N,q^(r+2)*g (2*r+5)) by
              rw [Finset.mul_sum];apply Finset.sum_congr rfl
              intro r _;rw [show r+4=2+(r+2) by omega,pow_add];ring]
          rw [hs]
        have hsh3 : (∑ r ∈ Finset.range N,q^(r+3)*g (2*r+7))=
            T-(g 1+q*g 3+q^2*g 5) := by
          have hs:=hshift 3; norm_num [Finset.sum_range_succ] at hs; exact hs
        have hsum : q^2*(∑ r ∈ Finset.range N, q^(r+4)*(1-q^(2*r+2))*
            (1-q^(2*r+4))*(1-q^(2*r+6))*g 1*g (2*r+3)*g (2*r+5)*g (2*r+7)) =
            q^3*g 1^2-a*w*(q^4*(T-g 1)+q^2*(1+q^2)*(T-g 1-q*g 3)+
              b*(T-g 1-q*g 3-q^2*g 5)) := by
          rw [Finset.mul_sum]
          have hh : (∑ r ∈ Finset.range N, q^2*(q^(r+4)*(1-q^(2*r+2))*
              (1-q^(2*r+4))*(1-q^(2*r+6))*g 1*g (2*r+3)*g (2*r+5)*g (2*r+7))) =
              ∑ r ∈ Finset.range N, (q^(r+3)*g 1 -
                a*w*(q^(r+5)*g (2*r+3)+q^(r+4)*(1+q^2)*g (2*r+5)+
                  q^(r+3)*b*g (2*r+7))) := by
            apply Finset.sum_congr rfl; intro r _; have hpr:=hpf q N r hq; dsimp only [g,a,b,w,W]
            simp only [pow_one]
            convert hpr using 1
            rw [show r+6=2+(r+4) by omega,pow_add];ring
          rw [hh,Finset.sum_sub_distrib,←Finset.mul_sum]; simp only [Finset.sum_add_distrib]
          rw [show (∑ r ∈ Finset.range N,q^(r+4)*(1+q^2)*g (2*r+5))=
            (1+q^2)*(∑ r ∈ Finset.range N,q^(r+4)*g (2*r+5)) by
              rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro r _;ring,
            show (∑ r ∈ Finset.range N,q^(r+3)*b*g (2*r+7))=
            b*(∑ r ∈ Finset.range N,q^(r+3)*g (2*r+7)) by
              rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro r _;ring]
          rw [hlead,hsh1,hsh2,hsh3]; ring
        simp only [←show g 1=Ring.inverse (1-q) by simp [g]]
        change q^2*(∑ r ∈ Finset.range N, q^(r+4)*(1-q^(2*r+2))*
          (1-q^(2*r+4))*(1-q^(2*r+6))*g 1*g (2*r+3)*g (2*r+5)*g (2*r+7)) = _
        rw [hsum]
        have hconstant : q^3*g 1^2+a*w*(q^4*g 1+q^2*(1+q^2)*(g 1+q*g 3)+
            b*(g 1+q*g 3+q^2*g 5)) =
            (1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7)*g 1^2*w := by
          have hD : IsUnit ((1-q)^2*W) := hu1.pow 2 |>.mul hw; apply hD.mul_left_cancel
          have h3 : (1-q)*a*g 3=1 := by
            rw [show (1-q)*a=1-q^3 by dsimp [a];ring]; exact hg 3 (by omega)
          have h5 : (1-q)*b*g 5=1 := by
            rw [show (1-q)*b=1-q^5 by dsimp [b];ring]; exact hg 5 (by omega)
          calc
            _ = q^3*W*((1-q)*g 1)^2+
                (W*w)*((1-q)*a*(q^4+q^2*(1+q^2)+b)*((1-q)*g 1)+
                  q*(1-q)*(q^2*(1+q^2)+b)*((1-q)*a*g 3)+
                  q^2*(1-q)*a*((1-q)*b*g 5)) := by ring
            _ = q^3*W+(1-q)*a*(q^4+q^2*(1+q^2)+b)+
                q*(1-q)*(q^2*(1+q^2)+b)+q^2*(1-q)*a := by rw [hg1,hw1,h3,h5];ring
            _ = 1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7 := by dsimp [W,a,b];ring
            _ = _ := by
              rw [show (1-q)^2*W*((1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7)*g 1^2*w)=
                (1+2*q+3*q^2+2*q^3+3*q^4-q^6-2*q^7)*((1-q)*g 1)^2*(W*w) by ring,
                hg1,hw1];ring
        have hGF := hconstant; dsimp only [g,w,W,a,b,T] at *
        linear_combination hGF
      let I:=Ideal.span {(X^(n+3) : PowerSeries ℤ)}
      let F:=Ideal.Quotient.mk I
      let q:=F X
      have hq : q^(n+3)=0 := by
        rw [←map_pow,Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (Set.mem_singleton _)
      have hinv (e : ℕ) (he : 0<e) : F (geom e)=Ring.inverse (1-q^e) := by
        have hmul:=congrArg F (hgeom e he); simp only [map_mul,map_sub,map_one,map_pow] at hmul
        have hu : IsUnit (1-F X^e) :=
          isUnit_iff_exists_inv.mpr ⟨F (geom e),by simpa [mul_comm] using hmul⟩
        apply hu.mul_right_cancel; rw [Ring.inverse_mul_cancel _ hu]; exact hmul
      have hW : F (J^2*K)=Ring.inverse ((1+q)^2*(1+q^2)) := by
        have hmul : ((1+X)^2*(1+X^2))*(J^2*K)=1 := by
          calc
            _ = ((1+X)*J)^2*((1+X^2)*K) := by ring
            _ = 1 := by rw [hj,hk];ring
        have hh:=congrArg F hmul; simp only [map_mul,map_pow,map_add,map_one] at hh
        have hu : IsUnit ((1+q)^2*(1+q^2)) := isUnit_iff_exists_inv.mpr ⟨F (J^2*K),hh⟩
        apply hu.mul_left_cancel; rw [Ring.mul_inverse_cancel _ hu]; exact hh
      have hfg : F (X^2*(∑ r ∈ Finset.range (n+3), X^(r+4)*(1-X^(2*r+2))*
            (1-X^(2*r+4))*(1-X^(2*r+6))*geom 1*geom (2*r+3)*
              geom (2*r+5)*geom (2*r+7))) =
          F ((1+2*X+3*X^2+2*X^3+3*X^4-X^6-2*X^7)*G^2*J^2*K-
            (1+X+X^2)*(1+X+2*X^2+X^3+3*X^4)*J^2*K*
              (∑ j ∈ Finset.range (n+3),X^j*geom (2*j+1))) := by
        have hh:=hgf q (n+3) (by omega) hq; have hhW := hW; simp only [map_mul,map_pow] at hhW
        simp only [map_mul,map_sum,map_pow,map_sub,map_add,map_one,map_ofNat]
        have hodd1 (j : ℕ) : F (geom (2*j+1))=Ring.inverse (1-q^(2*j+1)) :=
          hinv _ (by omega)
        have hodd3 (j : ℕ) : F (geom (2*j+3))=Ring.inverse (1-q^(2*j+3)) :=
          hinv _ (by omega)
        have hodd5 (j : ℕ) : F (geom (2*j+5))=Ring.inverse (1-q^(2*j+5)) :=
          hinv _ (by omega)
        have hodd7 (j : ℕ) : F (geom (2*j+7))=Ring.inverse (1-q^(2*j+7)) :=
          hinv _ (by omega)
        simp_rw [hodd1,hodd3,hodd5,hodd7,hinv 1 (by decide),pow_one] at ⊢
        simp only [G,hinv 1 (by decide),pow_one] at ⊢; simp only [mul_assoc,hhW]
        simpa only [mul_assoc] using hh
      have hmem:=Ideal.Quotient.eq.mp hfg
      obtain ⟨p,hp⟩:=Ideal.mem_span_singleton.mp hmem
      have hc:=congrArg (coeff (n+2)) hp
      have hz : coeff (n+2) (X^(n+3)*p)=0 := by
        rw [coeff_X_pow_mul',if_neg (by omega)]
      rw [map_sub,hz] at hc; have heq:=sub_eq_zero.mp hc
      rw [coeff_X_pow_mul',if_pos (by omega),show n+2-2=n by omega] at heq
      have hpad : coeff n (∑ r ∈ Finset.range (n+3), X^(r+4)*(1-X^(2*r+2))*
            (1-X^(2*r+4))*(1-X^(2*r+6))*geom 1*geom (2*r+3)*
              geom (2*r+5)*geom (2*r+7)) =
          coeff n (∑ r ∈ Finset.range (n+1), X^(r+4)*(1-X^(2*r+2))*
            (1-X^(2*r+4))*(1-X^(2*r+6))*geom 1*geom (2*r+3)*
              geom (2*r+5)*geom (2*r+7)) := by
        rw [map_sum,map_sum]
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega)); intro r _ hout
        have hr : n<r := by simpa using hout
        rw [show X^(r+4)*(1-X^(2*r+2))*(1-X^(2*r+4))*(1-X^(2*r+6))*
          geom 1*geom (2*r+3)*geom (2*r+5)*geom (2*r+7) =
          X^(r+4)*((1-X^(2*r+2))*(1-X^(2*r+4))*(1-X^(2*r+6))*
            geom 1*geom (2*r+3)*geom (2*r+5)*geom (2*r+7)) by ring,
          coeff_X_pow_mul',if_neg (by omega)]
      rw [hpad] at heq; exact heq
    have hP (l : ℕ) (hl : 2≤l) :
        let G:=geom 1
        let J:=PowerSeries.rescale (-1 : ℤ) G
        let K:=(1-X^2)*geom 4
        coeff l ((1+2*X+3*X^2+2*X^3+3*X^4-X^6-2*X^7)*G^2*J^2*K) =
          (4*(l : ℤ)+9+(-1 : ℤ)^l*(2*(l : ℤ)-3)+2*(-1 : ℤ)^(l/2))/4 := by
      classical
      dsimp only; have hg : (1-X)*G=1 := by simpa [G,mul_comm] using hgeom 1 (by decide)
      have hj : (1+X)*J=1 := by
        have hh:=congrArg (PowerSeries.rescale (-1 : ℤ)) hg
        simpa [J,map_mul,map_sub,PowerSeries.rescale_X] using hh
      have hk : (1+X^2)*K=1 := by
        calc
          _ = geom 4*(1-X^4) := by dsimp [K];ring
          _ = 1 := hgeom 4 (by decide)
      have hKperiod : coeff l ((1+X)*K)=(-1 : ℤ)^(l/2) := by
        rw [add_mul,one_mul,map_add,show X*K=X^1*K by simp,coeff_X_pow_mul',if_pos (by omega),hK,hK]
        rcases (show l%2=0 ∨ l%2=1 by omega) with he | ho
        · have hn : ¬2∣l-1 := by omega
          simp [Nat.dvd_iff_mod_eq_zero,he,hn]
        · have hn : 2∣l-1 := by omega
          have heq : (l-1)/2=l/2 := by omega
          simp [Nat.dvd_iff_mod_eq_zero,ho,hn,heq]
      have hf:=(hpf X G J K hg hj hk).1; have hc:=congrArg (coeff l) hf
      have hscale (a : ℕ) (f : PowerSeries ℤ) : coeff l ((a : PowerSeries ℤ)*f)=
          (a : ℤ)*coeff l f := by
        rw [show (a : PowerSeries ℤ)*f=a • f by simp [nsmul_eq_mul],map_nsmul]; simp [nsmul_eq_mul]
      change coeff l _ = _
      have hzero : coeff l (-8*X-4 : PowerSeries ℤ)=0 := by
        rw [map_sub]; have ha : (-8 : PowerSeries ℤ)*X=C (-8)*X := by simp
        rw [ha,coeff_C_mul]; rw [show (4 : PowerSeries ℤ)=C 4 by norm_num,coeff_C]
        simp [coeff_X,show l≠0 by omega,show l≠1 by omega]
      rw [show 4*(1+2*X+3*X^2+2*X^3+3*X^4-X^6-2*X^7)*G^2*J^2*K=
        (4 : PowerSeries ℤ)*((1+2*X+3*X^2+2*X^3+3*X^4-X^6-2*X^7)*G^2*J^2*K)
        by ring] at hc
      have hs4 := hscale 4; norm_num only [Nat.cast_ofNat] at hs4; rw [hs4] at hc
      rw [map_add,map_add,map_add,map_sub,map_add,hzero] at hc; have hs2 := hscale 2
      have hs5 := hscale 5; norm_num only [Nat.cast_ofNat] at hs2 hs5
      rw [show 2*(1+X)*K=(2 : PowerSeries ℤ)*((1+X)*K) by ring,hs2,
        hs5,hs2,hs5,hs4,hKperiod,hJ,hJ2,hG,hG2] at hc
      have hv : 4*coeff l
          ((1+2*X+3*X^2+2*X^3+3*X^4-X^6-2*X^7)*G^2*J^2*K)=
          4*(l : ℤ)+9+(-1 : ℤ)^l*(2*(l : ℤ)-3)+2*(-1 : ℤ)^(l/2) := by
        linarith
      rw [←hv,Int.mul_ediv_cancel_left _ (by decide : (4 : ℤ)≠0)]
    have hB (l : ℕ) (hl : 2≤l) (T : PowerSeries ℤ)
        (hT : ∀ i : ℕ,i≤l → coeff i T=((2*i+1).divisors.card : ℤ))
        (hdecomp :
          (1+X+X^2)*(1+X+2*X^2+X^3+3*X^4)*
            (PowerSeries.rescale (-1 : ℤ) (geom 1))^2*((1-X^2)*geom 4) =
            3*X^2-2*X+4+((1-X^2)*geom 4)-
              6*(PowerSeries.rescale (-1 : ℤ) (geom 1))+
              2*(PowerSeries.rescale (-1 : ℤ) (geom 1))^2) :
        coeff l ((1+X+X^2)*(1+X+2*X^2+X^3+3*X^4)*
            (PowerSeries.rescale (-1 : ℤ) (geom 1))^2*((1-X^2)*geom 4)*T) =
          3*((2*(l-2)+1).divisors.card : ℤ)-2*((2*(l-1)+1).divisors.card : ℤ)+
          4*((2*l+1).divisors.card : ℤ)+
          (∑ t ∈ Finset.range (l/2+1), (-1 : ℤ)^t*((2*(l-2*t)+1).divisors.card : ℤ))-
          6*(∑ i ∈ Finset.range (l+1),(-1 : ℤ)^(l-i)*((2*i+1).divisors.card : ℤ))+
          2*(∑ i ∈ Finset.range (l+1),
            (-1 : ℤ)^(l-i)*((l-i : ℕ)+1)*((2*i+1).divisors.card : ℤ)) := by
      classical
      have hU : coeff l (J*T)=∑ i ∈ Finset.range (l+1),
          (-1 : ℤ)^(l-i)*((2*i+1).divisors.card : ℤ) := by
        rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl; intro i hi; rw [hT i (by simpa using hi),hJ,mul_comm]
      have hV : coeff l (J^2*T)=∑ i ∈ Finset.range (l+1),
          (-1 : ℤ)^(l-i)*((l-i : ℕ)+1)*((2*i+1).divisors.card : ℤ) := by
        rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl; intro i hi; rw [hT i (by simpa using hi),hJ2]; push_cast; ring
      have hH : coeff l (K*T)=∑ t ∈ Finset.range (l/2+1),
          (-1 : ℤ)^t*((2*(l-2*t)+1).divisors.card : ℤ) := by
        rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp_rw [hK,ite_mul,zero_mul]
        rw [←Finset.sum_filter]
        symm
        apply Finset.sum_bij (fun t _=>2*t)
        · intro t ht
          have ht : t<l/2+1 := Finset.mem_range.mp ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨t,rfl⟩⟩
        · intro a _ b _ hab
          omega
        · intro i hi
          obtain ⟨hir,hid⟩:=Finset.mem_filter.mp hi
          obtain ⟨t,ht⟩:=hid
          exact ⟨t,Finset.mem_range.mpr (by have := Finset.mem_range.mp hir;omega),
            ht.symm⟩
        · intro t ht
          have ht : t<l/2+1 := Finset.mem_range.mp ht
          rw [Nat.mul_div_cancel_left _ (by decide : 0<2),hT _ (by omega)]
      have hscale (a : ℕ) (f : PowerSeries ℤ) : coeff l ((a : PowerSeries ℤ)*f)=
          (a : ℤ)*coeff l f := by
        rw [show (a : PowerSeries ℤ)*f=a • f by simp [nsmul_eq_mul],map_nsmul]; simp [nsmul_eq_mul]
      have hs2 := hscale 2; have hs3 := hscale 3; have hs4 := hscale 4; have hs6 := hscale 6
      norm_num only [Nat.cast_ofNat] at hs2 hs3 hs4 hs6; rw [hdecomp]
      change coeff l ((3*X^2-2*X+4+K-6*J+2*J^2)*T)=_; rw [add_mul,sub_mul,add_mul,add_mul,sub_mul]
      rw [map_add,map_sub,map_add,map_add,map_sub]
      rw [show 3*X^2*T=(3 : PowerSeries ℤ)*(X^2*T) by ring,hs3,
        show 2*X*T=(2 : PowerSeries ℤ)*(X^1*T) by simp [mul_assoc],hs2,
        hs4,show 6*J*T=(6 : PowerSeries ℤ)*(J*T) by ring,hs6,
        show 2*J^2*T=(2 : PowerSeries ℤ)*(J^2*T) by ring,hs2]
      rw [coeff_X_pow_mul',if_pos (by omega),coeff_X_pow_mul',if_pos (by omega),
        hT _ (by omega),hT _ (by omega),hT _ (by omega),hH,hU,hV]
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
    let T : PowerSeries ℤ:=∑ j ∈ Finset.range (n+3),X^j*geom (2*j+1)
    have ht (i : ℕ) (hi : i≤n+2) : coeff i T=((2*i+1).divisors.card : ℤ) :=
      hT i (n+2) hi
    have hp:=hP (n+2) (by omega); have hb:=hB (n+2) (by omega) T ht (hpf X G J K hg hj hk).2
    rw [htrans n,hgen n,map_sub,hp,hb]
    rw [show 2*(n+2-2)+1=2*n+1 by omega,
      show 2*(n+2-1)+1=2*n+3 by omega,
      show 2*(n+2)+1=2*n+5 by omega]
    ring
  have hlarge (n : ℕ) (p h u v : ℤ)
      (hp : p = (4*((n+2 : ℕ):ℤ)+9+(-1 : ℤ)^(n+2)*(2*((n+2 : ℕ):ℤ)-3)+
        2*(-1 : ℤ)^((n+2)/2))/4)
      (hh : |h| ≤ (Nat.sqrt (2*n+5):ℤ)+2)
      (hu : |u| ≤ (((Nat.sqrt (2*n+5)+1)/2:ℕ):ℤ))
      (hv : 0 ≤ (-1 : ℤ)^(n+2)*v ∧
        (-1 : ℤ)^(n+2)*v ≤ (((Nat.sqrt (2*n+7)+1)/2:ℕ):ℤ)^2) :
      (n : ℝ)/2-12*Real.sqrt (2*(n : ℝ)+7)-12 ≤
        (p : ℝ)-3*((2*n+1).divisors.card : ℝ)+2*((2*n+3).divisors.card : ℝ)-
        4*((2*n+5).divisors.card : ℝ)-(h : ℝ)+6*(u : ℝ)-2*(v : ℝ) := by
    let R := Real.sqrt (2*(n : ℝ)+7)
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R^2 = 2*(n : ℝ)+7 := Real.sq_sqrt (by positivity)
    have hroot (M : ℕ) (hM : M ≤ 2*n+7) : (Nat.sqrt M : ℝ) ≤ R := by
      have h1 := Real.nat_sqrt_le_real_sqrt (a := M)
      have h2 : Real.sqrt (M : ℝ) ≤ R := Real.sqrt_le_sqrt (by exact_mod_cast hM)
      exact h1.trans h2
    have hhalf (M : ℕ) (hM : M ≤ 2*n+7) :
        (((Nat.sqrt M+1)/2:ℕ):ℝ) ≤ (R+1)/2 := by
      have h : (2 : ℝ)*(((Nat.sqrt M+1)/2:ℕ):ℝ) ≤ (Nat.sqrt M : ℝ)+1 := by
        have hd := Nat.div_mul_le_self (Nat.sqrt M+1) 2
        exact_mod_cast (by omega : 2*((Nat.sqrt M+1)/2) ≤ Nat.sqrt M+1)
      linarith [hroot M hM]
    have ht (M : ℕ) (hM : M ≤ 2*n+7) (hOdd : Odd M) :
        (M.divisors.card : ℝ) ≤ R+1 := by
      have h := odd_divisors_card_le M hOdd
      have hc : (M.divisors.card : ℝ) ≤ (Nat.sqrt M : ℝ)+1 := by exact_mod_cast h
      linarith [hroot M hM]
    have ht1 := ht (2*n+1) (by omega) ⟨n,by omega⟩
    have ht5 := ht (2*n+5) (by omega) ⟨n+2,by omega⟩
    have ht3 : (0 : ℝ) ≤ (2*n+3).divisors.card := Nat.cast_nonneg _
    have hhR : (h : ℝ) ≤ R+2 := by
      have hc : (h : ℝ) ≤ (Nat.sqrt (2*n+5) : ℝ)+2 := by
        exact_mod_cast (le_abs_self h).trans hh
      linarith [hroot (2*n+5) (by omega)]
    have huR : -2*(u : ℝ) ≤ R+1 := by
      have hi := (neg_le_abs u).trans hu
      have hc : -(u : ℝ) ≤ (((Nat.sqrt (2*n+5)+1)/2:ℕ):ℝ) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using (Int.cast_le (R := ℝ)).mpr hi
      linarith [hhalf (2*n+5) (by omega)]
    have hpv : (n : ℝ)/2-R ≤ (p : ℝ)-2*(v : ℝ) := by
      have hmod := Nat.mod_lt (n+2) (by decide : 0 < 2)
      have hmod2 := Nat.mod_lt ((n+2)/2) (by decide : 0 < 2)
      have hpl : (if (n+2)%2=0 then 3*((n+2 : ℕ):ℤ)+2 else ((n+2 : ℕ):ℤ)+5) ≤ 2*p := by
        rw [neg_one_pow_eq_pow_mod_two (n+2), neg_one_pow_eq_pow_mod_two ((n+2)/2)] at hp
        interval_cases hl : (n+2)%2 <;> interval_cases he : (n+2)/2%2 <;>
          simp only [hl,he,pow_zero,pow_one] at hp ⊢ <;> norm_num at hp ⊢ <;> omega
      rw [neg_one_pow_eq_pow_mod_two (n+2)] at hv
      by_cases he : (n+2)%2=0
      · simp only [he,pow_zero,one_mul,if_true] at hv hpl
        have hpR : 3*((n : ℝ)+2)+2 ≤ 2*(p : ℝ) := by exact_mod_cast hpl
        have hvR : (v : ℝ) ≤ (((Nat.sqrt (2*n+7)+1)/2:ℕ):ℝ)^2 := by
          simpa only [Int.cast_pow,Int.cast_natCast] using (Int.cast_le (R := ℝ)).mpr hv.2
        have hr := hhalf (2*n+7) (by omega)
        have hr0 : (0 : ℝ) ≤ (((Nat.sqrt (2*n+7)+1)/2:ℕ):ℝ) := Nat.cast_nonneg _
        nlinarith
      · have ho : (n+2)%2=1 := by omega
        simp only [ho,pow_one,neg_one_mul,if_false] at hv hpl
        have hpR : (n : ℝ)+7 ≤ 2*(p : ℝ) := by exact_mod_cast hpl
        have hvR : (v : ℝ) ≤ 0 := by exact_mod_cast (by linarith [hv.1] : v ≤ 0)
        linarith
    dsimp [R] at hpv ht1 ht5 hhR huR; linarith
  have hthreshold (n : ℕ) (hn : 1203 ≤ n) :
      (0 : ℝ) ≤ (n : ℝ)/2 - 12*Real.sqrt (2*(n : ℝ)+7) - 12 := by
    have hnR : (1203 : ℝ) ≤ n := by exact_mod_cast hn
    let R := Real.sqrt (2*(n : ℝ)+7)
    have hRpos : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R^2 = 2*(n : ℝ)+7 := Real.sq_sqrt (by positivity)
    have hpoly : (12 : ℝ)^2*(2*(n : ℝ)+7) ≤ ((n : ℝ)/2-12)^2 := by
      nlinarith [sq_nonneg ((n : ℝ)-1203)]
    have hthresh : (12 : ℝ)*R ≤ (n : ℝ)/2-12 := by nlinarith
    dsimp [R] at hthresh
    linarith
  have hparity (l : ℕ) :
      (∑ t ∈ range (l/2+1), (-1 : ℤ)^t*((2*(l-2*t)+1).divisors.card : ℤ)) =
        ∑ i ∈ (range (l+1)).filter (fun i => i%2=l%2),
          (-1 : ℤ)^((l-i)/2)*((2*i+1).divisors.card : ℤ) := by
    apply sum_bij (fun t _ => l-2*t)
    · intro t ht
      simp only [mem_range] at ht
      simp only [mem_filter,mem_range]; omega
    · intro t ht s hs heq
      simp only [mem_range] at ht hs; omega
    · intro i hi
      simp only [mem_filter,mem_range] at hi
      exact ⟨(l-i)/2,mem_range.mpr (by omega),by omega⟩
    · intro t ht
      have := mem_range.mp ht
      rw [show (l-(l-2*t))/2=t by omega]
  have hfinite (n : ℕ) (hn : n < 1203) :
      0 ≤ (4*((n+2 : ℕ) : ℤ)+9+(-1 : ℤ)^(n+2)*(2*((n+2 : ℕ) : ℤ)-3)+
        2*(-1 : ℤ)^((n+2)/2))/4-
      3*((2*n+1).divisors.card : ℤ)+2*((2*n+3).divisors.card : ℤ)-
      4*((2*n+5).divisors.card : ℤ)-
      (∑ t ∈ range ((n+2)/2+1),(-1 : ℤ)^t*((2*(n+2-2*t)+1).divisors.card : ℤ))+
      6*(∑ i ∈ range (n+3),(-1 : ℤ)^(n+2-i)*((2*i+1).divisors.card : ℤ))-
      2*(∑ i ∈ range (n+3),(-1 : ℤ)^(n+2-i)*
        ((n+2-i : ℕ)+1)*((2*i+1).divisors.card : ℤ)) := by
    let tau := fun i => (((2*i+1).primeFactors.prod
      (fun p => (2*i+1).primeFactorsList.count p+1) : ℕ) : ℤ)
    have htau (i : ℕ) : tau i = ((2*i+1).divisors.card : ℤ) := by
      dsimp [tau]; rw [Nat.card_divisors (by omega)]
      simp only [Nat.primeFactorsList_count_eq]
    let U := fun k => ∑ i ∈ range k, (-1 : ℤ)^(k-1-i)*tau i
    let V := fun k => ∑ i ∈ range k, (-1 : ℤ)^(k-1-i)*
      ((k-1-i : ℕ)+1)*tau i
    let H := fun k => ∑ t ∈ range (k/2+1), (-1 : ℤ)^t*
      tau (k-2*t)
    have hU (k : ℕ) : U (k+1) = tau k-U k := by
      dsimp [U]; rw [sum_range_succ]
      simp only [Nat.sub_self,pow_zero,one_mul]
      have he : (∑ i ∈ range k, (-1 : ℤ)^(k-i)*tau i) =
          -(∑ i ∈ range k, (-1 : ℤ)^(k-1-i)*tau i) := by
        rw [←sum_neg_distrib]; apply sum_congr rfl; intro i hi
        rw [show k-i=(k-1-i)+1 by have := mem_range.mp hi; omega,pow_succ]; ring
      rw [he]; ring
    have hV (k : ℕ) : V (k+1) = U (k+1)-V k := by
      dsimp [V]; rw [sum_range_succ]
      simp only [Nat.sub_self,pow_zero,one_mul,Nat.cast_zero,zero_add]
      have he : (∑ i ∈ range k, (-1 : ℤ)^(k-i)*
          ((k-i : ℕ)+1)*tau i) = -U k-V k := by
        dsimp [U,V]; rw [←sum_neg_distrib,←sum_sub_distrib]
        apply sum_congr rfl; intro i hi
        rw [show k-i=(k-1-i)+1 by have := mem_range.mp hi; omega,pow_succ]
        push_cast; ring
      rw [he,hU]; ring
    have hH2 (k : ℕ) : H (k+2)+H k = tau (k+2) := by
      dsimp [H]
      rw [show (k+2)/2+1=(k/2+1)+1 by omega,sum_range_succ']
      simp only [Nat.mul_zero,Nat.sub_zero,pow_zero,one_mul]
      have he : (∑ t ∈ range (k/2+1), (-1 : ℤ)^(t+1)*
          tau (k+2-2*(t+1))) = -H k := by
        dsimp [H]; rw [←sum_neg_distrib]; apply sum_congr rfl; intro t _
        rw [show k+2-2*(t+1)=k-2*t by omega,pow_succ]; ring
      rw [he]; ring
    have hH (k : ℕ) : H k = tau k-
        (if k≤1 then 0 else H (k-2)) := by
      rcases k with _|_|k
      · simp [H]
      · simp [H]
      · have h := hH2 k
        simp only [if_neg (by omega : ¬k+1+1≤1)]
        change H (k+2) = tau (k+2)-H k
        linarith
    let step := fun (s : ℤ×ℤ×ℤ×ℤ) i =>
      let u := tau i-s.1
      (u,u-s.2.1,tau i-s.2.2.2,s.2.2.1)
    let states := (List.range 1206).scanl step (0,0,0,0)
    have hfold (k : ℕ) : (List.range k).foldl step (0,0,0,0) =
        (U k,V k,if k=0 then 0 else H (k-1),if k≤1 then 0 else H (k-2)) := by
      induction k with
      | zero => simp [U,V]
      | succ k ih =>
        rw [List.range_succ,List.foldl_append]
        simp only [List.foldl_cons,List.foldl_nil]; rw [ih]
        rw [hV k,hU k]
        simp only [show k+1≠0 by omega,if_false,Nat.add_sub_cancel]
        rw [hH k]
        by_cases hk : k=0
        · subst k; simp [step]
        · have hk1 : ¬ k+1≤1 := by omega
          simp [step,hk,hk1,show k+1-2=k-1 by omega]
    have hget (k : ℕ) (hk : k<1207) : states[k]'(by simp [states];omega) =
        (U k,V k,if k=0 then 0 else H (k-1),if k≤1 then 0 else H (k-2)) := by
      rw [List.getElem_scanl,List.take_range,Nat.min_eq_left (by omega),hfold]
    let pairs := (List.range 1203).zip (states.drop 3)
    let good := fun (p : ℕ × (ℤ×ℤ×ℤ×ℤ)) =>
      decide (0 ≤ (4*((p.1+2 : ℕ) : ℤ)+9+(-1 : ℤ)^(p.1+2)*
        (2*((p.1+2 : ℕ) : ℤ)-3)+2*(-1 : ℤ)^((p.1+2)/2))/4-
        3*tau p.1+2*tau (p.1+1)-
        4*tau (p.1+2)-p.2.2.2.1+6*p.2.1-2*p.2.2.1)
    have cert : pairs.all good = true := by decide +kernel
    have hnLen : n < pairs.length := by simp [pairs,states]; omega
    have hc := List.all_eq_true.mp cert _ (List.getElem_mem hnLen)
    have hpair : pairs[n]'hnLen = (n,(U (n+3),V (n+3),H (n+2),H (n+1))) := by
      simp only [pairs,List.getElem_zip,List.getElem_range,List.getElem_drop]
      rw [hget (3+n) (by omega)]
      simp [show 3+n=n+3 by omega]
    rw [hpair] at hc
    have hp := of_decide_eq_true hc
    dsimp [good,U,V,H] at hp
    simp only [htau] at hp
    exact hp
  intro n
  rw [hformula n]
  by_cases hn : 1203 ≤ n
  · let p : ℤ := (4*((n+2 : ℕ) : ℤ)+9+(-1 : ℤ)^(n+2)*
        (2*((n+2 : ℕ) : ℤ)-3)+2*(-1 : ℤ)^((n+2)/2))/4
    let h : ℤ := ∑ t ∈ range ((n+2)/2+1), (-1 : ℤ)^t*
      ((2*(n+2-2*t)+1).divisors.card : ℤ)
    let u : ℤ := ∑ i ∈ range (n+3), (-1 : ℤ)^(n+2-i)*
      ((2*i+1).divisors.card : ℤ)
    let v : ℤ := ∑ i ∈ range (n+3), (-1 : ℤ)^(n+2-i)*
      ((n+2-i : ℕ)+1)*((2*i+1).divisors.card : ℤ)
    have hh : |h| ≤ (Nat.sqrt (2*n+5) : ℤ)+2 := by
      dsimp [h]; rw [hparity (n+2)]
      simpa only [show 2*(n+2)+1=2*n+5 by omega] using
        parity_alternating_odd_divisor_sum_bound (n+2)
    have hu : |u| ≤ (((Nat.sqrt (2*n+5)+1)/2 : ℕ) : ℤ) := by
      simpa only [u,show n+2+1=n+3 by omega,show 2*(n+2)+1=2*n+5 by omega] using
        alternating_odd_divisor_sum_bound (n+2)
    have hv : 0 ≤ (-1 : ℤ)^(n+2)*v ∧
        (-1 : ℤ)^(n+2)*v ≤ (((Nat.sqrt (2*n+7)+1)/2 : ℕ) : ℤ)^2 := by
      simpa only [v, Nat.cast_add, Nat.cast_one, show n+2+1=n+3 by omega,
        show 2*(n+2)+3=2*n+7 by omega] using
        weighted_alternating_odd_divisor_sum_bound (n+2)
    have hc := (hthreshold n hn).trans (hlarge n p h u v rfl hh hu hv)
    change 0 ≤ p-3*((2*n+1).divisors.card : ℤ)+2*((2*n+3).divisors.card : ℤ)-
      4*((2*n+5).divisors.card : ℤ)-h+6*u-2*v
    exact_mod_cast hc
  · exact hfinite n (by omega)

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiTwo
