/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds
   mirror-E: none(waiver:odd-divisor-and-triangular-counting-bounds)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors,mathlib/module/Mathlib.Analysis.Real.Sqrt]
   utility: none
   digest: Odd-divisor pairing and triangular parity rows bound Gauss quotient coefficients. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207TripleProduct
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds

open PowerSeries Finset AndrewsElBachraouiDefs
open D5.S3.Combinatorics.InversionSeq.InversionSeq207TripleProduct
open D5.S3.Combinatorics.InversionSeq.InversionSeq207Euler

/-- Complementary divisor pairing bounds the divisor count of every positive odd integer. -/
theorem odd_divisors_card_le (M : ℕ) (hM : Odd M) : M.divisors.card ≤ Nat.sqrt M + 1 := by
  classical
  have hMpos : 0 < M := by obtain ⟨q, hq⟩ := hM; omega
  have hodd (d : ℕ) (hd : d ∣ M) : d % 2 = 1 := by
    have hrem := Nat.mod_lt d (by decide : 0 < 2)
    have hMod := Nat.odd_iff.mp hM
    obtain ⟨b, hb⟩ := hd
    by_contra h
    have hz : d % 2 = 0 := by omega
    rw [hb, Nat.mul_mod, hz] at hMod; simp at hMod
  let r := (Nat.sqrt M + 1) / 2
  let encode : ℕ → ℕ × ℕ := fun d =>
    if d ≤ Nat.sqrt M then (0, d / 2) else (1, (M / d) / 2)
  have hdata (d : ℕ) (hd : d ∈ M.divisors) :
      d * (M / d) = M ∧ d % 2 = 1 ∧ (M / d) % 2 = 1 ∧
      (d ≤ Nat.sqrt M ∨ M / d ≤ Nat.sqrt M) := by
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hmul := Nat.mul_div_cancel' hdvd
    exact ⟨hmul, hodd d hdvd, hodd (M / d) (Nat.div_dvd_of_dvd hdvd),
      Nat.le_sqrt_of_eq_mul hmul.symm⟩
  have hmap : Set.MapsTo encode M.divisors
      ((Finset.range 2).product (Finset.range r)) := by
    intro d hd
    obtain ⟨_, hod, hoc, hs⟩ := hdata d hd
    simp only [encode]
    split_ifs with hdsmall
    · simp only [Finset.mem_coe, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_range]
      constructor
      · decide
      · dsimp [r]
        omega
    · have hcsmall : M / d ≤ Nat.sqrt M := hs.resolve_left hdsmall
      simp only [Finset.mem_coe, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_range]
      constructor
      · decide
      · dsimp [r]
        omega
  have hinj : (M.divisors : Set ℕ).InjOn encode := by
    intro d hd e he hde
    obtain ⟨hdmul, hod, hoc, _⟩ := hdata d hd
    obtain ⟨hemul, hoe, hoe', _⟩ := hdata e he
    dsimp [encode] at hde
    split_ifs at hde with hdsmall hesmall hesmall
    · have hq := congrArg Prod.snd hde
      dsimp at hq; omega
    · have hq := congrArg Prod.fst hde
      simp at hq
    · have hq := congrArg Prod.fst hde
      simp at hq
    · have hq := congrArg Prod.snd hde
      dsimp at hq
      have hc : M / d = M / e := by omega
      have hcpos : 0 < M / e := by
        exact Nat.pos_of_dvd_of_pos
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)) hMpos
      apply Nat.eq_of_mul_eq_mul_right hcpos; simpa only [hc] using hdmul.trans hemul.symm
  have hcard := Finset.card_le_card_of_injOn encode hmap hinj
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range] at hcard
  dsimp [r] at hcard; omega


set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
/-- The Gauss quotient counts parity-compatible triangular pairs and has a uniform upper bound.
The coefficientwise transformation elaborates nested finite sums. -/
theorem gauss_product_coefficient_count_bound (n : ℕ) :
    let P : PowerSeries ℤ := ∏ i ∈ Finset.range (n + 1),
      ((1 - X ^ (2 + 2 * i)) * (1 - X ^ (4 + 2 * i)) * geom (1 + 2 * i) ^ 2)
    let pairs := (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun p =>
      (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
        ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2
    coeff n P = (pairs.card : ℤ) ∧
      (5 ≤ n → ((coeff n P : ℤ) : ℝ) ≤ 97 / 120 * (n : ℝ) +
        27 / 32 * Real.sqrt (2 * (n : ℝ) + 1 / 2) + 13 / 25) := by
  have hcoeff (n N : ℕ) (hn : n ≤ N) :
    coeff n (∏ i ∈ Finset.range (N+1),
      ((1-(X : PowerSeries ℤ)^(2+2*i))*(1-X^(4+2*i))*geom (1+2*i)^2)) =
      (((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter (fun p =>
        (p.1+1).choose 2+(p.2+1).choose 2 ≤ n ∧
        ((p.1+1).choose 2+(p.2+1).choose 2)%2=n%2)).card : ℤ) := by
    classical
    have hgauss (n N : ℕ) (hn : n ≤ N) :
        coeff n (∏ i ∈ Finset.range (N+1),
          ((1-(X : PowerSeries ℤ)^(2*i+2))*geom (2*i+1))) =
          (((Finset.range (n+1)).filter (fun a => (a+1).choose 2=n)).card : ℤ) := by
      classical
      have hcore (degree : ℕ) :
          coeff degree (pentagonalSeries ℚ *
            PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1)) formalTheta) =
          2 * (((Finset.range (degree + 1)).filter
            (fun a => (a + 1).choose 2 = degree)).card : ℚ) := by
        classical
        let ev : LaurentPolynomial ℚ →+* ℚ := LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1)
        let weighted := PowerSeries.map LaurentPolynomial.C (pentagonalSeries ℚ) * formalTheta
        have lower (a : ℕ) : a ≤ (a + 1).choose 2 := by
          induction a with
          | zero => simp
          | succ a ih =>
            rw [Nat.choose_succ_succ, Nat.choose_one_right]; omega
        have col (index : ℤ) :
            (coeff degree weighted).coeff index =
              if degree = (if 0 ≤ index then index.toNat.choose 2
                else (index.natAbs + 1).choose 2) then (-1 : ℚ) ^ index.natAbs else 0 := by
          have h := congrArg (coeff degree) (formal_triple_product index)
          rw [coeff_C_mul_X_pow] at h; convert h using 1
          dsimp [weighted]; rw [coeff_mul, coeff_mul]; simp only [coeff_mk]
          simp only [coeff_map, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
          apply Finset.sum_congr rfl; intro pair _
          exact AddMonoidAlgebra.coeff_single_zero_mul _ _ _
        have folded : coeff degree weighted =
            ∑ a ∈ Finset.range (degree + 1),
              LaurentPolynomial.C (if degree = (a + 1).choose 2 then (1 : ℚ) else 0) *
                (LaurentPolynomial.C ((-1 : ℚ) ^ (a + 1)) * LaurentPolynomial.T ((a + 1 : ℕ) : ℤ) +
                  LaurentPolynomial.C ((-1 : ℚ) ^ a) * LaurentPolynomial.T (-(a : ℤ))) := by
          apply LaurentPolynomial.ext; intro index; rw [col]; simp only [mul_add, ← mul_assoc]
          simp only [← map_mul]
          simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
            ← LaurentPolynomial.single_eq_C_mul_T,
            AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply,
            AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
          by_cases hpos : 0 < index
          · let a := index.toNat - 1
            have hindex : index = (a + 1 : ℕ) := by dsimp [a]; omega
            have habs : index.natAbs = a + 1 := by omega
            rw [if_pos (show 0 ≤ index by omega), habs,
              show index.toNat = a + 1 by omega]
            by_cases ha : a < degree + 1
            · rw [Finset.sum_eq_single a]
              · simp only [show ((a + 1 : ℕ) : ℤ) = index by omega, if_true,
                  if_neg (by omega : -(a : ℤ) ≠ index), add_zero]
                split_ifs <;> simp
              · intro b _ hba
                rw [if_neg (by omega : (b + 1 : ℕ) ≠ index),
                  if_neg (by omega : -(b : ℤ) ≠ index), zero_add]
              · exact fun hout => (hout (Finset.mem_range.mpr ha)).elim
            · have hne : degree ≠ (a + 1).choose 2 := by have := lower a; omega
              rw [if_neg hne]
              symm
              apply Finset.sum_eq_zero; intro b hb; simp only [Finset.mem_range] at hb
              rw [if_neg (by omega : (b + 1 : ℕ) ≠ index),
                if_neg (by omega : -(b : ℤ) ≠ index), zero_add]
          · let a := index.natAbs
            have hindex : index = -(a : ℤ) := by dsimp [a]; omega
            have hexp : (if 0 ≤ index then index.toNat.choose 2
                else (index.natAbs + 1).choose 2) = (a + 1).choose 2 := by
              by_cases hz : index = 0
              · simp [hz, a]
              · rw [if_neg (by omega)]
            rw [hexp]; change (if degree = (a + 1).choose 2 then (-1 : ℚ) ^ a else 0) = _
            by_cases ha : a < degree + 1
            · rw [Finset.sum_eq_single a]
              · simp only [if_neg (by omega : ((a + 1 : ℕ) : ℤ) ≠ index),
                  if_pos hindex.symm, zero_add]
                split_ifs <;> simp
              · intro b _ hba
                rw [if_neg (by omega : ((b + 1 : ℕ) : ℤ) ≠ index),
                  if_neg (by omega : -(b : ℤ) ≠ index), zero_add]
              · exact fun hout => (hout (Finset.mem_range.mpr ha)).elim
            · have hne : degree ≠ (a + 1).choose 2 := by have := lower a; omega
              rw [if_neg hne]
              symm
              apply Finset.sum_eq_zero; intro b hb; simp only [Finset.mem_range] at hb
              rw [if_neg (by omega : ((b + 1 : ℕ) : ℤ) ≠ index),
                if_neg (by omega : -(b : ℤ) ≠ index), zero_add]
        have hev (p : PowerSeries ℚ) :
            PowerSeries.map ev (PowerSeries.map LaurentPolynomial.C p) = p := by
          ext n; simp [coeff_map, ev]
        rw [show pentagonalSeries ℚ * PowerSeries.map ev formalTheta =
            PowerSeries.map ev weighted by dsimp only [weighted]; rw [map_mul, hev],
          coeff_map, folded,
          map_sum]
        simp only [ev, map_mul, map_add, LaurentPolynomial.eval₂_C, RingHom.id_apply,
          LaurentPolynomial.eval₂_T_n, LaurentPolynomial.eval₂_T_neg_n,
          Units.val_neg, Units.val_one, inv_neg, inv_one]
        have hsign (a : ℕ) : ((-1 : ℚ) ^ a) ^ 2 = 1 := by
          rw [← pow_mul, Nat.mul_comm a 2, pow_mul]; norm_num
        conv_lhs =>
          arg 2
          ext a
          rw [show (-1 : ℚ) ^ (a + 1) * (-1) ^ (a + 1) = 1 by
            simpa only [pow_two] using hsign (a + 1),
            show (-1 : ℚ) ^ a * (-1) ^ a = 1 by simpa only [pow_two] using hsign a]
          simp
        rw [← Finset.sum_boole (fun a => (a + 1).choose 2 = degree)
          (Finset.range (degree + 1)), Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        by_cases h : degree = (a + 1).choose 2
        · rw [if_pos h, if_pos h.symm]; norm_num
        · rw [if_neg h, if_neg (Ne.symm h)]; norm_num
      have heuler (degree cutoff : ℕ) (hlarge : degree < cutoff) :
          coeff degree (PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1))
            formalTheta) = coeff degree ((2 : PowerSeries ℚ) *
              (∏ i ∈ Finset.range cutoff, (1 + X ^ (i + 1))) ^ 2) := by
        classical
        let ev : LaurentPolynomial ℚ →+* ℚ := LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1)
        let q : PowerSeries ℚ := X
        let finite (shift cutoff : ℕ) : PowerSeries ℚ :=
          ∏ earlier ∈ Finset.range cutoff, (1 + q ^ (earlier + shift))
        let expansion (shift : ℕ) : PowerSeries ℚ :=
          PowerSeries.mk fun degree => ∑ index ∈ Finset.range (degree + 2),
            PowerSeries.coeff degree (q ^ (shift * index) * eulerCoefficients index) * (-1)^index
        let polynomial (cutoff : ℕ) : Polynomial (PowerSeries ℚ) :=
          ∏ earlier ∈ Finset.range cutoff,
            (1 - Polynomial.C (q ^ earlier) * Polynomial.X)
        have hpolyStep (cutoff : ℕ) : polynomial (cutoff + 1) = polynomial cutoff *
            (1 - Polynomial.C (q ^ cutoff) * Polynomial.X) :=
          Finset.prod_range_succ _ cutoff
        have hpolyStable (base extra degree index : ℕ) (hsmall : degree < base) :
            PowerSeries.coeff degree ((polynomial (base + extra)).coeff index) =
              PowerSeries.coeff degree ((polynomial base).coeff index) := by
          induction extra with
          | zero => simp
          | succ extra ih =>
              rw [show base + (extra + 1) = base + extra + 1 by omega, hpolyStep]
              rw [mul_sub, mul_one, Polynomial.coeff_sub, map_sub]
              have hzero : PowerSeries.coeff degree
                  ((polynomial (base + extra) *
                    (Polynomial.C (q ^ (base + extra)) * Polynomial.X)).coeff index) = 0 := by
                rw [show polynomial (base + extra) *
                    (Polynomial.C (q ^ (base + extra)) * Polynomial.X) =
                      Polynomial.C (q ^ (base + extra)) *
                        (polynomial (base + extra) * Polynomial.X) by ring,
                  Polynomial.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
              rw [hzero, sub_zero, ih]
        have hcolumn (degree cutoff index : ℕ) (hlarge : degree < cutoff) :
            PowerSeries.coeff degree ((polynomial cutoff).coeff index) =
              PowerSeries.coeff degree (eulerCoefficients index) := by
          rw [euler_coefficient_construction.2.2.2.1 index, PowerSeries.coeff_mk]
          rw [show cutoff = degree + 1 + (cutoff - (degree + 1)) by omega]
          exact hpolyStable (degree + 1) _ degree index (by omega)
        have hfiniteStable (shift base extra degree : ℕ) (hsmall : degree < base) :
            PowerSeries.coeff degree (finite shift (base + extra)) =
              PowerSeries.coeff degree (finite shift base) := by
          induction extra with
          | zero => simp
          | succ extra ih =>
              rw [show base + (extra + 1) = base + extra + 1 by omega]
              change PowerSeries.coeff degree
                ((∏ earlier ∈ Finset.range (base + extra + 1), _) : PowerSeries ℚ) = _
              rw [Finset.prod_range_succ, mul_add, mul_one, map_add]
              have hzero : PowerSeries.coeff degree
                  (finite shift (base + extra) * q ^ (base + extra + shift)) = 0 := by
                rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
              change PowerSeries.coeff degree (finite shift (base + extra)) + _ = _
              rw [hzero, add_zero, ih]
        have hfiniteCoeff (shift degree cutoff : ℕ) (hlarge : degree < cutoff) :
            PowerSeries.coeff degree (finite shift cutoff) =
              PowerSeries.coeff degree (expansion shift) := by
          have hdegree : (polynomial (degree + 1)).natDegree < degree + 2 := by
            have hbound : (polynomial (degree + 1)).natDegree ≤ degree + 1 := by
              apply (Polynomial.natDegree_prod_le _ _).trans
              calc
                _ ≤ ∑ _earlier ∈ Finset.range (degree + 1), 1 := by
                  apply Finset.sum_le_sum; intro earlier _
                  exact (Polynomial.natDegree_sub_le _ _).trans
                    (by simpa using Polynomial.natDegree_C_mul_le (q ^ earlier) Polynomial.X)
                _ = degree + 1 := by simp
            omega
          have heval : finite shift (degree + 1) =
              (polynomial (degree + 1)).eval (-q ^ shift) := by
            dsimp only [finite, polynomial]; rw [Polynomial.eval_prod]
            apply Finset.prod_congr rfl; intro earlier _
            simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_X]
            rw [mul_neg, sub_neg_eq_add, ← pow_add]
          rw [show cutoff = degree + 1 + (cutoff - (degree + 1)) by omega,
            hfiniteStable shift (degree + 1) _ degree (by omega), heval,
            Polynomial.eval_eq_sum_range' hdegree, map_sum]
          dsimp only [expansion]; rw [PowerSeries.coeff_mk]
          apply Finset.sum_congr rfl; intro index _; rw [neg_pow, ← pow_mul]
          rw [show (polynomial (degree + 1)).coeff index *
              ((-1 : PowerSeries ℚ) ^ index * q ^ (shift * index)) =
                q ^ (shift * index) * (polynomial (degree + 1)).coeff index * C ((-1)^index)
            by
              have hc : C ((-1 : ℚ) ^ index) = (-1 : PowerSeries ℚ) ^ index := by
                rw [map_pow, map_neg, map_one]
              rw [hc]
              ring]
          rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow_mul',
            PowerSeries.coeff_X_pow_mul']
          split_ifs with hle
          · rw [hcolumn _ (degree + 1) index (by omega)]
          · simp
        have hraw : PowerSeries.map ev formalTheta = expansion 0 * expansion 1 := by
          rw [formalTheta, map_mul]; congr 1
          · apply PowerSeries.ext
            intro degree
            simp only [PowerSeries.coeff_map, eulerLaurentExpansion, PowerSeries.coeff_mk,
              map_sum, expansion, Nat.zero_mul, pow_zero, one_mul]
            apply Finset.sum_congr rfl; intro i _; simp [ev]
          · apply PowerSeries.ext
            intro degree
            simp only [PowerSeries.coeff_map, shiftedEulerFactor, PowerSeries.coeff_mk,
              map_sum, expansion, Nat.one_mul]
            apply Finset.sum_congr rfl; intro index _
            change ev (LaurentPolynomial.invert
              (LaurentPolynomial.C _ * LaurentPolynomial.T (index : ℤ))) = _
            rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
            have hsign : ((-1 : ℚ) ^ index)⁻¹ = (-1 : ℚ) ^ index := by
              rw [← inv_pow]; norm_num
            simpa [ev, q] using
              congrArg (fun z => coeff degree (q ^ index * eulerCoefficients index) * z) hsign
        rw [hraw]
        have heq : ∀ d ≤ degree, coeff d (finite 0 (cutoff + 1)) =
            coeff d ((2 : PowerSeries ℚ) * finite 1 cutoff) := by
          intro d hd
          have hf : finite 0 (cutoff + 1) = (2 : PowerSeries ℚ) * finite 1 cutoff := by
            dsimp only [finite]; rw [Finset.prod_range_succ']
            simp only [Nat.add_zero, pow_zero]; rw [mul_comm]; norm_num
          rw [hf]
        rw [coeff_mul, pow_two, ← mul_assoc, coeff_mul]; apply Finset.sum_congr rfl; intro p hp
        have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [← hfiniteCoeff 0 p.1 (cutoff + 1) (by omega), heq p.1 (by omega),
          ← hfiniteCoeff 1 p.2 cutoff (by omega)]
      have hproducts (degree cutoff : ℕ) (hlarge : degree < cutoff) :
          coeff degree (∏ i ∈ Finset.range cutoff,
            ((1 - (X : PowerSeries ℚ) ^ (2*i+2)) *
              PowerSeries.map (Int.castRingHom ℚ) (geom (2*i+1)))) =
          coeff degree ((∏ i ∈ Finset.range (2*cutoff),
            (1 - (X : PowerSeries ℚ) ^ (i+1))) *
            (∏ i ∈ Finset.range (2*cutoff),
              (1 + (X : PowerSeries ℚ) ^ (i+1)))^2) := by
        classical
        let q : PowerSeries ℚ := X
        let g (e : ℕ) := PowerSeries.map (Int.castRingHom ℚ) (geom e)
        let P (B : ℕ) := ∏ i ∈ Finset.range B, (1-q^(i+1))
        let E (B : ℕ) := ∏ i ∈ Finset.range B, (1-q^(2*i+2))
        let F (B : ℕ) := ∏ i ∈ Finset.range B, (1+q^(i+1))
        let G (B : ℕ) := ∏ i ∈ Finset.range B, g (i+1)
        let O (B : ℕ) := ∏ i ∈ Finset.range B, g (2*i+1)
        have hgeom (e : ℕ) (he : 0 < e) : g e * (1 - q ^ e) = 1 := by
          have h : geom e * (1 - (X : PowerSeries ℤ)^e) = 1 := by
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
          have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) h
          simpa [g, q] using hmap
        have hPG (B : ℕ) : P B * G B = 1 := by
          dsimp only [P,G]; rw [← Finset.prod_mul_distrib]; apply Finset.prod_eq_one; intro i _
          rw [mul_comm, hgeom (i+1) (by omega)]
        have hPF (B : ℕ) : P B * F B = E B := by
          dsimp only [P,F,E]; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _
          rw [show 2*i+2=(i+1)*2 by omega, pow_mul]
          ring
        have hGE (B : ℕ) : G (2*B) * E B = O B := by
          have hpair : ∀ B, G (2*B) =
              ∏ i ∈ Finset.range B, g (2*i+1) * g (2*i+2) := by
            intro B
            induction B with
            | zero => simp [G]
            | succ B ih =>
              rw [show 2*(B+1)=2*B+1+1 by omega]
              dsimp only [G] at ih ⊢
              rw [Finset.prod_range_succ, Finset.prod_range_succ, ih,
                Finset.prod_range_succ]
              ring
          rw [hpair]; dsimp only [E,O]; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl
          intro i _; rw [mul_assoc, hgeom (2*i+2) (by omega), mul_one]
        have hEStable (base extra t : ℕ) (ht : t < base) :
            coeff t (E (base+extra)) = coeff t (E base) := by
          induction extra with
          | zero => simp
          | succ extra ih =>
            rw [show base+(extra+1)=base+extra+1 by omega]
            dsimp only [E]
            rw [Finset.prod_range_succ, mul_sub, mul_one, map_sub, coeff_mul_X_pow',
              if_neg (by omega), sub_zero]
            exact ih
        have hmult (a b c d : PowerSeries ℚ) (ha : ∀ t ≤ degree, coeff t a=coeff t b)
            (hc : ∀ t ≤ degree, coeff t c=coeff t d) :
            ∀ t ≤ degree, coeff t (a*c)=coeff t (b*d) := by
          intro t ht; rw [coeff_mul, coeff_mul]; apply Finset.sum_congr rfl; intro p hp
          have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          rw [ha p.1 (by omega), hc p.2 (by omega)]
        have hstable : ∀ t ≤ degree,
            coeff t (E (2*cutoff))=coeff t (E cutoff) := by
          intro t ht
          rw [show 2*cutoff=cutoff+cutoff by omega]
          exact hEStable _ _ _ (by omega)
        rw [Finset.prod_mul_distrib]; change coeff degree (E cutoff*O cutoff) =
          coeff degree (P (2*cutoff)*F (2*cutoff)^2)
        have hr (B : ℕ) : P B * F B^2=E B^2*G B := by
          have hu := hPG B
          have he := hPF B
          calc
            _ = E B * F B := by rw [pow_two, ←mul_assoc, hPF]
            _ = E B * F B * (P B * G B) := by rw [hu,mul_one]
            _ = E B * (P B * F B) * G B := by ring
            _ = E B^2*G B := by rw [he];ring
        rw [hr]
        have hreplace := hmult _ _ (G (2*cutoff)) (G (2*cutoff))
          (hmult _ _ _ _ hstable hstable) (fun _ _ => rfl) degree (by omega)
        rw [pow_two, hreplace]; congr 1
        calc
          E cutoff*O cutoff =
              E cutoff*(G (2*cutoff)*E cutoff) := by rw [hGE]
          _ = _ := by ring
      have hpentagonal (degree cutoff : ℕ) (hlarge : degree < cutoff) :
          coeff degree (∏ i ∈ Finset.range cutoff,
            (1-(X : PowerSeries ℚ)^(i+1))) = coeff degree (pentagonalSeries ℚ) := by
        classical
        obtain ⟨s, hs⟩ := Filter.eventually_atTop.mp
          (PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℚ degree)
        have hread := hs (s ∪ Finset.range cutoff) Finset.subset_union_left
        rw [← Finset.prod_sdiff Finset.subset_union_right] at hread
        have hignore (extras : Finset ℕ) (he : ∀ i ∈ extras, cutoff ≤ i)
            (series : PowerSeries ℚ) :
            coeff degree ((∏ i ∈ extras, (1-X^(i+1)))*series) = coeff degree series := by
          induction extras using Finset.induction_on with
          | empty => simp
          | @insert a extras ha ih =>
            rw [Finset.prod_insert ha]
            have habove := he a (Finset.mem_insert_self _ _)
            rw [mul_assoc, mul_comm (1-X^(a+1)), mul_sub, mul_one, map_sub,
              coeff_mul_X_pow', if_neg (by omega), sub_zero]
            exact ih (fun i hi => he i (Finset.mem_insert_of_mem hi))
        rw [hignore _ (by
          intro i hi
          have hnot := (Finset.mem_sdiff.mp hi).2
          simpa using hnot)] at hread
        exact hread
      let B := 2*(N+1)
      let P : PowerSeries ℚ := ∏ i ∈ Finset.range B, (1-X^(i+1))
      let F : PowerSeries ℚ := ∏ i ∈ Finset.range B, (1+X^(i+1))
      let ev : LaurentPolynomial ℚ →+* ℚ := LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1)
      have hfold : coeff n (pentagonalSeries ℚ * PowerSeries.map ev formalTheta) =
          2*coeff n (P*F^2) := by
        calc
          _ = coeff n (P*((2 : PowerSeries ℚ)*F^2)) := by
            rw [coeff_mul,coeff_mul]; apply Finset.sum_congr rfl; intro p hp
            have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
            rw [←hpentagonal p.1 B (by dsimp [B];omega), heuler p.2 B (by dsimp [B];omega)]
          _ = _ := by
            rw [show P*((2 : PowerSeries ℚ)*F^2)=C (2 : ℚ)*(P*F^2) by
              have htwo : C (2 : ℚ)=(2 : PowerSeries ℚ) := by
                rw [show (2 : ℚ)=1+1 by norm_num,map_add,map_one]
                norm_num
              rw [htwo]; ring,
              coeff_C_mul]
      have hc := hcore n
      change coeff n (pentagonalSeries ℚ*PowerSeries.map ev formalTheta)=_ at hc; rw [hfold] at hc
      have hq : coeff n (∏ i ∈ Finset.range (N+1),
          ((1-(X : PowerSeries ℚ)^(2*i+2))*PowerSeries.map (Int.castRingHom ℚ)
            (geom (2*i+1)))) =
          (((Finset.range (n+1)).filter (fun a => (a+1).choose 2=n)).card : ℚ) := by
        rw [hproducts n (N+1) (by omega)]; change coeff n (P*F^2)=_
        linarith
      have hcast : ((coeff n (∏ i ∈ Finset.range (N+1),
          ((1-(X : PowerSeries ℤ)^(2*i+2))*geom (2*i+1))) : ℤ) : ℚ) =
          coeff n (∏ i ∈ Finset.range (N+1),
            ((1-(X : PowerSeries ℚ)^(2*i+2))*PowerSeries.map (Int.castRingHom ℚ)
              (geom (2*i+1)))) := by
        have hm := coeff_map (Int.castRingHom ℚ) n (∏ i ∈ Finset.range (N+1),
          ((1-(X : PowerSeries ℤ)^(2*i+2))*geom (2*i+1)))
        simpa [map_prod] using hm.symm
      rw [←hcast] at hq
      exact_mod_cast hq
    classical
    let A : PowerSeries ℤ := ∏ i ∈ Finset.range (N+1),
      ((1-X^(2*i+2))*geom (2*i+1))
    let ψ : PowerSeries ℤ := ∑ a ∈ Finset.range (n+1), X^((a+1).choose 2)
    have htri (a : ℕ) : a ≤ (a+1).choose 2 := by
      induction a with
      | zero => simp
      | succ a ih => rw [Nat.choose_succ_succ,Nat.choose_one_right]; omega
    have heq : ∀ d ≤ n, coeff d A=coeff d ψ := by
      intro d hd
      change coeff d (∏ i ∈ Finset.range (N+1),
        ((1-(X : PowerSeries ℤ)^(2*i+2))*geom (2*i+1))) = _
      rw [hgauss d N (by omega)]; dsimp only [ψ]; rw [map_sum]; simp only [coeff_X_pow]
      rw [←Finset.sum_boole (fun a => (a+1).choose 2=d) (Finset.range (d+1))]
      simp only [eq_comm]
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega)); intro a ha hanot
      have hlarge : d<a := by simpa using hanot
      have := htri a
      rw [if_neg (by omega)]
    have hmul (a b c d : PowerSeries ℤ) (ha : ∀ t ≤ n, coeff t a=coeff t b)
        (hc : ∀ t ≤ n, coeff t c=coeff t d) :
        ∀ t ≤ n, coeff t (a*c)=coeff t (b*d) := by
      intro t ht; rw [coeff_mul,coeff_mul]; apply Finset.sum_congr rfl; intro p hp
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [ha p.1 (by omega),hc p.2 (by omega)]
    have hunit : geom 2*(1-(X : PowerSeries ℤ)^2)=1 := by
      apply PowerSeries.ext; intro t
      rw [mul_sub,mul_one,map_sub,coeff_mul_X_pow']; simp only [geom,coeff_mk]
      by_cases ht : 2≤t
      · rw [if_pos ht]
        have hd : 2 ∣ t-2 ↔ 2 ∣ t := by omega
        have hz : t≠0 := by omega
        simp [hd,coeff_one,hz]
      · interval_cases t <;> simp [coeff_one]
    let E (K : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range K, (1-X^(2*i+2))
    let H (K : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range K, (1-X^(2*i+4))
    let O (K : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range K, geom (2*i+1)
    have hshift (K : ℕ) : H K*(1-X^2)=E K*(1-X^(2*K+2)) := by
      have hf := (Finset.prod_range_succ'
        (fun i => (1-(X : PowerSeries ℤ)^(2*i+2))) K).symm.trans
        (Finset.prod_range_succ _ K)
      simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using hf
    have hH : H (N+1)=E (N+1)*(1-X^(2*N+4))*geom 2 := by
      calc
        _ = H (N+1)*(geom 2*(1-X^2)) := by rw [hunit,mul_one]
        _ = (H (N+1)*(1-X^2))*geom 2 := by ring
        _ = _ := by rw [hshift,show 2*(N+1)+2=2*N+4 by omega]
    have hD : (∏ i ∈ Finset.range (N+1),
        ((1-(X : PowerSeries ℤ)^(2+2*i))*(1-X^(4+2*i))*geom (1+2*i)^2)) =
        A^2*geom 2*(1-X^(2*N+4)) := by
      simp only [show ∀ i, 2+2*i=2*i+2 by omega,
        show ∀ i, 4+2*i=2*i+4 by omega,show ∀ i, 1+2*i=2*i+1 by omega]
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_pow]
      change E (N+1)*H (N+1)*O (N+1)^2 = _; rw [hH]
      have hA : A=E (N+1)*O (N+1) := Finset.prod_mul_distrib
      rw [hA]; ring
    rw [hD,mul_sub,mul_one,map_sub,coeff_mul_X_pow',if_neg (by omega),sub_zero]
    simp only [pow_two] at *
    have hcoeff := hmul _ _ (geom 2) (geom 2) (hmul _ _ _ _ heq heq)
      (fun _ _ => rfl) n (by omega)
    rw [hcoeff]; dsimp only [ψ]
    rw [Finset.sum_mul,Finset.sum_mul]; simp only [Finset.mul_sum,Finset.sum_mul]
    simp_rw [←pow_add]; rw [map_sum]; simp only [map_sum,coeff_X_pow_mul',geom,coeff_mk]
    rw [←Finset.sum_boole (fun p : ℕ×ℕ =>
      (p.1+1).choose 2+(p.2+1).choose 2 ≤ n ∧
        ((p.1+1).choose 2+(p.2+1).choose 2)%2=n%2)
      (Finset.range (n+1) ×ˢ Finset.range (n+1)),Finset.sum_product]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
    by_cases hle : (a+1).choose 2+(b+1).choose 2≤n
    · have hpar : 2 ∣ n-((a+1).choose 2+(b+1).choose 2) ↔
          ((a+1).choose 2+(b+1).choose 2)%2=n%2 := by omega
      simp [hle,hpar]
    · simp [hle]
  have hpair_bound (n : ℕ) (hn : 5 ≤ n) (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, (p.1 + 1).choose 2 + (p.2 + 1).choose 2 ≤ n ∧
      ((p.1 + 1).choose 2 + (p.2 + 1).choose 2) % 2 = n % 2) :
    (s.card : ℝ) ≤ 97 / 120 * (n : ℝ) +
      27 / 32 * Real.sqrt (2 * (n : ℝ) + 1 / 2) + 13 / 25 := by
    have hcount :
      (s.card : ℝ) ≤ ∑ a ∈ range (⌊Real.sqrt (2 * (n : ℝ) + 1 / 2) + 1 / 2⌋₊),
        (Real.sqrt ((Real.sqrt (2 * (n : ℝ) + 1 / 2)) ^ 2 -
          ((a : ℝ) + 1 / 2) ^ 2) / 2 + 3 / 4) := by
      classical
      have htriN (a : ℕ) : 2 * (a + 1).choose 2 = a * (a + 1) := by
        rw [Nat.choose_two_right, Nat.add_sub_cancel]
        have hd : 2 ∣ a * (a + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self a)
        simpa only [Nat.mul_comm] using Nat.mul_div_cancel' hd
      have htriR (a : ℕ) : 2 * ((a + 1).choose 2 : ℝ) = (a : ℝ) * (a + 1) := by
        exact_mod_cast htriN a
      have hparity (b c : ℕ) (hq : b / 2 = c / 2)
          (hp : ((b + 1).choose 2) % 2 = ((c + 1).choose 2) % 2) : b = c := by
        have hstep (a : ℕ) : (a + 2).choose 2 = (a + 1).choose 2 + a + 1 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Nat.choose_succ_succ' (a + 1) 1
        have hadj : b = c ∨ b + 1 = c ∨ c + 1 = b := by omega
        rcases hadj with h | h | h
        · exact h
        · have hs := hstep b
          rw [← h, show b + 1 + 1 = b + 2 by omega] at hp
          omega
        · have hs := hstep c
          rw [← h, show c + 1 + 1 = c + 2 by omega] at hp
          omega
      let R : ℝ := Real.sqrt (2 * (n : ℝ) + 1 / 2)
      let r : ℕ := ⌊R + 1 / 2⌋₊
      have hR0 : 0 ≤ R := Real.sqrt_nonneg _
      have hR2 : R ^ 2 = 2 * (n : ℝ) + 1 / 2 := Real.sq_sqrt (by positivity)
      have hab (p : ℕ × ℕ) (hp : p ∈ s) :
          ((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2 ≤ R ^ 2 := by
        have hsum : ((p.1 + 1).choose 2 : ℝ) + ((p.2 + 1).choose 2 : ℝ) ≤ n := by
          exact_mod_cast (hs p hp).1
        have ha := htriR p.1
        have hb := htriR p.2
        nlinarith
      have hrow (p : ℕ × ℕ) (hp : p ∈ s) : p.1 < r := by
        have hpR : (p.1 : ℝ) + 1 / 2 ≤ R := by
          have h := hab p hp
          nlinarith [sq_nonneg ((p.2 : ℝ) + 1 / 2)]
        have hp1 : ((p.1 + 1 : ℕ) : ℝ) ≤ R + 1 / 2 := by push_cast; linarith
        have hfloor := (Nat.le_floor_iff (by positivity : 0 ≤ R + 1 / 2)).mpr hp1
        dsimp [r]; omega
      have hfiber : s.card = ∑ a ∈ range r, (s.filter (fun p => p.1 = a)).card := by
        exact Finset.card_eq_sum_card_fiberwise fun p hp => Finset.mem_range.mpr (hrow p hp)
      have hbound (a : ℕ) (ha : a ∈ range r) :
          ((s.filter (fun p => p.1 = a)).card : ℝ) ≤
            Real.sqrt (R ^ 2 - ((a : ℝ) + 1 / 2) ^ 2) / 2 + 3 / 4 := by
        let H : ℝ := Real.sqrt (R ^ 2 - ((a : ℝ) + 1 / 2) ^ 2)
        let L : ℕ := ⌊H + 1 / 2⌋₊
        have hH0 : 0 ≤ H := Real.sqrt_nonneg _
        have hsize (p : ℕ × ℕ) (hp : p ∈ s.filter (fun p => p.1 = a)) : p.2 < L := by
          obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
          have habp := hab p hp
          rw [hpa] at habp
          have hbH : (p.2 : ℝ) + 1 / 2 ≤ H := by
            apply Real.le_sqrt_of_sq_le; nlinarith
          have hb1 : ((p.2 + 1 : ℕ) : ℝ) ≤ H + 1 / 2 := by push_cast; linarith
          have hfloor := (Nat.le_floor_iff (by positivity : 0 ≤ H + 1 / 2)).mpr hb1
          dsimp [L]; omega
        have hmap : Set.MapsTo (fun p : ℕ × ℕ => p.2 / 2)
            (s.filter (fun p => p.1 = a)) (range ((L + 1) / 2)) := by
          intro p hp; apply Finset.mem_range.mpr
          have hpL := hsize p hp
          change p.2 / 2 < (L + 1) / 2; omega
        have hinj : ((s.filter (fun p => p.1 = a)) : Set (ℕ × ℕ)).InjOn
            (fun p => p.2 / 2) := by
          intro p hp q hq hpq
          obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
          obtain ⟨hq, hqa⟩ := Finset.mem_filter.mp hq
          apply Prod.ext
          · omega
          · apply hparity _ _ hpq
            have hpp := (hs p hp).2
            have hqp := (hs q hq).2
            rw [hpa] at hpp; rw [hqa] at hqp; omega
        have hcard := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 / 2) hmap hinj
        rw [Finset.card_range] at hcard
        have hdiv : 2 * ((L + 1) / 2) ≤ L + 1 := Nat.mul_div_le _ _
        have hdivR : 2 * (((L + 1) / 2 : ℕ) : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast hdiv
        have hcardR : ((s.filter (fun p => p.1 = a)).card : ℝ) ≤ ((L + 1) / 2 : ℕ) := by
          exact_mod_cast hcard
        have hLR : (L : ℝ) ≤ H + 1 / 2 := Nat.floor_le (by positivity)
        change _ ≤ H / 2 + 3 / 4
        linarith
      have hfiberR : (s.card : ℝ) =
          ∑ a ∈ range r, ((s.filter (fun p => p.1 = a)).card : ℝ) := by exact_mod_cast hfiber
      rw [hfiberR]; exact Finset.sum_le_sum hbound
    have hpoly (R : ℝ) (hR : 3 ≤ R) (r : ℕ) (hr : (r : ℝ) ≤ R + 1 / 2) :
      (∑ a ∈ range r, (Real.sqrt (R ^ 2 - ((a : ℝ) + 1 / 2) ^ 2) / 2 + 3 / 4)) ≤
        97 / 240 * R ^ 2 + 27 / 32 * R + 5 / 16 + 1 / (480 * R ^ 2) := by
      have hRpos : 0 < R := by linarith
      have hRne : R ≠ 0 := ne_of_gt hRpos
      have hs2 (u : ℕ) : (∑ a ∈ range u, ((a : ℝ) + 1 / 2) ^ 2) =
          (u : ℝ) * (4 * (u : ℝ) ^ 2 - 1) / 12 := by
        induction u with
        | zero => simp
        | succ u ih =>
          rw [Finset.sum_range_succ, ih]; push_cast; ring
      have hs4 (u : ℕ) : (∑ a ∈ range u, ((a : ℝ) + 1 / 2) ^ 4) =
          (u : ℝ) * (48 * (u : ℝ) ^ 4 - 40 * (u : ℝ) ^ 2 + 7) / 240 := by
        induction u with
        | zero => simp
        | succ u ih =>
          rw [Finset.sum_range_succ, ih]; push_cast; ring
      let F : ℝ → ℝ := fun t => t * R - t * (4 * t ^ 2 - 1) / (24 * R) -
        t * (48 * t ^ 4 - 40 * t ^ 2 + 7) / (1920 * R ^ 3)
      have hmajorant (x : ℝ) (hx : 0 ≤ x) (hxR : x ≤ R) :
          Real.sqrt (R ^ 2 - x ^ 2) ≤ R - x ^ 2 / (2 * R) - x ^ 4 / (8 * R ^ 3) := by
        have h2 : x ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hx hxR 2
        have h4 : x ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ hx hxR 4
        have hb2 : x ^ 2 / (2 * R) ≤ R / 2 := by
          apply (div_le_iff₀ (by positivity)).mpr; nlinarith
        have hb4 : x ^ 4 / (8 * R ^ 3) ≤ R / 8 := by
          apply (div_le_iff₀ (by positivity)).mpr; nlinarith
        apply Real.sqrt_le_iff.mpr
        constructor
        · linarith
        · have hid : (R - x ^ 2 / (2 * R) - x ^ 4 / (8 * R ^ 3)) ^ 2 -
              (R ^ 2 - x ^ 2) = x ^ 6 / (8 * R ^ 4) + x ^ 8 / (64 * R ^ 6) := by
            field_simp; ring
          have hnon : 0 ≤ x ^ 6 / (8 * R ^ 4) + x ^ 8 / (64 * R ^ 6) := by positivity
          linarith
      have hsum : (∑ a ∈ range r,
          ((R - ((a : ℝ) + 1 / 2) ^ 2 / (2 * R) -
            ((a : ℝ) + 1 / 2) ^ 4 / (8 * R ^ 3)) / 2 + 3 / 4)) =
            F r / 2 + 3 / 4 * r := by
        have hdivsum (f : ℕ → ℝ) (c : ℝ) :
            (∑ a ∈ range r, f a / c) = (∑ a ∈ range r, f a) / c := by
          simp only [div_eq_mul_inv, Finset.sum_mul]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hdivsum,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, hs2, hs4]
        dsimp [F]; ring
      have hmono (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ R + 1 / 2) : F s ≤ F t := by
        have ht0 : 0 ≤ t := hs.trans hst
        let U : ℝ := 7 * R / 6
        have hU : 0 ≤ U := by dsimp [U]; positivity
        have htU : t ≤ U := by dsimp [U]; linarith
        have hsU : s ≤ U := hst.trans htU
        have hmon (p q : ℕ) : t ^ p * s ^ q ≤ U ^ (p + q) := by
          calc
            _ ≤ U ^ p * U ^ q := mul_le_mul (pow_le_pow_left₀ ht0 htU p)
              (pow_le_pow_left₀ hs hsU q) (pow_nonneg hs q) (pow_nonneg hU p)
            _ = _ := (pow_add _ _ _).symm
        have h20 := hmon 2 0
        have h11 := hmon 1 1
        have h02 := hmon 0 2
        have h40 := hmon 4 0
        have h31 := hmon 3 1
        have h22 := hmon 2 2
        have h13 := hmon 1 3
        have h04 := hmon 0 4
        norm_num only [pow_zero, pow_one, mul_one, one_mul, Nat.reduceAdd] at h20 h11 h02
        norm_num only [pow_zero, pow_one, mul_one, one_mul, Nat.reduceAdd] at h40 h31 h22 h13 h04
        have hp2 : t ^ 2 + t * s + s ^ 2 ≤ 49 / 12 * R ^ 2 := by
          dsimp [U] at h20 h11 h02; nlinarith
        have hp4 : t ^ 4 + t ^ 3 * s + t ^ 2 * s ^ 2 + t * s ^ 3 + s ^ 4 ≤
            12005 / 1296 * R ^ 4 := by
          dsimp [U] at h40 h31 h22 h13 h04; nlinarith
        have hp2R := mul_le_mul_of_nonneg_right hp2 (sq_nonneg R)
        have hp2pos : 0 ≤ t ^ 2 + t * s + s ^ 2 := by positivity
        have hR4 : 81 ≤ R ^ 4 := by
          have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hR 4
          norm_num at h; exact h
        have hnum : 0 ≤ 1920 * R ^ 4 - 320 * R ^ 2 * (t ^ 2 + t * s + s ^ 2) +
            80 * R ^ 2 - 48 * (t ^ 4 + t ^ 3 * s + t ^ 2 * s ^ 2 + t * s ^ 3 + s ^ 4) +
            40 * (t ^ 2 + t * s + s ^ 2) - 7 := by nlinarith [sq_nonneg R]
        have hdifference : F t - F s = (t - s) / (1920 * R ^ 3) *
            (1920 * R ^ 4 - 320 * R ^ 2 * (t ^ 2 + t * s + s ^ 2) + 80 * R ^ 2 -
              48 * (t ^ 4 + t ^ 3 * s + t ^ 2 * s ^ 2 + t * s ^ 3 + s ^ 4) +
              40 * (t ^ 2 + t * s + s ^ 2) - 7) := by
          dsimp [F]; field_simp; ring
        have hdiff0 : 0 ≤ F t - F s := by
          rw [hdifference]; exact mul_nonneg (div_nonneg (sub_nonneg.mpr hst) (by positivity)) hnum
        linarith
      have hendpoint : F (R + 1 / 2) / 2 + 3 / 4 * (R + 1 / 2) =
          97 / 240 * R ^ 2 + 27 / 32 * R + 5 / 16 + 1 / (480 * R ^ 2) := by
        dsimp [F]; field_simp; ring
      calc
        _ ≤ ∑ a ∈ range r,
            ((R - ((a : ℝ) + 1 / 2) ^ 2 / (2 * R) -
              ((a : ℝ) + 1 / 2) ^ 4 / (8 * R ^ 3)) / 2 + 3 / 4) := by
          apply Finset.sum_le_sum; intro a ha
          have ha1 : ((a : ℝ) + 1) ≤ r := by exact_mod_cast (Finset.mem_range.mp ha)
          have haR : (a : ℝ) + 1 / 2 ≤ R := by linarith
          have h := hmajorant ((a : ℝ) + 1 / 2) (by positivity) haR
          linarith
        _ = F r / 2 + 3 / 4 * r := hsum
        _ ≤ F (R + 1 / 2) / 2 + 3 / 4 * (R + 1 / 2) := by
          have hm := hmono r (R + 1 / 2) (by positivity) hr le_rfl
          linarith
        _ = _ := hendpoint
    let R : ℝ := Real.sqrt (2 * (n : ℝ) + 1 / 2)
    have hR : 3 ≤ R := by
      apply Real.le_sqrt_of_sq_le
      have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hRpos : 0 < R := by linarith
    have hR2 : R ^ 2 = 2 * (n : ℝ) + 1 / 2 := Real.sq_sqrt (by positivity)
    have hR2ge : 9 ≤ R ^ 2 := by nlinarith
    have hfrac : 1 / (480 * R ^ 2) ≤ (1 : ℝ) / 4320 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr; nlinarith
    have hr : (⌊R + 1 / 2⌋₊ : ℝ) ≤ R + 1 / 2 := Nat.floor_le (by positivity)
    have hp := hpoly R hR (⌊R + 1 / 2⌋₊) hr
    have he := hcount.trans hp
    change (s.card : ℝ) ≤ 97 / 120 * (n : ℝ) + 27 / 32 * R + 13 / 25; nlinarith
  dsimp only
  have hp := hcoeff n n le_rfl
  refine ⟨hp, ?_⟩; intro hn; rw [hp]; apply hpair_bound n hn
  intro p hp; exact (Finset.mem_filter.mp hp).2

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds
