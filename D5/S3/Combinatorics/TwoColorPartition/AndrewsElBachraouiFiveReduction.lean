/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction
   mirror-E: none(waiver:two-color-partition-eventual-positivity)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Finite nilpotent transformations of the full two-parameter D-prime series. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiHeine
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds

/-! Exact finite identities for the original two-color partition series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction

open PowerSeries Finset AndrewsElBachraouiDefs AndrewsElBachraouiHeine
open scoped BigOperators

private theorem nilpotent_source_reduction {R : Type} [CommRing R]
    (q : R) (N k m : ℕ) (hq : q ^ N = 0)
    (hm : 1 ≤ m) (hmk : m < k) :
    (∑ j ∈ range N, q ^ (2 * m * j) *
      ∏ i ∈ range N,
        (1 - q ^ (2 * j + 2 + 2 * i)) *
        (1 - q ^ (2 * j + 2 * k + 2 * i)) *
        Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2) =
    (∑ r ∈ range N, q ^ r *
      (∏ i ∈ range (m - 1), (1 - q ^ (2 * r + 2 + 2 * i))) *
      (∏ i ∈ range (k - m - 1), (1 - q ^ (2 * r + 2 * m + 1 + 2 * i)))) *
      ∏ i ∈ range (k - 1), Ring.inverse (1 - q ^ (2 * i + 1)) := by
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
  let pre (f : ℕ → Rˣ) (j : ℕ) := ∏ i ∈ range j, f i
  let tail (f : ℕ → Rˣ) (j : ℕ) := ∏ i ∈ range N, f (j + i)
  have htail (f : ℕ → Rˣ) (hf : ∀ i, N ≤ i → f i = 1) (j : ℕ) :
      tail f j = pre f N * (pre f j)⁻¹ := by
    have heq : pre f (j + N) = pre f N := by
      dsimp only [pre]
      rw [show j + N = N + j by omega, prod_range_add]
      simp [hf, show ∀ i, N ≤ N + i by omega]
    have hadd := prod_range_add f j N
    change pre f (j + N) = pre f j * tail f j at hadd
    rw [heq] at hadd
    rw [hadd]
    simp [mul_comm, mul_left_comm]
  let A (r : ℕ) := pre O r * (pre E r)⁻¹
  let B (r : ℕ) := (∏ i ∈ range r, O (i + k - 1)) * (pre E r)⁻¹
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
      ((tail E (j + k - 1) * (tail O j)⁻¹ : Rˣ) : R) =
        ∑ r ∈ range N, q ^ ((2 * j + 1) * r) * (B r : R) := by
    have hb := nilpotent_q_binomial (q ^ (2 * k - 1)) (q ^ 2)
      (q ^ (2 * j + 1)) N hbase (harg _ (by omega))
    have hprod : ((tail E (j + k - 1) * (tail O j)⁻¹ : Rˣ) : R) =
        ∏ i ∈ range N, (1 - q ^ (2 * (j + k - 1 + i) + 2)) *
          Ring.inverse (1 - q ^ (2 * (j + i) + 1)) := by
      dsimp only [tail]
      rw [← prod_inv_distrib, ← prod_mul_distrib, Units.coe_prod]
      simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
    have hB (r : ℕ) : (B r : R) =
        ∏ i ∈ range r, (1 - q ^ (2 * (i + k - 1) + 1)) *
          Ring.inverse (1 - q ^ (2 * i + 2)) := by
      dsimp only [B, pre]
      rw [← prod_inv_distrib, ← prod_mul_distrib, Units.coe_prod]
      simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
    rw [hprod]
    simp_rw [hB]
    simp only [← pow_mul, ← pow_add] at hb
    have hi1 (i : ℕ) : 2 * (j + k - 1 + i) + 2 = 2 * k - 1 + (2 * j + 1) + 2 * i := by omega
    have hi2 (i : ℕ) : 2 * (j + i) + 1 = 2 * j + 1 + 2 * i := by omega
    have hi3 (i : ℕ) : 2 * (i + k - 1) + 1 = 2 * k - 1 + 2 * i := by omega
    have hi4 (i : ℕ) : 2 * i + 2 = 2 * (i + 1) := by omega
    simp_rw [hi1, hi2, hi3, hi4]
    exact hb
  have hsecond (r : ℕ) :
      (∑ j ∈ range N, q ^ ((2 * r + 2 * m) * j) * (A j : R)) =
        ((tail O (r + m) * (tail E (r + m - 1))⁻¹ : Rˣ) : R) := by
    have hb := nilpotent_q_binomial (q ^ 1) (q ^ 2)
      (q ^ (2 * r + 2 * m)) N hbase (harg _ (by omega))
    have hprod : ((tail O (r + m) * (tail E (r + m - 1))⁻¹ : Rˣ) : R) =
        ∏ i ∈ range N, (1 - q ^ (2 * (r + m + i) + 1)) *
          Ring.inverse (1 - q ^ (2 * (r + m - 1 + i) + 2)) := by
      dsimp only [tail]
      rw [← prod_inv_distrib, ← prod_mul_distrib, Units.coe_prod]
      simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
    have hA (j : ℕ) : (A j : R) =
        ∏ i ∈ range j, (1 - q ^ (2 * i + 1)) * Ring.inverse (1 - q ^ (2 * i + 2)) := by
      dsimp only [A, pre]
      rw [← prod_inv_distrib, ← prod_mul_distrib, Units.coe_prod]
      simp only [Units.val_mul, ← Ring.inverse_unit, hE, hO]
    rw [hprod]
    simp_rw [hA]
    simp only [← pow_mul, ← pow_add] at hb
    have hi1 (i : ℕ) : 2 * (r + m + i) + 1 = 1 + (2 * r + 2 * m) + 2 * i := by omega
    have hi2 (i : ℕ) : 2 * (r + m - 1 + i) + 2 = 2 * r + 2 * m + 2 * i := by omega
    have hi3 (i : ℕ) : 2 * i + 1 = 1 + 2 * i := by omega
    have hi4 (i : ℕ) : 2 * i + 2 = 2 * (i + 1) := by omega
    simp_rw [hi1, hi2, hi3, hi4]
    exact hb.symm
  have hcollapse (r : ℕ) :
      K * B r * tail O (r + m) * (tail E (r + m - 1))⁻¹ =
      (∏ i ∈ range (m - 1), E (r + i)) *
      (∏ i ∈ range (k - m - 1), O (r + m + i)) * (pre O (k - 1))⁻¹ := by
    dsimp only [K, B]
    rw [htail O hlargeO, htail E hlargeE]
    have hEsplit : pre E (r + m - 1) =
        pre E r * ∏ i ∈ range (m - 1), E (r + i) := by
      exact (show r + m - 1 = r + (m - 1) by omega) ▸ prod_range_add E r (m - 1)
    have hOleft : pre O (r + (k - 1)) =
        pre O (k - 1) * ∏ i ∈ range r, O (i + k - 1) := by
      dsimp only [pre]
      rw [show r + (k - 1) = k - 1 + r by omega, prod_range_add]
      congr 1
      apply prod_congr rfl
      intro i _
      congr 1
      omega
    have hOright : pre O (r + (k - 1)) =
        pre O (r + m) * ∏ i ∈ range (k - m - 1), O (r + m + i) := by
      dsimp only [pre]
      rw [show r + (k - 1) = r + m + (k - m - 1) by omega, prod_range_add]
    have hOprod : (∏ i ∈ range r, O (i + k - 1)) =
        pre O (r + m) * (∏ i ∈ range (k - m - 1), O (r + m + i)) *
          (pre O (k - 1))⁻¹ := by
      rw [← hOright, hOleft]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [hEsplit, hOprod]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hprod (j : ℕ) :
      (∏ i ∈ range N, (1 - q ^ (2 * j + 2 + 2 * i)) *
        (1 - q ^ (2 * j + 2 * k + 2 * i)) *
        Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2) =
      (P j : R) * ((tail E (j + k - 1) * (tail O j)⁻¹ : Rˣ) : R) := by
    have hp : P j * (tail E (j + k - 1) * (tail O j)⁻¹) =
        ∏ i ∈ range N, E (j + i) * E (j + k - 1 + i) * ((O (j + i))⁻¹) ^ 2 := by
      dsimp only [P, tail]
      rw [prod_mul_distrib, prod_mul_distrib, prod_pow, prod_inv_distrib, pow_two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [← Units.val_mul, hp, Units.coe_prod]
    apply prod_congr rfl
    intro i _
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← Ring.inverse_unit, hE, hO]
    rw [show 2 * (j + i) + 2 = 2 * j + 2 + 2 * i by omega,
      show 2 * (j + k - 1 + i) + 2 = 2 * j + 2 * k + 2 * i by omega,
      show 2 * (j + i) + 1 = 2 * j + 1 + 2 * i by omega]
  calc
    _ = ∑ j ∈ range N, q ^ (2 * m * j) * (K : R) * (A j : R) *
        (∑ r ∈ range N, q ^ ((2 * j + 1) * r) * (B r : R)) := by
      apply sum_congr rfl
      intro j _
      rw [hprod, hfirst, hP, Units.val_mul]
      ring
    _ = ∑ r ∈ range N, q ^ r * (K : R) * (B r : R) *
        (∑ j ∈ range N, q ^ ((2 * r + 2 * m) * j) * (A j : R)) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro j _
      have hexp : 2 * m * j + (2 * j + 1) * r = r + (2 * r + 2 * m) * j := by ring
      calc
        _ = q ^ (2 * m * j + (2 * j + 1) * r) * (K : R) * (A j : R) * (B r : R) := by
          rw [pow_add]; ring
        _ = _ := by rw [hexp, pow_add]; ring
    _ = ∑ r ∈ range N, q ^ r *
        (((∏ i ∈ range (m - 1), E (r + i)) *
          (∏ i ∈ range (k - m - 1), O (r + m + i)) * (pre O (k - 1))⁻¹ : Rˣ) : R) := by
      apply sum_congr rfl
      intro r _
      rw [hsecond]
      have hc := congrArg (fun u : Rˣ => (u : R)) (hcollapse r)
      simp only [Units.val_mul] at hc
      calc
        _ = q ^ r * ((K : R) * (B r : R) * (tail O (r + m) : R) *
            (((tail E (r + m - 1))⁻¹ : Rˣ) : R)) := by
          simp only [Units.val_mul]; ring
        _ = _ := by rw [hc]; simp only [Units.val_mul]
    _ = _ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro r _
      dsimp only [pre]
      simp only [Units.val_mul, Units.coe_prod, ← prod_inv_distrib,
        ← Ring.inverse_unit, hE, hO]
      simp_rw [show ∀ i, 2 * (r + i) + 2 = 2 * r + 2 + 2 * i by omega,
        show ∀ i, 2 * (r + m + i) + 1 = 2 * r + 2 * m + 1 + 2 * i by omega]
      ring


/-- The finite rational term in the source transformation, with its coefficient cutoff. -/
noncomputable def rationalTrunc (k m N : ℕ) : PowerSeries ℤ :=
  (∑ r ∈ range (N + 1), X ^ r *
    (∏ i ∈ range (m - 1), (1 - X ^ (2 * r + 2 + 2 * i))) *
    (∏ i ∈ range (k - m - 1), (1 - X ^ (2 * r + 2 * m + 1 + 2 * i)))) *
    ∏ i ∈ range (k - 1), geom (2 * i + 1)

/-- The product subtracted from the rational term in the source transformation. -/
noncomputable def productTrunc (k N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ range (N + 1),
    (1 - X ^ (2 + 2 * i)) * (1 - X ^ (2 * k + 2 * i)) * geom (1 + 2 * i) ^ 2

/-- The coefficient-defined geometric series is the inverse of its binomial factor. -/
theorem geom_mul_one_sub (e : ℕ) (he : 0 < e) :
    geom e * (1 - X ^ e) = 1 := by
  apply PowerSeries.ext
  intro t
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
  simp only [geom, coeff_mk]
  by_cases het : e ≤ t
  · rw [ite_eq_left het]
    have hdvd : e ∣ t - e ↔ e ∣ t := by
      constructor
      · intro h
        have := dvd_add h (dvd_refl e)
        simpa [Nat.sub_add_cancel het] using this
      · intro h
        exact Nat.dvd_sub h (dvd_refl e)
    have ht : t ≠ 0 := by omega
    simp [hdvd, coeff_one, ht]
  · rw [ite_eq_right het]
    by_cases ht : t = 0
    · simp [ht]
    · have hnot : ¬ e ∣ t := by
        intro h
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht) h
        omega
      simp [hnot, coeff_one, ht]


private theorem map_geom_inverse {R : Type} [CommRing R]
    (F : PowerSeries ℤ →+* R) (e : ℕ) (he : 0 < e) :
    F (geom e) = Ring.inverse (1 - (F X) ^ e) := by
  have hmul := congrArg F (geom_mul_one_sub e he)
  simp only [map_mul, map_sub, map_one, map_pow] at hmul
  have hu : IsUnit (1 - F X ^ e) :=
    isUnit_iff_exists_inv.mpr ⟨F (geom e), by simpa [mul_comm] using hmul⟩
  apply hu.mul_right_cancel
  rw [Ring.inverse_mul_cancel _ hu]
  exact hmul

private theorem coeff_eq_of_mod_X (n : ℕ) (a b : PowerSeries ℤ)
    (h : Ideal.Quotient.mk (Ideal.span ({X ^ (n + 1)} : Set (PowerSeries ℤ))) a =
      Ideal.Quotient.mk (Ideal.span ({X ^ (n + 1)} : Set (PowerSeries ℤ))) b) :
    coeff n a = coeff n b := by
  have hmem := Ideal.Quotient.eq.mp h
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hmem
  have hc := congrArg (coeff n) hp
  rw [map_sub, coeff_X_pow_mul', ite_eq_right (by omega)] at hc
  exact sub_eq_zero.mp hc

/-- Indices of the finite numerator offsets, including the empty boundary ranges. -/
def offsetIndices (k m : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (range (m-1)).disjSum (range (k-m-1))

/-- The source's even and odd numerator offsets. -/
def offset (m : ℕ) : ℕ ⊕ ℕ → ℕ :=
  Sum.elim (fun i => 2+2*i) (fun i => 2*m+1+2*i)

/-- The exact finite rational-series expansion of the transformed source term. -/
noncomputable def rationalSeries (k m : ℕ) : PowerSeries ℤ :=
  (∑ S ∈ (offsetIndices k m).powerset,
    C ((-1 : ℤ)^S.card) * X^(∑ i ∈ S, offset m i) * geom (2*S.card+1)) *
    ∏ i ∈ range (k-1), geom (2*i+1)

private theorem rational_coefficient_expansion (k m n : ℕ) :
    coeff n (rationalTrunc k m n) = coeff n (rationalSeries k m) := by
  classical
  let I : Ideal (PowerSeries ℤ) := Ideal.span ({X^(n+1)} : Set (PowerSeries ℤ))
  let F := Ideal.Quotient.mk I
  let q := F X
  have hq : q^(n+1)=0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hsum (e : ℕ) (he : 0 < e) :
      (∑ r ∈ range (n+1), q^(e*r)) = F (geom e) := by
    have hmul := congrArg F (geom_mul_one_sub e he)
    simp only [map_mul, map_sub, map_one, map_pow] at hmul
    have hu : IsUnit (1-q^e) := isUnit_iff_exists_inv.mpr
      ⟨F (geom e), by simpa [q, mul_comm] using hmul⟩
    apply hu.mul_right_cancel
    have hgeo := mul_geom_sum (q^e) (n+1)
    have hz : (q^e)^(n+1)=0 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
    simp only [hz, sub_zero, ← pow_mul] at hgeo
    have hgeo' : (∑ r ∈ range (n+1), q^(e*r)) * (1-q^e) = 1 := by
      linear_combination -hgeo
    exact hgeo'.trans hmul.symm
  have hexp (r : ℕ) :
      (∏ i ∈ range (m-1), (1-q^(2*r+2+2*i))) *
        (∏ i ∈ range (k-m-1), (1-q^(2*r+2*m+1+2*i))) =
      ∑ S ∈ (offsetIndices k m).powerset,
        (-1) ^ S.card * q^(2*r*S.card + ∑ i ∈ S, offset m i) := by
    rw [show (∏ i ∈ range (m-1), (1-q^(2*r+2+2*i))) *
        (∏ i ∈ range (k-m-1), (1-q^(2*r+2*m+1+2*i))) =
        ∏ i ∈ offsetIndices k m, (1-q^(2*r+offset m i)) by
      simp [offsetIndices, prod_disjSum, offset, Nat.add_assoc]]
    rw [prod_sub]
    apply sum_congr rfl
    intro S _
    simp only [prod_const_one, mul_one, prod_pow_eq_pow_sum, sum_add_distrib, sum_const,
      nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have heq : F (rationalTrunc k m n) = F (rationalSeries k m) := by
    simp only [rationalTrunc, rationalSeries, map_mul, map_sum, map_prod, map_sub,
      map_one, map_pow]
    congr 1
    conv_lhs => arg 2; ext r; rw [mul_assoc, hexp, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro S _
    have hterm (r : ℕ) : q^r * ((-1)^S.card *
        q^(2*r*S.card+∑ i ∈ S, offset m i)) =
        (-1)^S.card * q^(∑ i ∈ S, offset m i) * q^((2*S.card+1)*r) := by
      rw [pow_add, show (2*S.card+1)*r = r+2*r*S.card by ring, pow_add]
      ring
    change (∑ r ∈ range (n+1), q^r * ((-1)^S.card *
      q^(2*r*S.card+∑ i ∈ S, offset m i))) = _
    simp_rw [hterm]
    rw [← mul_sum, hsum _ (by omega)]
    simp only [map_pow, map_neg, map_one]
    rfl
  exact coeff_eq_of_mod_X n _ _ heq

/-- Source Theorem 4, for every admissible pair and every coefficient, with no shift. -/
theorem source_coefficient_reduction (k m n : ℕ) (hm : 1 ≤ m) (hmk : m < k) :
    dCoeff k m n = coeff n (rationalTrunc k m n - productTrunc k n) := by
  classical
  let I : Ideal (PowerSeries ℤ) := Ideal.span ({X ^ (n + 1)} : Set (PowerSeries ℤ))
  let F := Ideal.Quotient.mk I
  let q := F X
  have hq : q ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hinv (e : ℕ) (he : 0 < e) : F (geom e) = Ring.inverse (1 - q ^ e) :=
    map_geom_inverse F e he
  let f (j : ℕ) : (PowerSeries ℤ) ⧸ I := q ^ (2 * m * j) *
    ∏ i ∈ range (n + 1),
      (1 - q ^ (2 * j + 2 + 2 * i)) * (1 - q ^ (2 * j + 2 * k + 2 * i)) *
      Ring.inverse (1 - q ^ (2 * j + 1 + 2 * i)) ^ 2
  have hfN : f (n + 1) = 0 := by
    dsimp only [f]
    have hz : q ^ (2 * m * (n + 1)) = 0 := by
      rw [Nat.mul_comm (2 * m), pow_mul, hq, zero_pow (by omega)]
    rw [hz, zero_mul]
  have hshift : (∑ j ∈ range (n + 1), f j) =
      (∑ j ∈ range (n + 1), f (j + 1)) + f 0 := by
    have hfirst := sum_range_succ' f (n + 1)
    have hlast := sum_range_succ f (n + 1)
    rw [hfN, add_zero] at hlast
    exact hlast.symm.trans hfirst
  have hd : F (dTrunc k m n) = ∑ j ∈ range (n + 1), f (j + 1) := by
    simp only [dTrunc, f, map_sum, map_mul, map_pow, map_prod, map_sub, map_one]
    apply sum_congr rfl
    intro j _
    rw [show m * (2 * j + 2) = 2 * m * (j + 1) by ring]
    congr 1
    apply prod_congr rfl
    intro i _
    rw [hinv _ (by omega)]
    congr 2 <;> omega
  have hp : F (productTrunc k n) = f 0 := by
    simp only [productTrunc, f, map_prod, map_mul, map_sub, map_one, map_pow,
      Nat.mul_zero, zero_add, pow_zero, one_mul]
    apply prod_congr rfl
    intro i _
    rw [hinv _ (by omega)]
  have hr : F (rationalTrunc k m n) = ∑ j ∈ range (n + 1), f j := by
    rw [show (∑ j ∈ range (n + 1), f j) = _ from
      nilpotent_source_reduction q (n + 1) k m hq hm hmk]
    simp only [rationalTrunc, map_sum, map_prod, map_mul, map_pow, map_sub, map_one]
    congr 1
    apply prod_congr rfl
    intro i _
    rw [hinv _ (by omega)]
  have hfg : F (dTrunc k m n) = F (rationalTrunc k m n - productTrunc k n) := by
    rw [map_sub, hr, hp, hshift, hd]
    ring
  exact coeff_eq_of_mod_X n _ _ hfg

/-- The consistent coefficient sequence of the first Gauss quotient. -/
noncomputable def gaussSeries : PowerSeries ℤ := mk fun n => coeff n (productTrunc 2 n)

/-- The source product after its finite even-denominator factorization. -/
noncomputable def productSeries (k : ℕ) : PowerSeries ℤ :=
  gaussSeries * ∏ i ∈ range (k-2), geom (2*i+4)

private theorem productTrunc_stable (k t N : ℕ) (hk : 1 ≤ k) (ht : t ≤ N) :
    coeff t (productTrunc k N) = coeff t (productTrunc k t) := by
  classical
  let I : Ideal (PowerSeries ℤ) := Ideal.span ({X^(t+1)} : Set (PowerSeries ℤ))
  let F := Ideal.Quotient.mk I
  let q := F X
  have hq : q^(t+1)=0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hz (e : ℕ) (he : t+1 ≤ e) : q^e=0 := by
    rw [show e=(t+1)+(e-(t+1)) by omega, pow_add, hq, zero_mul]
  apply coeff_eq_of_mod_X t
  simp only [productTrunc, map_prod, map_mul, map_sub, map_one, map_pow]
  symm
  apply prod_subset (range_mono (by omega))
  intro i hi hnot
  have hi' : t+1 ≤ i := by simpa using hnot
  rw [map_geom_inverse F _ (by omega)]
  change (1-q^(2+2*i))*(1-q^(2*k+2*i))*Ring.inverse (1-q^(1+2*i))^2=1
  rw [hz _ (by omega), hz _ (by omega), hz _ (by omega)]
  simp

private theorem product_coefficient_expansion (k n : ℕ) (hk : 2 ≤ k) :
    coeff n (productTrunc k n) = coeff n (productSeries k) := by
  classical
  let I : Ideal (PowerSeries ℤ) := Ideal.span ({X^(n+1)} : Set (PowerSeries ℤ))
  let F := Ideal.Quotient.mk I
  let q := F X
  have hq : q^(n+1)=0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hz (e : ℕ) (he : n+1 ≤ e) : q^e=0 := by
    rw [show e=(n+1)+(e-(n+1)) by omega, pow_add, hq, zero_mul]
  let f (i : ℕ) : (PowerSeries ℤ) ⧸ I := 1-q^(2*i+4)
  let B : (PowerSeries ℤ) ⧸ I := ∏ i ∈ range (k-2), f i
  let G : PowerSeries ℤ := ∏ i ∈ range (k-2), geom (2*i+4)
  have hunit : B*F G=1 := by
    simp only [B, G, map_prod, ← prod_mul_distrib]
    apply prod_eq_one
    intro i _
    have h := congrArg F (geom_mul_one_sub (2*i+4) (by omega))
    simpa [map_mul, map_sub, map_pow, map_one, mul_comm, f, q] using h
  have htail : (∏ i ∈ range (n+1), (1-q^(2*k+2*i)))*B =
      ∏ i ∈ range (n+1), (1-q^(4+2*i)) := by
    have heq : (∏ i ∈ range ((n+1)+(k-2)), f i) = ∏ i ∈ range (n+1), f i := by
      rw [prod_range_add]
      have hone : (∏ i ∈ range (k-2), f (n+1+i))=1 := by
        apply prod_eq_one
        intro i _
        dsimp [f]
        rw [hz _ (by omega), sub_zero]
      rw [hone, mul_one]
    have heq' := prod_range_add f (k-2) (n+1)
    rw [show k-2+(n+1)=(n+1)+(k-2) by omega, heq] at heq'
    have he (i : ℕ) : 2*(k-2+i)+4=2*k+2*i := by omega
    rw [mul_comm] at heq'
    dsimp only [f] at heq'
    simp only [he] at heq'
    simpa only [B, f, show ∀ i, 2*i+4=4+2*i by omega] using heq'.symm
  have hprod : F (productTrunc k n)*B=F (productTrunc 2 n) := by
    simp only [productTrunc, map_prod, map_mul, map_sub, map_pow, map_one,
      prod_mul_distrib]
    change ((∏ i ∈ range (n+1), (1-q^(2+2*i))) *
      (∏ i ∈ range (n+1), (1-q^(2*k+2*i))) *
      (∏ i ∈ range (n+1), F (geom (1+2*i))^2))*B = _
    have hm : ((∏ i ∈ range (n+1), (1-q^(2+2*i))) *
        (∏ i ∈ range (n+1), (1-q^(2*k+2*i))) *
        (∏ i ∈ range (n+1), F (geom (1+2*i))^2))*B =
        (∏ i ∈ range (n+1), (1-q^(2+2*i))) *
        ((∏ i ∈ range (n+1), (1-q^(2*k+2*i)))*B) *
        (∏ i ∈ range (n+1), F (geom (1+2*i))^2) := by ring
    rw [hm, htail]
  have hfg : F (productTrunc k n)=F (productTrunc 2 n*G) := by
    rw [map_mul]
    calc F (productTrunc k n) = F (productTrunc k n)*(B*F G) := by rw [hunit, mul_one]
         _ = _ := by rw [← mul_assoc, hprod]
  have hc := coeff_eq_of_mod_X n _ _ hfg
  rw [hc]
  unfold productSeries
  change coeff n (productTrunc 2 n*G)=coeff n (gaussSeries*G)
  rw [coeff_mul, coeff_mul]
  apply sum_congr rfl
  intro p hp
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [productTrunc_stable 2 p.1 n (by omega) (by omega)]
  simp only [gaussSeries, coeff_mk]

/-- Full source coefficient identity, expressed using fixed series and with no index shift. -/
theorem source_coefficient_expansion (k m n : ℕ) (hm : 1 ≤ m) (hmk : m < k) :
    dCoeff k m n = coeff n (rationalSeries k m) - coeff n (productSeries k) := by
  rw [source_coefficient_reduction k m n hm hmk, map_sub,
    rational_coefficient_expansion, product_coefficient_expansion k n (by omega)]

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
