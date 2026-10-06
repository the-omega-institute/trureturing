/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn
   mirror-E: none(waiver:named-motzkin-column-conjecture)
   anchors: []
   utility: none
   digest: Cigler's Motzkin-column series has the prescribed denominator and exact degree. -/

import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnSequence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumn

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinColumnDefs
open CiglerMotzkinHankelOrthogonal CiglerMotzkinHankelNegative

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1600000 in
-- Mixed determinants and bilateral coefficient sums need a larger elaboration budget.
/-- The normalized mixed alternant descends to the exact integral numerator. -/
theorem result : CiglerMotzkinColumnDefs.claim := by
  intro k m hm
  classical
  obtain ⟨K, field, characteristic, phi, alpha, zeta, injective, parameter, separated,
    primitive, nodes_ne, w, a, b, modes, fixed_forward, fixed_back,
    z, A, B, constant, forward, back, recurrence⟩ :=
    CiglerMotzkinColumnSequence.scalar_model k m
  let := field
  let := characteristic
  let h := m + k
  let psi : Base →+* K := phi.comp specialize.toRingHom
  let r (i : Fin k) : K := phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹
  let c (i : Fin m) : K := i.val
  let gB : Base[X] := X ^ m * orthogonal k
  let g : (ℤ[X])[X] := Polynomial.map specialize.toRingHom gB
  have gB_monic : gB.IsMonicOfDegree h := by
    simpa [gB, h] using (isMonicOfDegree_X_pow Base m).mul (orthogonal_basis k).1
  have g_monic : g.IsMonicOfDegree h := by
    constructor
    · rw [show g = Polynomial.map specialize.toRingHom gB from rfl,
        gB_monic.monic.natDegree_map, gB_monic.natDegree_eq]
    · exact gB_monic.monic.map _
  let V : K := (Matrix.vandermonde c).det * (Matrix.vandermonde r).det * (∏ i, r i ^ m)
  have V_ne : V ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply Matrix.det_vandermonde_ne_zero_iff.mpr
        intro i j equal
        apply Fin.ext
        exact Nat.cast_injective equal
      · exact Matrix.det_vandermonde_ne_zero_iff.mpr
          (CiglerMotzkinColumnDenominator.fixed_roots phi k zeta primitive).1
    · exact prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero m (nodes_ne i))
  let u (j : Fin h) : (PowerSeries K)ˣ :=
    if hj : j.val < m then Units.map (PowerSeries.rescale (j.val : K)).toMonoidHom z
    else Units.map PowerSeries.C.toMonoidHom (w ⟨j.val - m, by dsimp [h] at j; omega⟩)
  let aa (j : Fin h) : PowerSeries K :=
    if hj : j.val < m then PowerSeries.rescale (j.val : K) A
    else PowerSeries.C (a ⟨j.val - m, by dsimp [h] at j; omega⟩)
  let bb (j : Fin h) : PowerSeries K :=
    if hj : j.val < m then PowerSeries.rescale (j.val : K) B
    else PowerSeries.C (b ⟨j.val - m, by dsimp [h] at j; omega⟩)
  let T (n : ℤ) : Matrix (Fin h) (Fin h) (PowerSeries K) := Matrix.of fun i j =>
    aa j * ((u j ^ (n + i.val) : (PowerSeries K)ˣ) : PowerSeries K) +
      bb j * ((u j ^ (-(n + i.val)) : (PowerSeries K)ˣ) : PowerSeries K)
  let v (n : ℤ) : K := PowerSeries.coeff (m.choose 2) (T n).det
  let U (n : ℤ) : K := (-1) ^ h.choose 2 * V⁻¹ * v n
  let q (n : ℤ) : PowerSeries K :=
    A * ((z ^ n : (PowerSeries K)ˣ) : PowerSeries K) +
      B * ((z ^ (-n) : (PowerSeries K)ˣ) : PowerSeries K)
  let qf (n : ℤ) (i : Fin k) : K :=
    a i * ((w i ^ n : Kˣ) : K) + b i * ((w i ^ (-n) : Kˣ) : K)
  have T_entry (n : ℤ) (i j : Fin h) : T n i j =
      if hj : j.val < m then PowerSeries.rescale (j.val : K) (q (n + i.val))
      else PowerSeries.C (qf (n + i.val) ⟨j.val - m, by dsimp [h] at j; omega⟩) := by
    have rescaled (x : K) (s : ℤ) :
        ((Units.map (PowerSeries.rescale x).toMonoidHom z ^ s : (PowerSeries K)ˣ) :
          PowerSeries K) = PowerSeries.rescale x ((z ^ s : (PowerSeries K)ˣ) :
            PowerSeries K) := (congrArg Units.val (map_zpow
              (Units.map (PowerSeries.rescale x).toMonoidHom) z s)).symm
    have scalar (i : Fin k) (s : ℤ) :
        ((Units.map PowerSeries.C.toMonoidHom (w i) ^ s : (PowerSeries K)ˣ) :
          PowerSeries K) = PowerSeries.C ((w i ^ s : Kˣ) : K) :=
      (congrArg Units.val (map_zpow (Units.map PowerSeries.C.toMonoidHom) (w i) s)).symm
    dsimp only [T, Matrix.of_apply, aa, bb, u]
    split_ifs with top
    · simp only [rescaled, q, map_add, map_mul]
    · simp only [scalar, qf, map_add, map_mul]
  have signs (s : ℕ) (M : Matrix (Fin h) (Fin h) K) :
      (-1 : K) ^ h.choose 2 *
        (Matrix.of fun i j => (-1 : K) ^ (s + i.val) * M i j).det =
          (-1 : K) ^ (s * h) * M.det := by
    have index_sum (l : ℕ) : (∑ i : Fin l, i.val) = l.choose 2 := by
      induction l with
      | zero => simp
      | succ l ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih, Nat.choose_succ_succ, Nat.choose_one_right]
        change l.choose 2 + l = l + l.choose 2
        omega
    rw [Matrix.det_mul_column, prod_pow_eq_pow_sum, sum_add_distrib, sum_const,
      card_univ, Fintype.card_fin, smul_eq_mul, index_sum, ← mul_assoc, ← pow_add]
    rw [show h.choose 2 + (h * s + h.choose 2) = s * h + 2 * h.choose 2 by ring,
      pow_add, pow_mul]
    simp
  have bridge (n : ℤ) (s : ℕ) (f : Fin h → (ℤ[X])[X])
      (series : ∀ i, q (n + i.val) = (-1 : PowerSeries K) ^ (s + i.val) *
        (Polynomial.map phi (f i) : PowerSeries K))
      (fixed : ∀ i j, qf (n + i.val) j = (-1 : K) ^ (s + i.val) *
        (Polynomial.map phi (f i)).eval (r j)) :
      U n = (-1 : K) ^ (s * h) *
        phi ((Matrix.of fun i j : Fin h => ((f i) %ₘ g).coeff j.val).det) := by
    let M : Matrix (Fin h) (Fin h) (PowerSeries K) := Matrix.of fun i j =>
      if hj : j.val < m then PowerSeries.rescale (j.val : K) (Polynomial.map phi (f i))
      else PowerSeries.C ((Polynomial.map phi (f i)).eval
        (r ⟨j.val - m, by dsimp [h] at j; omega⟩))
    have matrix : T n = Matrix.of fun i j =>
        PowerSeries.C ((-1 : K) ^ (s + i.val)) * M i j := by
      ext i j
      rw [T_entry]
      dsimp only [M, Matrix.of_apply]
      split_ifs with top
      · rw [series, map_mul]
        congr 1
        simp
      · rw [fixed, map_mul]
    have mixed := (CiglerMotzkinColumnDenominator.fixed_roots
      phi k zeta primitive).2.2.2.2 m (fun i => Polynomial.map phi (f i)) c
    have mapped_g : X ^ m * Polynomial.map psi (orthogonal k) =
        Polynomial.map phi g := by simp [g, gB, psi, Polynomial.map_map]
    have rem_matrix :
        (Matrix.of fun i j : Fin h =>
          ((Polynomial.map phi (f i)) %ₘ (Polynomial.map phi g)).coeff j.val).det =
          phi ((Matrix.of fun i j : Fin h => ((f i) %ₘ g).coeff j.val).det) := by
      rw [phi.map_det]
      congr 1
      ext i j
      simp only [Matrix.of_apply]
      rw [← map_modByMonic phi g_monic.monic, coeff_map]
      rfl
    change PowerSeries.coeff (m.choose 2) M.det = V *
      (Matrix.of fun i j : Fin h => ((Polynomial.map phi (f i)) %ₘ
        (X ^ m * Polynomial.map psi (orthogonal k))).coeff j.val).det at mixed
    rw [mapped_g, rem_matrix] at mixed
    have scaled := Matrix.det_mul_column
      (fun i : Fin h => PowerSeries.C ((-1 : K) ^ (s + i.val))) M
    rw [← map_prod] at scaled
    change (Matrix.of fun i j =>
      PowerSeries.C ((-1 : K) ^ (s + i.val)) * M i j).det = _ at scaled
    dsimp only [U, v]
    rw [matrix, scaled, PowerSeries.coeff_C_mul, mixed]
    have sign_product : (-1 : K) ^ h.choose 2 *
        (∏ i : Fin h, (-1 : K) ^ (s + i.val)) = (-1 : K) ^ (s * h) := by
      simpa only [Matrix.det_mul_column, Matrix.det_one, mul_one] using signs s (1 :
        Matrix (Fin h) (Fin h) K)
    calc
      _ = ((-1 : K) ^ h.choose 2 * (∏ i : Fin h, (-1 : K) ^ (s + i.val))) *
          (V⁻¹ * V) * phi
            ((Matrix.of fun i j : Fin h => ((f i) %ₘ g).coeff j.val).det) := by ring
      _ = _ := by rw [sign_product, inv_mul_cancel₀ V_ne, mul_one]
  have positive (n : ℕ) : U n = phi (columnHankel k m n) := by
    rw [bridge n n (fun i => Polynomial.map specialize.toRingHom (orthogonal (n + i.val)))]
    · obtain ⟨ell, moments, ortho⟩ := CiglerMotzkinColumnTransfer.column_moments
      have integral := CiglerMotzkinColumnDeterminant.multiplier_remainders
        orthogonal (fun i => (orthogonal_basis i).1) ell ortho gB h n gB_monic
      have entries (i j : Fin n) : ell (gB * X ^ (i.val + j.val)) =
          motzkin (m + i.val + j.val) k := by
        rw [show gB * X ^ (i.val + j.val) = X ^ (m + i.val + j.val) * orthogonal k by
          dsimp [gB]; rw [pow_add, pow_add]; ring, moments]
      simp only [entries] at integral
      have specialized := congrArg specialize integral
      simp only [map_mul, map_pow, map_neg, map_one] at specialized
      rw [specialize.map_det, specialize.map_det] at specialized
      have remainder (i j : Fin h) : specialize ((orthogonal (n + i.val) %ₘ gB).coeff
          j.val) = ((Polynomial.map specialize.toRingHom
          (orthogonal (n + i.val))) %ₘ g).coeff j.val := by
        dsimp only [g]
        rw [← map_modByMonic specialize.toRingHom gB_monic.monic, coeff_map]
        rfl
      simp only [AlgHom.mapMatrix_apply] at specialized
      change columnHankel k m n = _ at specialized
      rw [specialized, map_mul, map_pow, map_neg, map_one]
      congr 1
      apply congrArg phi
      apply congrArg Matrix.det
      funext i j
      exact (remainder i j).symm
    · intro i
      rw [show (n : ℤ) + i.val = ((n + i.val : ℕ) : ℤ) by omega]
      simpa only [q, Polynomial.map_map, zpow_natCast] using (forward (n + i.val)).symm
    · intro i j
      rw [show (n : ℤ) + i.val = ((n + i.val : ℕ) : ℤ) by omega]
      simpa only [qf, Polynomial.map_map, zpow_natCast] using
        (fixed_forward j (n + i.val)).symm
  have negative (s : ℕ) : U (-(s : ℤ)) = (-1 : K) ^ (s * h) *
      phi ((Matrix.of fun i j : Fin h =>
        ((if i.val < s then Polynomial.map specialize.toRingHom (backward (s - 1 - i.val))
          else Polynomial.map specialize.toRingHom (orthogonal (i.val - s))) %ₘ g).coeff
            j.val).det) := by
    apply bridge
    · intro i
      by_cases top : i.val < s
      · rw [if_pos top, show -(s : ℤ) + i.val =
          -((s - 1 - i.val + 1 : ℕ) : ℤ) by omega]
        have sign : (-1 : PowerSeries K) ^ (s - 1 - i.val + 1) = (-1) ^ (s + i.val) := by
          apply neg_one_pow_congr
          rw [even_iff_two_dvd, even_iff_two_dvd]
          omega
        simpa only [q, sign, Polynomial.map_map, neg_neg, zpow_natCast] using
          (back (s - 1 - i.val)).symm
      · rw [if_neg top, show -(s : ℤ) + i.val = ((i.val - s : ℕ) : ℤ) by omega]
        have sign : (-1 : PowerSeries K) ^ (i.val - s) = (-1) ^ (s + i.val) := by
          apply neg_one_pow_congr
          rw [even_iff_two_dvd, even_iff_two_dvd]
          omega
        simpa only [q, sign, Polynomial.map_map, zpow_natCast] using (forward (i.val - s)).symm
    · intro i j
      by_cases top : i.val < s
      · rw [if_pos top, show -(s : ℤ) + i.val =
          -((s - 1 - i.val + 1 : ℕ) : ℤ) by omega]
        have sign : (-1 : K) ^ (s - 1 - i.val + 1) = (-1) ^ (s + i.val) := by
          apply neg_one_pow_congr
          rw [even_iff_two_dvd, even_iff_two_dvd]
          omega
        simpa only [qf, sign, Polynomial.map_map, neg_neg, zpow_natCast] using
          (fixed_back j (s - 1 - i.val)).symm
      · rw [if_neg top, show -(s : ℤ) + i.val = ((i.val - s : ℕ) : ℤ) by omega]
        have sign : (-1 : K) ^ (i.val - s) = (-1) ^ (s + i.val) := by
          apply neg_one_pow_congr
          rw [even_iff_two_dvd, even_iff_two_dvd]
          omega
        simpa only [qf, sign, Polynomial.map_map, zpow_natCast] using
          (fixed_forward j (i.val - s)).symm
  have negative_gap (s : ℕ) (hs : 1 ≤ s) (hb : s < h + 1) : U (-(s : ℤ)) = 0 := by
    rw [negative, (CiglerMotzkinColumnNegative.negative_endpoint h g g_monic).1
      s hs (by omega), map_zero, mul_zero]
  have endpoint : U (-((h + 1 : ℕ) : ℤ)) = (-1 : K) ^ (h + 1).choose 2 := by
    rw [negative]
    have entries (i j : Fin h) :
        ((if i.val < h + 1 then Polynomial.map specialize.toRingHom
          (backward (h + 1 - 1 - i.val)) else Polynomial.map specialize.toRingHom
          (orthogonal (i.val - (h + 1)))) %ₘ g).coeff j.val =
          ((Polynomial.map specialize.toRingHom (backward (h - i.val))) %ₘ g).coeff
            j.val := by rw [if_pos (by omega), Nat.add_sub_cancel]
    simp only [entries]
    rw [(CiglerMotzkinColumnNegative.negative_endpoint h g g_monic).2,
      map_pow, map_neg, map_one]
    have even : Even ((h + 1) * h) := by
      simpa only [Nat.mul_comm] using Nat.even_mul_succ_self h
    rw [even.neg_one_pow, one_mul]
  have negative_nonzero : U (-((h + 1 : ℕ) : ℤ)) ≠ 0 := by
    rw [endpoint]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  let Q : K[X] := Polynomial.map phi (columnDenominator k m)
  have degree_info :=
    (CiglerMotzkinColumnDenominator.mode_denominator phi alpha parameter k m).2
  change Q.natDegree = (k + 1) * (m + 1 + (m + 1).choose 3) ∧
    Q.leadingCoeff ≠ 0 at degree_info
  let N := (m + 1).choose 3 + k * (m.choose 1 + m.choose 2 + m.choose 3)
  have balance : Q.natDegree = N + h + 1 := by
    rw [degree_info.1]
    dsimp only [N, h]
    have pascal : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    rw [Nat.choose_one_right, pascal]
    ring
  have recurrent (n : ℤ) :
      ∑ d ∈ range (Q.natDegree + 1), Q.coeff d * U (n - d) = 0 := by
    have raw := recurrence n
    change ∑ d ∈ range (Q.natDegree + 1), Q.coeff d * v (n - d) = 0 at raw
    have scaled : (∑ d ∈ range (Q.natDegree + 1), Q.coeff d * U (n - d)) =
        ((-1 : K) ^ h.choose 2 * V⁻¹) *
          (∑ d ∈ range (Q.natDegree + 1), Q.coeff d * v (n - d)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      dsimp only [U]
      ring
    rw [scaled, raw, mul_zero]
  let FK : PowerSeries K := (Q : PowerSeries K) * PowerSeries.mk (fun n => U n)
  have convolution (n : ℕ) : PowerSeries.coeff n FK =
      ∑ d ∈ range (Q.natDegree + 1),
        if d ≤ n then Q.coeff d * U ((n : ℤ) - d) else 0 := by
    dsimp only [FK]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
    by_cases hb : n ≤ Q.natDegree
    · apply sum_subset_zero_on_sdiff (range_mono (by omega))
      · intro d hd
        simp only [mem_sdiff, mem_range] at hd
        rw [if_neg (by omega)]
      · intro d hd
        have dn : d ≤ n := by simp only [mem_range] at hd; omega
        rw [if_pos dn, Nat.cast_sub dn]
    · symm
      apply sum_subset_zero_on_sdiff (range_mono (by omega))
      · intro d hd
        simp only [mem_sdiff, mem_range] at hd
        rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      · intro d hd
        have dn : d ≤ n := by simp only [mem_range] at hd; omega
        rw [if_pos dn, Nat.cast_sub dn]
  have boundary (n : ℕ) : PowerSeries.coeff n FK =
      -(∑ d ∈ range (Q.natDegree + 1),
        if n < d then Q.coeff d * U ((n : ℤ) - d) else 0) := by
    have split : (∑ d ∈ range (Q.natDegree + 1), Q.coeff d * U ((n : ℤ) - d)) =
        (∑ d ∈ range (Q.natDegree + 1),
          if d ≤ n then Q.coeff d * U ((n : ℤ) - d) else 0) +
        (∑ d ∈ range (Q.natDegree + 1),
          if n < d then Q.coeff d * U ((n : ℤ) - d) else 0) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      by_cases hd : d ≤ n <;> simp [hd, show (n < d) ↔ ¬d ≤ n by omega]
    rw [recurrent, ← convolution] at split
    exact eq_neg_of_add_eq_zero_left split.symm
  have field_tail (n : ℕ) (hn : N < n) : PowerSeries.coeff n FK = 0 := by
    rw [boundary, neg_eq_zero]
    apply sum_eq_zero
    intro d hd
    split_ifs with top
    · have db : d ≤ Q.natDegree := by simp only [mem_range] at hd; omega
      have index : (n : ℤ) - d = -((d - n : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega)]; ring
      rw [index, negative_gap (d - n) (by omega) (by omega), mul_zero]
    · rfl
  have field_top : PowerSeries.coeff N FK =
      -Q.leadingCoeff * U (-((h + 1 : ℕ) : ℤ)) := by
    rw [boundary, sum_eq_single Q.natDegree]
    · rw [if_pos (by omega), coeff_natDegree]
      have index : (N : ℤ) - Q.natDegree = -((h + 1 : ℕ) : ℤ) := by
        rw [balance]; push_cast; ring
      rw [index, neg_mul]
    · intro d hd different
      split_ifs with top
      · have db : d < Q.natDegree := by simp only [mem_range] at hd; omega
        have index : (N : ℤ) - d = -((d - N : ℕ) : ℤ) := by
          rw [Nat.cast_sub (by omega)]; ring
        rw [index, negative_gap (d - N) (by omega) (by omega), mul_zero]
      · rfl
    · simp
  let F : PowerSeries ℤ[X] := (columnDenominator k m : PowerSeries ℤ[X]) *
    PowerSeries.mk (columnHankel k m)
  have mapped_series : PowerSeries.map phi F = FK := by
    dsimp only [F, FK, Q]
    rw [map_mul, Polynomial.polynomial_map_coe]
    congr 1
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (positive n).symm
  have mapped_coeff (n : ℕ) : phi (PowerSeries.coeff n F) = PowerSeries.coeff n FK := by
    rw [← PowerSeries.coeff_map, mapped_series]
  have tail (n : ℕ) (hn : N < n) : PowerSeries.coeff n F = 0 := by
    apply injective
    rw [map_zero, mapped_coeff, field_tail n hn]
  have top_ne : PowerSeries.coeff N F ≠ 0 := by
    intro zero
    have zeroK : PowerSeries.coeff N FK = 0 := by rw [← mapped_coeff, zero, map_zero]
    rw [field_top, neg_mul] at zeroK
    exact (neg_ne_zero.mpr (mul_ne_zero degree_info.2 negative_nonzero)) zeroK
  let R : (ℤ[X])[X] :=
    ∑ n ∈ range (N + 1), Polynomial.monomial n (PowerSeries.coeff n F)
  have coefficients (n : ℕ) : R.coeff n =
      if n < N + 1 then PowerSeries.coeff n F else 0 := by
    simp [R, finsetSum_coeff, coeff_monomial]
  refine ⟨R, ?_, ?_⟩
  · apply PowerSeries.ext
    intro n
    rw [Polynomial.coeff_coe, coefficients]
    split_ifs with hn
    · rfl
    · exact (tail n (by omega)).symm
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [coefficients, if_neg (by omega)]
    · rw [coefficients, if_pos (by omega)]
      exact top_ne

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumn
