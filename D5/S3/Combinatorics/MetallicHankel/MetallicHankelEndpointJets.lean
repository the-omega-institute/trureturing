/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointJets
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointJets
   mirror-E: none(waiver:actual-continuant-endpoint-jets)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: All endpoint coefficients of the same metallic continuants have exact polynomial laws. -/

import D5.S3.Combinatorics.MetallicHankel.MetallicHankelBlocks
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointSpectral
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelBranches

/-! Exact rational polynomial laws for both endpoints of supported continuants. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets

open PowerSeries Finset MetallicHankelBlocks MetallicHankelData
open scoped Matrix

private theorem identity_matrix_coefficients
    (R : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ))
    (hR : R.map constantCoeff = 1) (h : ℕ) (i j : Fin 2) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ h ∧ ∀ K : ℕ,
      P.eval (K : ℚ) = coeff h ((R ^ K) i j) := by
  classical
  let V := R - 1
  have divisible (i j : Fin 2) : (X : PowerSeries ℚ) ∣ V i j := by
    apply X_dvd_iff.mpr
    have hij := congrFun (congrFun hR i) j
    simpa [V, Matrix.map_apply, Matrix.one_apply, apply_ite] using sub_eq_zero.mpr hij
  choose T hT using divisible
  let Tm : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ) := T
  have factor : V = (X : PowerSeries ℚ) • Tm := by
    funext i j
    exact hT i j
  have high (a : ℕ) (ha : h < a) : coeff h ((V ^ a) i j) = 0 := by
    rw [factor, smul_pow, Matrix.smul_apply, smul_eq_mul, coeff_X_pow_mul',
      ite_eq_right (by omega)]
  let P : Polynomial ℚ := ∑ a ∈ range (h + 1),
    Polynomial.C (coeff h ((V ^ a) i j) / (a.factorial : ℚ)) * descPochhammer ℚ a
  refine ⟨P, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro a ha
    apply (Polynomial.natDegree_mul_le ..).trans
    simp only [Polynomial.natDegree_C, zero_add, descPochhammer_natDegree]
    exact Nat.le_of_lt_succ (mem_range.mp ha)
  · intro K
    have binomial : R ^ K = ∑ a ∈ range (K + 1),
        (K.choose a : ℕ) • V ^ a := by
      rw [show R = V + 1 by dsimp [V]; abel, (Commute.one_right V).add_pow]
      apply sum_congr rfl
      intro a _
      simp only [one_pow, mul_one, nsmul_eq_mul]
      exact (Nat.cast_commute (K.choose a) (V ^ a)).eq.symm
    have truncation : (∑ a ∈ range (K + 1),
        (K.choose a : ℚ) * coeff h ((V ^ a) i j)) =
        ∑ a ∈ range (h + 1), (K.choose a : ℚ) * coeff h ((V ^ a) i j) := by
      rcases le_total (K + 1) (h + 1) with before | after
      · apply sum_subset (range_mono before)
        intro a _ outside
        rw [Nat.choose_eq_zero_of_lt (by simpa using outside), Nat.cast_zero, zero_mul]
      · symm
        apply sum_subset (range_mono after)
        intro a _ outside
        rw [high a (by simpa using outside), mul_zero]
    rw [binomial]
    simp only [Matrix.sum_apply, Matrix.smul_apply, map_sum, map_nsmul]
    simp only [nsmul_eq_mul, truncation, P, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    apply sum_congr rfl
    intro a _
    rw [Nat.cast_choose_eq_descPochhammer_div ℚ K a]
    ring

private theorem spectral_coefficients
    (U : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ)) (D : ℕ) (hD : 0 < D)
    (htr : constantCoeff (Matrix.trace U) = 1) (hdet : U.det = X ^ D)
    (g h : ℕ) (i j : Fin 2) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ h ∧ ∀ K : ℕ, h < D * K →
      P.eval (K : ℚ) = coeff h (X ^ g * (U ^ K) i j) := by
  obtain ⟨a, ha, E, hE⟩ :=
    MetallicHankelEndpointSpectral.transfer_spectral_remainder U D hD htr hdet
  let u : (PowerSeries ℚ)ˣ :=
    (isUnit_iff_constantCoeff.mpr (ha ▸ isUnit_one)).unit
  have hu : (u : PowerSeries ℚ) = a := IsUnit.unit_spec _
  obtain ⟨P, hp, he⟩ :=
    D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelBranches.unit_power_coefficients
      u (by simpa [hu] using ha) (X ^ g * E i j) h
  refine ⟨P, hp, ?_⟩
  intro K hh
  have hv := he (K : ℤ)
  simp only [Int.cast_natCast, zpow_natCast, Units.val_pow_eq_pow_val, hu] at hv
  rw [hv, show X ^ g * E i j * a ^ K = X ^ g * (a ^ K * E i j) by ring,
    coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs with hg
  · exact (hE K (h - g) (by omega) i j).symm
  · rfl

private theorem common_reverse (d g : ℕ) (f : PowerSeries ℤ)
    (hf : ∀ r, d < r → coeff r f = 0) :
    reverseAt (d + g) (reverseAt d f) = X ^ g * f := by
  ext r
  rw [reverse_coeff, reverse_coeff, coeff_X_pow_mul']
  by_cases hr : r ≤ d + g
  · rw [ite_eq_left hr]
    by_cases hg : g ≤ r
    · rw [ite_eq_left (by omega), ite_eq_left hg]
      rw [show d - (d + g - r) = r - g by omega]
    · rw [ite_eq_right (by omega), ite_eq_right hg]
  · rw [ite_eq_right hr, ite_eq_left (by omega), hf (r - g) (by omega)]

/-- Arbitrary endpoint jets of the supplied, unchanged metallic continuants.
The low jets use their specified-degree reversals. The high jets use the
common-degree reversals, namely Q and X^(n+1) times the predecessor Q.
Every positive block, including the first golden block, is in scope. -/
theorem continuant_endpoint_jets (n L : ℕ) (hn : 1 ≤ n)
    (k : ℕ → ℕ) (b : ℕ → ℤ) (D Q : ℕ → PowerSeries ℤ) (s : ℕ → ℕ)
    (hL : L = if n = 1 then 3 else 6 * n - 4)
    (data : ∀ p, let z := Nat.rec TailState.v₂ (fun _ z => nextState (max n 2) z) p
      k p = (if n = 1 then (if p % 3 = 2 then 1 else 0)
        else (fractionData (max n 2) z).1) ∧
      b p = (if n = 1 then (if p % 3 = 1 then 1 else -1)
        else (fractionData (max n 2) z).2.1) ∧
      D p = (if n = 1 then (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X)
        else (fractionData (max n 2) z).2.2))
    (s0 : s 0 = 0) (ss : ∀ p, s (p + 1) = s p + k p + 1)
    (qzero : Q 0 = 1) (qone : Q 1 = D 0)
    (qstep : ∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
      C (b (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p)
    (support : ∀ p r, s p < r → coeff r (Q p) = 0) :
    let ν := if n % 2 = 0 then 1 else 2
    let ρ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
    ∀ h : ℕ, ∃ P : Fin 4 → Polynomial ℚ,
      (∀ i, (P i).natDegree ≤ h) ∧ ∀ K : ℕ, 1 ≤ K →
        let p := (K * ν) * L
        s p = s (p - 1) + (n + 1) ∧
        reverseAt (s p) (reverseAt (s p) (Q p)) = Q p ∧
        reverseAt (s p) (reverseAt (s (p - 1)) (Q (p - 1))) =
          X ^ (n + 1) * Q (p - 1) ∧
        (P 0).eval (K : ℚ) = ((coeff h (reverseAt (s p) (Q p)) : ℤ) : ℚ) ∧
        (P 1).eval (K : ℚ) = ((coeff h (reverseAt (s (p - 1)) (Q (p - 1))) : ℤ) : ℚ) ∧
        (h < 2 * K * ρ →
          (P 2).eval (K : ℚ) = ((coeff h (Q p) : ℤ) : ℚ) ∧
          (P 3).eval (K : ℚ) = ((coeff h (X ^ (n + 1) * Q (p - 1)) : ℤ) : ℚ)) := by
  classical
  dsimp only
  let ν := if n % 2 = 0 then 1 else 2
  let ρ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
  let R := transferPrefix (reversedStep k b D) L ^ ν
  let U := transferPrefix (ordinaryStep L k b D) L ^ ν
  obtain ⟨hr, hrev⟩ := reversed_blocks n L hn k b D Q s hL data s0 ss qzero qone qstep support
  obtain ⟨ht, hd, hord, hprev⟩ := ordinary_blocks n L hn k b D Q hL data qzero qone qstep
  change R.map constantCoeff = 1 at hr
  change constantCoeff (Matrix.trace U) = 1 at ht
  let φ := PowerSeries.map (Int.castRingHom ℚ)
  let Rq := R.map φ
  let Uq := U.map φ
  have rq : Rq.map constantCoeff = 1 := by
    funext i j
    have hij := congrFun (congrFun hr i) j
    have hc (f : PowerSeries ℤ) : constantCoeff (φ f) = ((constantCoeff f : ℤ) : ℚ) := rfl
    simpa [Rq, Matrix.map_apply, hc, Matrix.one_apply, apply_ite] using
      congrArg (fun z : ℤ => (z : ℚ)) hij
  have ut : constantCoeff (Matrix.trace Uq) = 1 := by
    have hc (f : PowerSeries ℤ) : constantCoeff (φ f) = ((constantCoeff f : ℤ) : ℚ) := rfl
    rw [show Matrix.trace Uq = φ (Matrix.trace U) from (AddMonoidHom.map_trace φ U).symm,
      hc]
    exact_mod_cast ht
  change U.det = X ^ (2 * ρ) at hd
  have ud : Uq.det = X ^ (2 * ρ) := by
    rw [show Uq.det = φ U.det from (φ.map_det U).symm, hd]
    simp only [φ, map_pow, PowerSeries.map_X]
  have pos : 0 < 2 * ρ := by dsimp [ρ]; split_ifs <;> positivity
  have action (M : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ))
      (F G : PowerSeries ℤ) (K : ℕ) (hv : M ^ K *ᵥ ![1, 0] = ![F, G]) :
      ((M.map φ) ^ K) 0 0 = φ F ∧ ((M.map φ) ^ K) 1 0 = φ G := by
    have v0 := congrFun hv 0
    have v1 := congrFun hv 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at v0 v1
    rw [← Matrix.map_pow]
    exact ⟨congrArg φ v0, congrArg φ v1⟩
  intro h
  obtain ⟨A, ha, ea⟩ := identity_matrix_coefficients Rq rq h 0 0
  obtain ⟨B, hb, eb⟩ := identity_matrix_coefficients Rq rq h 1 0
  obtain ⟨C, hc, ec⟩ := spectral_coefficients Uq (2 * ρ) pos ut ud 0 h 0 0
  obtain ⟨E, he, ee⟩ := spectral_coefficients Uq (2 * ρ) pos ut ud (n + 1) h 1 0
  refine ⟨![A, B, C, E], ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · intro K hK
    have rv := action R _ _ K (hrev K hK)
    have ov := action U _ _ K (hord K hK)
    have previous := hprev s ss K hK
    refine ⟨previous, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero, pow_zero, one_mul] using
        common_reverse (s ((K * ν) * L)) 0 (Q ((K * ν) * L)) (support _)
    · rw [previous]
      exact common_reverse _ (n + 1) _ (support _)
    · simpa only [Matrix.cons_val_zero, Rq, rv.1, φ, coeff_map, Int.coe_castRingHom] using ea K
    · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Rq, rv.2,
        φ, coeff_map, Int.coe_castRingHom] using eb K
    · intro hh
      change h < 2 * K * ρ at hh
      have bound : h < (2 * ρ) * K := by simpa only [Nat.mul_right_comm] using hh
      constructor
      · simpa [Uq, ov.1, φ] using ec K bound
      · have shifted : X ^ (n + 1) * (Uq ^ K) 1 0 = φ (X ^ (n + 1) * Q (((K * ν) * L) - 1)) := by
          rw [ov.2]
          simp only [φ, map_mul, map_pow, PowerSeries.map_X, ν]
        simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, shifted, φ, coeff_map,
          Int.coe_castRingHom, ν, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] using ee K bound

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets
