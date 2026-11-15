/- GID: D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/BalaA119370Exponential
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The normalized quadratic series in Bala's exponential identity. -/

import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S3.Combinatorics.Nonnesting.CatalanLagrangeBridge
import D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums
import D5.S3.Arith.Congruence.TebniA350759PrimeCongruences

/-! Exact formal power-series semantics for the quadratic source. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PowerSeries Finset
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

namespace D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential

/-- The generating function specified independently by the original quadratic. -/
def IsSourceSeries (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧ A = 1 + X * A ^ 2 + X ^ 2 * (A ^ 2 - A)

/-- Both endpoints of the finite binomial-square row are included. -/
noncomputable def row (n : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ range (n + 1), C ((n.choose k : ℚ) ^ 2) * (1 + X) ^ k

/-- The locally finite sum of X^n row(n)/n, with n positive. -/
noncomputable def logarithm : PowerSeries ℚ :=
  mk fun m => ∑ n ∈ Icc 1 m, (1 / (n : ℚ)) * coeff (m - n) (row n)

/-- Formal exponential substitution, including its zeroth power. -/
noncomputable def formalExp (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (exp ℚ).subst f

/-- The source discriminant. -/
noncomputable def discriminant : PowerSeries ℚ :=
  (1 + X ^ 2) ^ 2 - 4 * X * (1 + X)

/-- Divide the numerator first by its proven X factor, then by a unit. -/
noncomputable def printedBranch (S : PowerSeries ℚ) : PowerSeries ℚ :=
  (mk fun n => coeff (n + 1) ((1 + X ^ 2) - S)) * (2 * (1 + X))⁻¹

private theorem normalized_quadratic {R : Type*} [CommRing R]
    (u v : PowerSeries R) :
    ∃ f : PowerSeries R, constantCoeff f = 1 ∧
      f = 1 + X * (u * f + v * f ^ 2) ∧
      ∀ g, constantCoeff g = 1 → g = 1 + X * (u * g + v * g ^ 2) → g = f := by
  apply exists_unique_fixed
  · intro f hf
    simp
  · intro d f g hd hf hg hfg
    have hdiv := (agree_iff d f g).mp hfg
    apply (agree_iff (d + 1) _ _).mpr
    rw [pow_succ]
    have hh := dvd_mul_of_dvd_right (mul_dvd_mul hdiv (dvd_refl X)) (u + v * (f + g))
    convert hh using 1; ring

private theorem source_exists : ∃! A : PowerSeries ℚ, IsSourceSeries A := by
  obtain ⟨A, h0, he, hu⟩ := normalized_quadratic (-X) (1 + X : PowerSeries ℚ)
  have hs : IsSourceSeries A := ⟨h0, by linear_combination he⟩
  refine ⟨A, hs, ?_⟩
  intro B hB
  exact hu B hB.1 (by linear_combination hB.2)

private theorem auxiliary_exists :
    ∃ C : PowerSeries (Polynomial ℚ), constantCoeff C = 1 ∧
      C = (1 + X * C) * (1 + PowerSeries.C Polynomial.X * X * C) := by
  obtain ⟨f, h0, he, _⟩ := normalized_quadratic
    (1 + C Polynomial.X) (C Polynomial.X * X : PowerSeries (Polynomial ℚ))
  exact ⟨f, h0, by linear_combination he⟩

private theorem finite_subst (f u : PowerSeries ℚ) (hu : constantCoeff u = 0) (n : ℕ) :
    coeff n (f.subst u) = ∑ k ∈ range (n + 1), coeff k f * coeff n (u ^ k) := by
  rw [coeff_subst' (.of_constantCoeff_zero' hu)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply mem_range.mpr
  by_contra h
  have hz : coeff n (u ^ k) = 0 := by
    apply coeff_of_lt_order
    exact ((show (n : ENat) < (k : ENat) by exact_mod_cast (by omega : n < k)).trans_le
      (le_order_pow_of_constantCoeff_eq_zero k hu))
  exact hk (by simp [hz])

set_option backward.isDefEq.respectTransparency false in
private theorem rational_log_coefficient (c : PowerSeries ℚ) (y : ℚ)
    (he : c = (1 + X * c) * (1 + C y * X * c))
    (n : ℕ) (hn : 0 < n) :
    (n : ℚ) * coeff n (logOf c) =
      coeff n (((1 + X) * (1 + C y * X) : PowerSeries ℚ) ^ n) := by
  let f : PowerSeries ℚ := X * c
  let r : PowerSeries ℚ := (1 + X) * (1 + C y * X)
  let u := logOf r
  have hf : constantCoeff f = 0 := by simp [f]
  have hr : constantCoeff r = 1 := by simp [r]
  have hs : HasSubst f := .of_constantCoeff_zero' hf
  have hone : (1 : PowerSeries ℚ).subst f = 1 := by
    simpa using (subst_C (a := f) (1 : ℚ))
  have hcsub : c = r.subst f := by
    simpa [r, subst_mul hs, subst_add hs, subst_X hs, subst_C, ← PowerSeries.C_apply,
      hone, f, mul_assoc] using he
  have hroot : f = X * r.subst f := by simp only [f, ← hcsub]
  have hlog : logOf c = u.subst f := by
    simp only [u, logOf_eq]
    rw [subst_comp_subst_apply (.of_constantCoeff_zero' (by simp [hr])) hs]
    rw [subst_sub hs, hone, ← hcsub]
  have hd : derivative u * r = derivative r := by
    have h := D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums.logarithmic_derivative
      (r - 1) (by simp [hr])
    simpa only [u, logOf_eq, show (1 : PowerSeries ℚ) + (r - 1) = r by ring,
      map_sub, derivative_one, sub_zero] using h
  have heuler (v : PowerSeries ℚ) (k : ℕ) :
      coeff k (X * derivative v) = (k : ℚ) * coeff k v := by
    cases k with
    | zero => simp
    | succ k => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring
  have hsum : (n : ℚ) * coeff n (logOf c) = coeff n (X * derivative u * r ^ n) := by
    rw [hlog, finite_subst _ _ hf, Finset.mul_sum,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply sum_congr rfl
    intro k hk
    rw [heuler]
    by_cases hk0 : k = 0
    · subst k
      simp [coeff_one, hn.ne']
    have hl := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient
      f r hf hroot n k (by omega) (by have := mem_range.mp hk; omega)
    linear_combination coeff k u * hl
  have hp : r ^ n = r * r ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hder : derivative (r ^ n) = (n : PowerSeries ℚ) * (derivative u * r ^ n) := by
    rw [derivative_pow, hp]
    rw [show derivative u * (r * r ^ (n - 1)) = derivative r * r ^ (n - 1) by rw [← mul_assoc, hd]]
    ring
  have hh := congrArg (coeff n) (congrArg (fun z : PowerSeries ℚ => X * z) hder)
  rw [heuler] at hh
  have ht : coeff n (X * ((n : PowerSeries ℚ) * (derivative u * r ^ n))) =
      (n : ℚ) * coeff n (X * derivative u * r ^ n) := by
    rw [show X * ((n : PowerSeries ℚ) * (derivative u * r ^ n)) =
      C (n : ℚ) * (X * derivative u * r ^ n) by simp only [map_natCast]; ring, coeff_C_mul]
  rw [ht] at hh
  exact hsum.trans (mul_left_cancel₀ (by exact_mod_cast hn.ne') hh.symm)

private noncomputable def rowPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ range (n + 1), Polynomial.C ((n.choose k : ℚ) ^ 2) * Polynomial.X ^ k

private theorem rational_binomial_coefficient (y : ℚ) (n : ℕ) :
    coeff n (((1 + X) * (1 + C y * X) : PowerSeries ℚ) ^ n) =
      (rowPolynomial n).eval y := by
  have hscaled (k : ℕ) : coeff k ((1 + C y * X : PowerSeries ℚ) ^ n) =
      y ^ k * (n.choose k : ℚ) := by
    have hh : (1 + C y * X : PowerSeries ℚ) ^ n = rescale y ((1 + X) ^ n) := by
      simp only [map_pow, map_add, map_one, rescale_X]
    rw [hh, coeff_rescale, P13CatalanLagrangeBridge.binomialCoefficient]
  rw [mul_pow, mul_comm ((1 + X : PowerSeries ℚ) ^ n), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [rowPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply sum_congr rfl
  intro k hk
  rw [hscaled, P13CatalanLagrangeBridge.binomialCoefficient,
    Nat.choose_symm (by have := mem_range.mp hk; omega)]
  ring

private theorem polynomial_log_coefficient (c : PowerSeries (Polynomial ℚ))
    (hc : constantCoeff c = 1)
    (he : c = (1 + X * c) * (1 + C Polynomial.X * X * c))
    (n : ℕ) (hn : 0 < n) :
    coeff n (logOf c) = Polynomial.C (1 / (n : ℚ)) * rowPolynomial n := by
  apply Polynomial.funext
  intro y
  let e : Polynomial ℚ →+* ℚ := Polynomial.evalRingHom y
  have heq : c.map e = (1 + X * c.map e) * (1 + C y * X * c.map e) := by
    have h := congrArg (PowerSeries.map e) he
    simpa only [map_mul, map_add, map_one, map_X, map_C, e, Polynomial.coe_evalRingHom,
      Polynomial.eval_X] using h
  have hmap : (logOf c).map e = logOf (c.map e) := by
    have hz : HasSubst (c - 1) := .of_constantCoeff_zero' (by simp [hc])
    have h := PowerSeries.map_subst hz (h := e) (log (Polynomial ℚ))
    change PowerSeries.map e ((log (Polynomial ℚ)).subst (c - 1)) =
      ((log (Polynomial ℚ)).map e).subst (PowerSeries.map e (c - 1)) at h
    simpa only [logOf_eq, map_log, map_sub, map_one] using h
  have h := rational_log_coefficient (c.map e) y heq n hn
  rw [rational_binomial_coefficient] at h
  have hh : Polynomial.eval y (coeff n (logOf c)) = coeff n (logOf (c.map e)) := by
    simpa only [coeff_map, e, Polynomial.coe_evalRingHom] using congrArg (coeff n) hmap
  rw [Polynomial.eval_mul, Polynomial.eval_C, hh]
  have hne : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  linear_combination h

open scoped PowerSeries.WithPiTopology
private local instance : UniformSpace ℚ := ⊥
private local instance : UniformSpace (Polynomial ℚ) := ⊥

open D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion

private theorem diagonal_coeff (f : PowerSeries (Polynomial ℚ)) (m : ℕ) :
    coeff m (diagonal f) = ∑ n ∈ range (m + 1),
      coeff (m - n) ((Polynomial.eval₂RingHom C (1 + X)) (coeff n f)) := by
  have hs := PowerSeries.hasSum_eval₂
    (φ := Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) (1 + X))
    continuous_of_discreteTopology (PowerSeries.HasEval.X (R := ℚ)) f
  have hh := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mp hs m
  rw [← diagonal_apply f] at hh
  simp only [coeff_mul_X_pow'] at hh
  rw [← hh.tsum_eq, tsum_eq_sum (s := range (m + 1))]
  · apply sum_congr rfl
    intro n hn
    rw [ite_eq_left (by have := mem_range.mp hn; omega)]
  · intro n hn
    exact ite_eq_right (by have := hn; simp only [mem_range, not_lt] at this; omega)

private theorem diagonal_constant (f : PowerSeries (Polynomial ℚ))
    (hf : constantCoeff f = 1) : constantCoeff (diagonal f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, diagonal_coeff]
  simp [coeff_zero_eq_constantCoeff_apply, hf]

private theorem diagonal_log (c : PowerSeries (Polynomial ℚ))
    (hc : constantCoeff c = 1) : diagonal (logOf c) = logOf (diagonal c) := by
  have hm : (log ℚ).map (algebraMap ℚ (Polynomial ℚ)) = log (Polynomial ℚ) := map_log _
  have hs : HasSubst (c - 1) := .of_constantCoeff_zero' (by simp [hc])
  have hsub : subst (c - 1) (log ℚ) = logOf c := by
    rw [logOf_eq, ← hm, map_algebraMap_eq_subst_X,
      subst_comp_subst_apply HasSubst.X' hs, subst_X hs]
  rw [← hsub, diagonal_subst _ _ (by simp [hc])
    (by simp [diagonal_constant c hc]), map_sub, map_one]
  rfl

private theorem diagonal_log_eq (c : PowerSeries (Polynomial ℚ))
    (hc : constantCoeff c = 1)
    (he : c = (1 + X * c) * (1 + C Polynomial.X * X * c)) :
    logOf (diagonal c) = logarithm := by
  rw [← diagonal_log c hc]
  ext m
  rw [diagonal_coeff, logarithm, coeff_mk]
  have hterm (n : ℕ) (hn : 0 < n) :
      coeff (m - n) ((Polynomial.eval₂RingHom C (1 + X)) (coeff n (logOf c))) =
        (1 / (n : ℚ)) * coeff (m - n) (row n) := by
    rw [polynomial_log_coefficient c hc he n hn, map_mul]
    have hp : (Polynomial.eval₂RingHom C (1 + X : PowerSeries ℚ)) (rowPolynomial n) = row n := by
      simp [rowPolynomial, row, map_sum, map_mul, map_pow, Polynomial.coe_eval₂RingHom]
    rw [hp]
    simp [Polynomial.coe_eval₂RingHom, coeff_C_mul]
  rw [sum_range_succ']
  have hzero : coeff m ((Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) (1 + X))
      (coeff 0 (logOf c))) = 0 := by
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_logOf hc]
  rw [Nat.sub_zero, hzero, add_zero]
  rw [show Icc 1 m = (range m).image Nat.succ by
    ext i
    simp only [mem_Icc, mem_image, mem_range]
    constructor
    · intro hi; exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega, sum_image]
  · apply sum_congr rfl
    intro n hn
    exact hterm (n + 1) (by omega)
  · exact fun _ _ _ _ h => Nat.succ.inj h

private theorem branch_of_source (A : PowerSeries ℚ) (hA : IsSourceSeries A) :
    (∃! S : PowerSeries ℚ, constantCoeff S = 1 ∧ S ^ 2 = discriminant) ∧
    ∀ S : PowerSeries ℚ, constantCoeff S = 1 → S ^ 2 = discriminant →
      X ∣ (1 + X ^ 2) - S ∧ A = printedBranch S := by
  let s : PowerSeries ℚ := (1 + X ^ 2) - 2 * X * (1 + X) * A
  have hs0 : constantCoeff s = 1 := by simp [s]
  have hquad : (1 + X ^ 2) * A - X * (1 + X) * A ^ 2 = 1 := by
    linear_combination hA.2
  have hs : s ^ 2 = discriminant := by
    dsimp [s, discriminant]
    linear_combination -4 * X * (1 + X) * hquad
  have huniq (t : PowerSeries ℚ) (ht0 : constantCoeff t = 1)
      (ht : t ^ 2 = discriminant) : t = s := by
    have hz : (t - s) * (t + s) = 0 := by linear_combination ht - hs
    have hu : IsUnit (t + s) := isUnit_iff_constantCoeff.mpr (by simp [ht0, hs0])
    exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hz)
  refine ⟨⟨s, ⟨hs0, hs⟩, fun t ht => huniq t ht.1 ht.2⟩, ?_⟩
  intro t ht0 ht
  rw [huniq t ht0 ht]
  have hnum : (1 + X ^ 2) - s = X * (2 * (1 + X) * A) := by dsimp [s]; ring
  refine ⟨⟨2 * (1 + X) * A, hnum⟩, ?_⟩
  rw [printedBranch, hnum]
  have hshift : (mk fun n => coeff (n + 1) (X * (2 * (1 + X) * A))) = 2 * (1 + X) * A := by
    ext n
    simp
  rw [hshift]
  have hinv := PowerSeries.mul_inv_cancel (2 * (1 + X) : PowerSeries ℚ)
    (by simp only [map_mul, map_add, map_one, constantCoeff_X, add_zero]; norm_num [map_ofNat])
  calc
    A = A * (2 * (1 + X) * (2 * (1 + X))⁻¹) := by rw [hinv, mul_one]
    _ = _ := by ring

private theorem logarithm_zero : constantCoeff logarithm = 0 := by
  simp [logarithm, constantCoeff_mk]

private theorem logarithm_sum :
    HasSum (fun n : ℕ => C (1 / ((n + 1 : ℕ) : ℚ)) * row (n + 1) * X ^ (n + 1)) logarithm := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro m
  have hz (n : ℕ) (hn : n ∉ range m) :
      coeff m (C (1 / ((n + 1 : ℕ) : ℚ)) * row (n + 1) * X ^ (n + 1)) = 0 := by
    rw [coeff_mul_X_pow', ite_eq_right (by have := hn; simp only [mem_range, not_lt] at this; omega)]
  have hh := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hz
  convert hh using 1
  rw [logarithm, coeff_mk]
  rw [show Icc 1 m = (range m).image Nat.succ by
    ext i
    simp only [mem_Icc, mem_image, mem_range]
    constructor
    · intro hi; exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega,
    sum_image (by intro a ha b hb hab; exact Nat.succ.inj hab)]
  apply sum_congr rfl
  intro n hn
  rw [coeff_mul_X_pow', ite_eq_left (by have := mem_range.mp hn; omega), coeff_C_mul]

private theorem exponential_sum (f : PowerSeries ℚ) (hf : constantCoeff f = 0) :
    HasSum (fun j : ℕ => C (1 / (j.factorial : ℚ)) * f ^ j) (formalExp f) := by
  have hs : HasSubst f := .of_constantCoeff_zero' hf
  have hh := PowerSeries.hasSum_aeval hs.hasEval (exp ℚ)
  rw [← substAlgHom_eq_aeval hs] at hh
  have heq (j : ℕ) : coeff j (exp ℚ) • f ^ j = C (1 / (j.factorial : ℚ)) * f ^ j := by
    rw [coeff_exp]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    calc
      (1 / (j.factorial : ℚ)) • f ^ j =
          (algebraMap ℚ (PowerSeries ℚ)) (1 / (j.factorial : ℚ)) • f ^ j :=
        (algebraMap_smul (PowerSeries ℚ) _ _).symm
      _ = _ := by rw [algebraMap_eq, smul_eq_mul]
  simpa only [heq, coe_substAlgHom, formalExp] using hh

/-- Bala's whole-series identity, with its independent source and formal branch. -/
theorem result :
    (∃! A : PowerSeries ℚ, IsSourceSeries A) ∧
    constantCoeff logarithm = 0 ∧
    HasSum (fun n : ℕ => C (1 / ((n + 1 : ℕ) : ℚ)) * row (n + 1) * X ^ (n + 1)) logarithm ∧
    (∀ m n : ℕ, m < n → coeff m (C (1 / (n : ℚ)) * row n * X ^ n) = 0) ∧
    HasSum (fun j : ℕ => C (1 / (j.factorial : ℚ)) * logarithm ^ j) (formalExp logarithm) ∧
    (∀ m j : ℕ, m < j → coeff m (logarithm ^ j) = 0) ∧
    (∀ m : ℕ, coeff m (formalExp logarithm) =
      ∑ j ∈ range (m + 1), (1 / (j.factorial : ℚ)) * coeff m (logarithm ^ j)) ∧
    ∀ A : PowerSeries ℚ, IsSourceSeries A →
      A = 1 + X * formalExp logarithm ∧
      (∀ m : ℕ, coeff m A = coeff m (1 + X * formalExp logarithm)) ∧
      (∃! S : PowerSeries ℚ, constantCoeff S = 1 ∧ S ^ 2 = discriminant) ∧
      ∀ S : PowerSeries ℚ, constantCoeff S = 1 → S ^ 2 = discriminant →
        X ∣ (1 + X ^ 2) - S ∧ A = printedBranch S := by
  have hzero := logarithm_zero
  refine ⟨source_exists, hzero, logarithm_sum, ?_, exponential_sum logarithm hzero, ?_, ?_, ?_⟩
  · intro m n hmn
    rw [coeff_mul_X_pow', ite_eq_right (by omega)]
  · intro m j hmj
    apply coeff_of_lt_order
    exact (show (m : ENat) < (j : ENat) by exact_mod_cast hmj).trans_le
      (le_order_pow_of_constantCoeff_eq_zero j hzero)
  · intro m
    simpa only [formalExp, coeff_exp, Algebra.algebraMap_self, RingHom.id_apply] using
      finite_subst (exp ℚ) logarithm hzero m
  · obtain ⟨c, hc, he⟩ := auxiliary_exists
    let b := diagonal c
    have hb0 : constantCoeff b = 1 := diagonal_constant c hc
    have hb : b = (1 + X * b) * (1 + (1 + X) * X * b) := by
      have h := congrArg diagonal he
      simpa only [map_mul, map_add, map_one, diagonal_X, diagonal_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, b] using h
    have hl : logOf b = logarithm := diagonal_log_eq c hc he
    have hexp : formalExp logarithm = b := by
      have hs : HasSubst (b - 1) := .of_constantCoeff_zero' (by simp [hb0])
      have hh := congrArg (subst (b - 1)) (subst_exp_log (A := ℚ))
      rw [subst_comp_subst_apply HasSubst.log hs] at hh
      have h1 : (1 : PowerSeries ℚ).subst (b - 1) = 1 := by
        rw [← coe_substAlgHom hs, map_one]
      rw [subst_add hs, h1, subst_X hs] at hh
      change formalExp (logOf b) = 1 + (b - 1) at hh
      rw [hl] at hh
      convert hh using 1; ring
    have hstar : IsSourceSeries (1 + X * b) := by
      refine ⟨by simp, ?_⟩
      linear_combination X * hb
    obtain ⟨a, ha, hu⟩ := source_exists
    intro A hA
    have hAe : A = 1 + X * formalExp logarithm := by
      rw [hexp]
      exact (hu A hA).trans (hu (1 + X * b) hstar).symm
    exact ⟨hAe, fun m => congrArg (coeff m) hAe, branch_of_source A hA⟩

end D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential
