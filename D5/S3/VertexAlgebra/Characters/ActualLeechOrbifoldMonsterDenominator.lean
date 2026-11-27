/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldMonsterDenominator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldMonsterDenominator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The coefficientwise Monster denominator Euler product for the native Leech character. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldFaberLogarithm

/-! The finite Euler products stabilize coefficientwise at the native
Faber–Hecke denominator. The specialization to one variable sums the
coefficients of each total degree. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Nat

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldMonsterDenominator

open PowerSeries Finset
open ActualLeechOrbifoldFaberLogarithm
  (denominator constantCoeff_denominator coeff_coeff_denominator_succ
    logOf_mul derivative_logOf_mul coeff_coeff_neg_logOf_denominator)

local notation "c" => ActualLeechOrbifoldHeckeExpansion.coeff

/-- The exponent of the Euler factor of bidegree `(r,s)` is the native
dimension in weight `rs + 1`. -/
def multiplicity (r s : ℕ) : ℕ :=
  ActualLeechOrbifoldTraceSeries.dimension ((↑(r * s) : ℤ) + 1)

@[simp] theorem cast_multiplicity (r s : ℕ) : (multiplicity r s : ℂ) = c (r * s) :=
  rfl

private def factor {R : Type*} [CommRing R] (r s : ℕ) : PowerSeries (PowerSeries R) :=
  1 - C ((X : PowerSeries R) ^ s) * X ^ r

/-- The actual finite Euler product over the square `1 ≤ r,s ≤ N`. -/
def finiteProduct (N : ℕ) (R : Type*) [CommRing R] : PowerSeries (PowerSeries R) :=
  ∏ x ∈ Icc 1 N ×ˢ Icc 1 N, factor x.1 x.2 ^ multiplicity x.1 x.2

private theorem constantCoeff_factor {r : ℕ} (hr : 0 < r) (s : ℕ) :
    constantCoeff (factor (R := ℂ) r s) = 1 := by
  simp [factor, hr.ne']

@[simp] theorem constantCoeff_finiteProduct (N : ℕ) :
    constantCoeff (finiteProduct N ℂ) = 1 := by
  rw [finiteProduct, map_prod]
  apply prod_eq_one
  intro x hx
  have hr : 0 < x.1 := (mem_Icc.mp (mem_product.mp hx).1).1
  rw [map_pow, constantCoeff_factor hr, one_pow]

private theorem neg_logOf_prod {A ι : Type*} [CommRing A] [Algebra ℚ A]
    (S : Finset ι) (f : ι → PowerSeries A) (hf : ∀ i ∈ S, constantCoeff (f i) = 1) :
    -logOf (∏ i ∈ S, f i) = ∑ i ∈ S, -logOf (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [logOf_eq, subst_zero_of_constantCoeff_zero constantCoeff_log]
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, constantCoeff (f i) = 1 := fun i hi => hf i (mem_insert_of_mem hi)
    have hP : constantCoeff (∏ i ∈ S, f i) = 1 := by
      rw [map_prod]
      exact prod_eq_one hS
    rw [prod_insert ha, logOf_mul (hf a (mem_insert_self a S)) hP, neg_add,
      sum_insert ha, ih hS]

private theorem neg_logOf_pow {A : Type*} [CommRing A] [Algebra ℚ A]
    {F : PowerSeries A} (hF : constantCoeff F = 1) (k : ℕ) :
    -logOf (F ^ k) = k • (-logOf F) := by
  induction k with
  | zero => simp [logOf_eq, subst_zero_of_constantCoeff_zero constantCoeff_log]
  | succ k ih =>
    rw [pow_succ, logOf_mul (by rw [map_pow, hF, one_pow]) hF, neg_add, ih, succ_nsmul]

private theorem neg_coeff_rescale_log {A : Type*} [CommRing A] [Algebra ℚ A]
    (b : A) {a : ℕ} (ha : 0 < a) :
    -coeff a (rescale (-b) (log A)) = algebraMap ℚ A (1 / (a : ℚ)) * b ^ a := by
  have hrat : (-1 : ℚ) ^ a * ((-1 : ℚ) ^ (a + 1) / (a : ℚ)) = -(1 / (a : ℚ)) := by
    rw [← mul_div_assoc, pow_succ, ← mul_assoc, ← mul_pow]
    norm_num [div_eq_mul_inv]
  have h := congrArg (algebraMap ℚ A) hrat
  simp only [map_mul, map_pow, map_neg, map_one] at h
  rw [coeff_rescale, coeff_log, ite_eq_right ha.ne', ← neg_one_mul b, mul_pow,
    mul_right_comm, h, neg_mul, neg_neg]

private theorem coeff_neg_logOf_one_sub {A : Type*} [CommRing A] [Algebra ℚ A]
    (b : A) {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    coeff n (-logOf (1 - C b * X ^ r)) =
      if r ∣ n then algebraMap ℚ A (1 / (n / r : ℕ)) * b ^ (n / r) else 0 := by
  have hx : HasSubst ((X : PowerSeries A) ^ r) := .X_pow hr.ne'
  have hlog : logOf (1 - C b * X ^ r : PowerSeries A) =
      (rescale (-b) (log A)).subst ((X : PowerSeries A) ^ r) := by
    rw [logOf_eq, rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' (-b)) hx,
      subst_smul hx, subst_X hx, smul_eq_C_mul, map_neg]
    congr 1
    ring
  rw [hlog, map_neg, coeff_subst_X_pow hr.ne']
  split_ifs with hd
  · have ha : 0 < n / r := Nat.div_pos (Nat.le_of_dvd hn hd) hr
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using neg_coeff_rescale_log b ha
  · exact neg_zero

private theorem coeff_coeff_neg_logOf_factor {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (s m : ℕ) :
    coeff m (coeff n (-logOf (factor r s))) =
      if r ∣ n ∧ m = s * (n / r) then 1 / ((n / r : ℕ) : ℂ) else 0 := by
  rw [factor, coeff_neg_logOf_one_sub _ hr hn]
  by_cases hd : r ∣ n
  · rw [ite_eq_left hd]
    have halg (z : ℚ) : algebraMap ℚ (PowerSeries ℂ) z = C (algebraMap ℚ ℂ z) :=
      (RingHom.map_rat_algebraMap (C (R := ℂ)) z).symm
    rw [halg, ← pow_mul, coeff_C_mul_X_pow]
    simp [hd]
  · simp [hd]

private theorem coeff_coeff_neg_logOf_finiteProduct_sum (N n m : ℕ) (hn : 0 < n) :
    coeff m (coeff n (-logOf (finiteProduct N ℂ))) =
      ∑ x ∈ Icc 1 N ×ˢ Icc 1 N,
        if x.1 ∣ n ∧ m = x.2 * (n / x.1) then c (x.1 * x.2) / ((n / x.1 : ℕ) : ℂ)
        else 0 := by
  rw [finiteProduct, neg_logOf_prod]
  · simp only [map_sum]
    apply sum_congr rfl
    intro x hx
    have hr : 0 < x.1 := (mem_Icc.mp (mem_product.mp hx).1).1
    rw [neg_logOf_pow (constantCoeff_factor hr x.2), map_nsmul, map_nsmul,
      coeff_coeff_neg_logOf_factor hr hn]
    split_ifs <;> simp [nsmul_eq_mul, div_eq_mul_inv]
  · intro x hx
    have hr : 0 < x.1 := (mem_Icc.mp (mem_product.mp hx).1).1
    rw [map_pow, constantCoeff_factor hr, one_pow]

/-- The negative logarithm of the finite Euler product has the Faber–Hecke
divisor sum at every positive bidegree inside the square. -/
theorem coeff_coeff_neg_logOf_finiteProduct {N n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnN : n ≤ N) (hmN : m ≤ N) :
    coeff m (coeff n (-logOf (finiteProduct N ℂ))) =
      ∑ a ∈ (n.gcd m).divisors, c ((n / a) * (m / a)) / (a : ℂ) := by
  rw [coeff_coeff_neg_logOf_finiteProduct_sum N n m hn, ← sum_filter]
  have hg : n.gcd m ≠ 0 := by
    exact ne_zero_of_dvd_ne_zero hn.ne' (Nat.gcd_dvd_left n m)
  have hindex (x : ℕ × ℕ)
      (hx : x ∈ (Icc 1 N ×ˢ Icc 1 N).filter fun x => x.1 ∣ n ∧ m = x.2 * (n / x.1)) :
      n / x.1 ∈ (n.gcd m).divisors ∧
        n / (n / x.1) = x.1 ∧ m / (n / x.1) = x.2 := by
    obtain ⟨hbox, hd, he⟩ := mem_filter.mp hx
    have hr : 0 < x.1 := (mem_Icc.mp (mem_product.mp hbox).1).1
    have ha : 0 < n / x.1 := Nat.div_pos (Nat.le_of_dvd hn hd) hr
    have hnEq : x.1 * (n / x.1) = n := Nat.mul_div_cancel' hd
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_gcd ?_ ?_, hg⟩, ?_, ?_⟩
    · exact ⟨x.1, by rw [mul_comm]; exact hnEq.symm⟩
    · exact ⟨x.2, by simpa [mul_comm] using he⟩
    · conv_lhs => lhs; rw [← hnEq]
      exact Nat.mul_div_cancel _ ha
    · conv_lhs => lhs; rw [he]
      exact Nat.mul_div_cancel _ ha
  refine sum_bij (fun x _ => n / x.1) (fun x hx => (hindex x hx).1) ?_ ?_ ?_
  · intro x hx y hy e
    obtain ⟨_, hxn, hxm⟩ := hindex x hx
    obtain ⟨_, hyn, hym⟩ := hindex y hy
    exact Prod.ext (hxn.symm.trans (e ▸ hyn)) (hxm.symm.trans (e ▸ hym))
  · intro a ha
    have hd := Nat.dvd_of_mem_divisors ha
    have han : a ∣ n := hd.trans (Nat.gcd_dvd_left n m)
    have ham : a ∣ m := hd.trans (Nat.gcd_dvd_right n m)
    have hap : 0 < a := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hn.ne' han)
    have hna : 0 < n / a := Nat.div_pos (Nat.le_of_dvd hn han) hap
    have hma : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm ham) hap
    have hnEq : (n / a) * a = n := Nat.div_mul_cancel han
    have hquot : n / (n / a) = a := by
      conv_lhs => lhs; rw [← hnEq]
      exact Nat.mul_div_cancel_left _ hna
    refine ⟨(n / a, m / a), mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩, hquot⟩
    · exact mem_Icc.mpr ⟨hna, (Nat.div_le_self _ _).trans hnN⟩
    · exact mem_Icc.mpr ⟨hma, (Nat.div_le_self _ _).trans hmN⟩
    · exact ⟨a, hnEq.symm⟩
    · change m = (m / a) * (n / (n / a))
      rw [hquot, Nat.div_mul_cancel ham]
  · intro x hx
    obtain ⟨_, hxn, hxm⟩ := hindex x hx
    rw [hxn, hxm]

/-- Agreement of the negative logarithms at all coefficients in the square,
including both axes. -/
theorem coeff_coeff_neg_logOf_finiteProduct_eq {N n m : ℕ} (hnN : n ≤ N) (hmN : m ≤ N) :
    coeff m (coeff n (-logOf (finiteProduct N ℂ))) =
      coeff m (coeff n (-logOf denominator)) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [coeff_zero_eq_constantCoeff_apply]
    rw [ActualLeechOrbifoldFaberLogarithm.constantCoeff_neg_logOf_denominator, map_neg,
      constantCoeff_logOf (constantCoeff_finiteProduct N), neg_zero]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp only [coeff_zero_eq_constantCoeff_apply]
    rw [ActualLeechOrbifoldFaberLogarithm.constantCoeff_coeff_neg_logOf_denominator,
      ← coeff_zero_eq_constantCoeff_apply, coeff_coeff_neg_logOf_finiteProduct_sum N n 0 hn]
    apply sum_eq_zero
    intro x hx
    have hr : 0 < x.1 := (mem_Icc.mp (mem_product.mp hx).1).1
    have hs : 0 < x.2 := (mem_Icc.mp (mem_product.mp hx).2).1
    split_ifs with h
    · exact ((Nat.mul_pos hs (Nat.div_pos (Nat.le_of_dvd hn h.1) hr)).ne' h.2.symm).elim
    · rfl
  rw [coeff_coeff_neg_logOf_finiteProduct hn hm hnN hmN,
    coeff_coeff_neg_logOf_denominator hn]

private theorem coeff_mul_congr_through {A : Type*} [Semiring A]
    {F G U V : PowerSeries A} (n : ℕ)
    (hF : ∀ i ≤ n, coeff i F = coeff i G) (hU : ∀ i ≤ n, coeff i U = coeff i V) :
    coeff n (F * U) = coeff n (G * V) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply sum_congr rfl
  intro x hx
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [hF _ (by omega), hU _ (by omega)]

private theorem coeff_eq_of_logOf_agree {F G : PowerSeries (PowerSeries ℂ)}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) {N M : ℕ}
    (hlog : ∀ i ≤ N, ∀ j ≤ M, coeff j (coeff i (logOf F)) = coeff j (coeff i (logOf G))) :
    ∀ n ≤ N, ∀ m ≤ M, coeff m (coeff n F) = coeff m (coeff n G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn m hm
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff_apply, hF, hG]
    | succ n =>
      have hd (H : PowerSeries (PowerSeries ℂ)) (hH : constantCoeff H = 1) :
          coeff m (coeff n (derivative (logOf H) * H)) =
            coeff m (coeff (n + 1) H) * ((n + 1 : ℕ) : ℂ) := by
        rw [derivative_logOf_mul hH, coeff_derivative, ← Nat.cast_succ, coeff_mul_natCast]
      have hmul :
          coeff m (coeff n (derivative (logOf F) * F)) =
            coeff m (coeff n (derivative (logOf G) * G)) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum, map_sum]
        apply sum_congr rfl
        intro x hx
        have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        apply coeff_mul_congr_through
        · intro j hj
          simp only [coeff_derivative, ← Nat.cast_succ, coeff_mul_natCast]
          rw [hlog _ (by omega) _ (hj.trans hm)]
        · intro j hj
          exact ih _ (by omega) (by omega) _ (hj.trans hm)
      rw [hd F hF, hd G hG] at hmul
      exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n) hmul

/-- For any fixed bidegree, every square containing that bidegree has the
exact coefficient of the native denominator. This is the formal Euler
product identity in coefficientwise form. -/
theorem coeff_coeff_finiteProduct {N n m : ℕ} (hn : n ≤ N) (hm : m ≤ N) :
    coeff m (coeff n (finiteProduct N ℂ)) = coeff m (coeff n denominator) := by
  apply coeff_eq_of_logOf_agree (constantCoeff_finiteProduct N) constantCoeff_denominator
    (N := N) (M := N) _ n hn m hm
  intro i hi j hj
  have h := coeff_coeff_neg_logOf_finiteProduct_eq hi hj
  simpa only [map_neg, neg_inj] using h

open Finset.HasAntidiagonal

private def diagonalSeries (F : PowerSeries (PowerSeries ℂ)) : PowerSeries ℂ :=
  mk fun d => ∑ x ∈ antidiagonal d, coeff x.2 (coeff x.1 F)

private theorem diagonalSeries_monomial (z : ℂ) (r s : ℕ) :
    diagonalSeries (C (C z * X ^ s) * X ^ r) = C z * X ^ (r + s) := by
  apply PowerSeries.ext
  intro d
  rw [diagonalSeries, coeff_mk, coeff_C_mul_X_pow]
  by_cases h : d = r + s
  · subst d
    rw [ite_eq_left rfl, sum_eq_single (r, s)]
    · rw [coeff_C_mul_X_pow, ite_eq_left rfl, coeff_C_mul_X_pow, ite_eq_left rfl]
    · intro x hx hne
      have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hr : x.1 ≠ r := by
        intro h
        exact hne (Prod.ext h (by omega))
      rw [coeff_C_mul_X_pow, ite_eq_right hr, map_zero]
    · simp
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro x hx
    have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_cases hr : x.1 = r
    · have hs : x.2 ≠ s := by omega
      rw [coeff_C_mul_X_pow, ite_eq_left hr, coeff_C_mul_X_pow, ite_eq_right hs]
    · rw [coeff_C_mul_X_pow, ite_eq_right hr, map_zero]

private theorem diagonalSeries_mul (F G : PowerSeries (PowerSeries ℂ)) :
    diagonalSeries (F * G) = diagonalSeries F * diagonalSeries G := by
  apply PowerSeries.ext
  intro d
  simp only [diagonalSeries, coeff_mk, PowerSeries.coeff_mul, map_sum]
  simp only [sum_mul]
  simp only [mul_sum]
  simp_rw [← sum_product', sum_sigma']
  -- Transpose the two convolution indices to group each factor by total degree.
  let transpose : (Σ _ : ℕ × ℕ, (ℕ × ℕ) × (ℕ × ℕ)) →
      (Σ _ : ℕ × ℕ, (ℕ × ℕ) × (ℕ × ℕ)) :=
    fun x => ⟨(x.2.1.1 + x.2.2.1, x.2.1.2 + x.2.2.2),
      ((x.2.1.1, x.2.2.1), (x.2.1.2, x.2.2.2))⟩
  have hmem (x : Σ _ : ℕ × ℕ, (ℕ × ℕ) × (ℕ × ℕ)) :
      x ∈ (antidiagonal d).sigma (fun a => antidiagonal a.1 ×ˢ antidiagonal a.2) →
        transpose x ∈ (antidiagonal d).sigma
          (fun a => antidiagonal a.1 ×ˢ antidiagonal a.2) := by
    simp only [mem_sigma, mem_product, Finset.HasAntidiagonal.mem_antidiagonal]
    rintro ⟨hdegree, hx, hy⟩
    exact ⟨by dsimp [transpose]; omega, rfl, rfl⟩
  have hinv (x : Σ _ : ℕ × ℕ, (ℕ × ℕ) × (ℕ × ℕ))
      (hx : x ∈ (antidiagonal d).sigma (fun a => antidiagonal a.1 ×ˢ antidiagonal a.2)) :
      transpose (transpose x) = x := by
    rcases x with ⟨a, x, y⟩
    obtain ⟨_, hx, hy⟩ := by
      simpa only [mem_sigma, mem_product, Finset.HasAntidiagonal.mem_antidiagonal] using hx
    simp [transpose, hx, hy]
  exact sum_nbij' transpose transpose hmem hmem hinv hinv (fun _ _ => rfl)

/-- Formal specialization `p = q = t`, using finite total-degree slices. -/
def diagonal : PowerSeries (PowerSeries ℂ) →+* PowerSeries ℂ where
  toFun := diagonalSeries
  map_zero' := PowerSeries.ext fun d => by simp [diagonalSeries]
  map_one' := by simpa using diagonalSeries_monomial 1 0 0
  map_add' F G := PowerSeries.ext fun d => by simp [diagonalSeries, sum_add_distrib]
  map_mul' := diagonalSeries_mul

/-- The coefficient of the specialization is the sum over the total-degree slice. -/
theorem coeff_diagonal (F : PowerSeries (PowerSeries ℂ)) (d : ℕ) :
    coeff d (diagonal F) = ∑ x ∈ antidiagonal d, coeff x.2 (coeff x.1 F) :=
  by simp only [diagonal, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    diagonalSeries, coeff_mk]

/-- The actual univariate finite product after setting `p = q = t`. -/
def finiteDiagonalProduct (N : ℕ) (R : Type*) [CommRing R] : PowerSeries R :=
  ∏ x ∈ Icc 1 N ×ˢ Icc 1 N, (1 - X ^ (x.1 + x.2)) ^ multiplicity x.1 x.2

theorem diagonal_finiteProduct (N : ℕ) : diagonal (finiteProduct N ℂ) = finiteDiagonalProduct N ℂ := by
  rw [finiteProduct, finiteDiagonalProduct, map_prod]
  apply prod_congr rfl
  intro x _
  rw [map_pow, factor, map_sub, map_one]
  congr 2
  change diagonalSeries (C ((X : PowerSeries ℂ) ^ x.2) * X ^ x.1) = _
  simpa only [map_one, one_mul] using diagonalSeries_monomial 1 x.1 x.2

private theorem constantCoeff_coeff_denominator_succ (i : ℕ) :
    constantCoeff (coeff (i + 1) denominator) = 0 := by
  simp [denominator, coeff_succ_X_mul]

private theorem coeff_diagonal_denominator_succ_succ (d : ℕ) :
    coeff (d + 2) (diagonal denominator) = -(d + 1 : ℂ) * c (d + 1) := by
  rw [coeff_diagonal, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  simp only [coeff_zero_eq_constantCoeff_apply, constantCoeff_denominator,
    coeff_one, constantCoeff_coeff_denominator_succ, zero_add]
  rw [show (∑ a ∈ antidiagonal d, coeff (a.2 + 1) (coeff (a.1 + 1) denominator)) =
      ∑ _a ∈ antidiagonal d, -c (d + 1) by
    apply sum_congr rfl
    intro a ha
    rw [coeff_coeff_denominator_succ, Finset.HasAntidiagonal.mem_antidiagonal.mp ha]]
  simp [nsmul_eq_mul, Nat.cast_add]
  ring

/-- The one-variable denominator is `1 - ∑_{d ≥ 2} (d-1)c(d-1)t^d`. -/
def diagonalDenominator : PowerSeries ℂ :=
  1 - X ^ 2 * mk (fun d => (d + 1 : ℂ) * c (d + 1))

theorem diagonal_denominator : diagonal denominator = diagonalDenominator := by
  apply PowerSeries.ext
  intro d
  cases d with
  | zero =>
    simp [diagonalDenominator, coeff_diagonal, constantCoeff_denominator]
  | succ d =>
    cases d with
    | zero =>
      rw [coeff_diagonal, Finset.Nat.sum_antidiagonal_succ]
      simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_coeff_denominator_succ,
        diagonalDenominator, coeff_X_pow_mul']
    | succ d =>
      rw [coeff_diagonal_denominator_succ_succ]
      simp [diagonalDenominator, coeff_X_pow_mul', show d + 2 - 2 = d by omega]
      ring

/-- The actual univariate finite Euler product agrees with the native
diagonal denominator through degree `N`. -/
theorem coeff_finiteDiagonalProduct {N d : ℕ} (hd : d ≤ N) :
    coeff d (finiteDiagonalProduct N ℂ) = coeff d diagonalDenominator := by
  rw [← diagonal_finiteProduct, ← diagonal_denominator, coeff_diagonal, coeff_diagonal]
  apply sum_congr rfl
  intro x hx
  have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  exact coeff_coeff_finiteProduct (by omega) (by omega)

local notation "ιℤ" => (Int.castRingHom ℂ)

/-- The integral denominator with coefficients given by the native dimensions. -/
def integerDenominator : PowerSeries (PowerSeries ℤ) :=
  1 - X * PowerSeries.mk (fun i => X * PowerSeries.mk (fun j => (multiplicity 1 (i + 1 + j) : ℤ)))

private theorem map_integerDenominator :
    integerDenominator.map (PowerSeries.map ιℤ) = denominator := by
  have h :
      PowerSeries.map (PowerSeries.map ιℤ)
        (PowerSeries.mk fun i => X * PowerSeries.mk fun j => (multiplicity 1 (i + 1 + j) : ℤ)) =
      PowerSeries.mk (fun i => X * PowerSeries.mk fun j => c (i + 1 + j)) := by
    apply PowerSeries.ext
    intro i
    rw [coeff_map, coeff_mk, coeff_mk, map_mul, map_X]
    apply congrArg (fun G : PowerSeries ℂ => X * G)
    apply PowerSeries.ext
    intro j
    simp [coeff_map, coeff_mk]
  rw [integerDenominator, map_sub, map_one, map_mul, map_X, h]
  rfl

private theorem map_finiteProduct_int (N : ℕ) :
    (finiteProduct N ℤ).map (PowerSeries.map ιℤ) = finiteProduct N ℂ := by
  simp only [finiteProduct, factor, map_prod, map_pow, map_sub, map_one, map_mul, map_C, map_X]

/-- The bivariate coefficient identity holds over the integers. -/
theorem coeff_coeff_finiteProduct_int {N n m : ℕ} (hn : n ≤ N) (hm : m ≤ N) :
    coeff m (coeff n (finiteProduct N ℤ)) = coeff m (coeff n integerDenominator) := by
  have h := coeff_coeff_finiteProduct hn hm
  rw [← map_finiteProduct_int N, ← map_integerDenominator, coeff_map, coeff_map,
    coeff_map, coeff_map] at h
  exact Int.cast_injective h

/-- The integral diagonal denominator has the coefficient `-(d-1)c(d-1)`
in each degree `d ≥ 2`. -/
def integerDiagonalDenominator : PowerSeries ℤ :=
  1 - X ^ 2 * mk (fun d => (d + 1 : ℤ) * (multiplicity 1 (d + 1) : ℤ))

private theorem map_integerDiagonalDenominator :
    integerDiagonalDenominator.map ιℤ = diagonalDenominator := by
  have h :
      PowerSeries.map ιℤ (mk fun d => (d + 1 : ℤ) * (multiplicity 1 (d + 1) : ℤ)) =
        mk (fun d => (d + 1 : ℂ) * c (d + 1)) := by
    apply PowerSeries.ext
    intro d
    simp [coeff_map, coeff_mk]
  rw [integerDiagonalDenominator, diagonalDenominator, map_sub, map_one, map_mul, map_pow,
    map_X, h]

private theorem map_finiteDiagonalProduct_int (N : ℕ) :
    (finiteDiagonalProduct N ℤ).map ιℤ = finiteDiagonalProduct N ℂ := by
  simp only [finiteDiagonalProduct, map_prod, map_pow, map_sub, map_one, map_X]

/-- The univariate coefficient identity through degree `N` holds over the integers. -/
theorem coeff_finiteDiagonalProduct_int {N d : ℕ} (hd : d ≤ N) :
    coeff d (finiteDiagonalProduct N ℤ) = coeff d integerDiagonalDenominator := by
  have h := coeff_finiteDiagonalProduct hd
  rw [← map_finiteDiagonalProduct_int N, ← map_integerDiagonalDenominator, coeff_map,
    coeff_map] at h
  exact Int.cast_injective h

end D5.S3.VertexAlgebra.ActualLeechOrbifoldMonsterDenominator
