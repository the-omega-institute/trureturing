/- GID: D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Even integral rescaling and triangular composition prove Scheuerle A381670. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Dyadic denominators of the compositional-square solution

Thomas Scheuerle's OEIS A381670 (March 3, 2025) conjectures that the reduced
denominators of the rational solution of `X * (A + 1) = A.subst A`, with
constant coefficient zero and linear coefficient one, are powers of two.
See `Library/ArithSums/scheuerle2025a381670.md`.

Construct the rescaled series `F(x) = A(4x)/4` over the integers. If two series
tangent to `X` agree below degree `n`, their compositional squares differ at
that degree by twice their coefficient difference. Thus the residual at degree
`n` is removed by one correction, without changing any lower coefficient.

The integrality step takes place entirely over the integers: if `P-X = 2Q`,
then `Q(P)-Q(X)` is divisible by 2, since each difference `P^k-X^k` is.
Consequently `P(P)-X-4XP` is divisible by 4. Its half is therefore even.
Compatible corrected approximations give `F`; conjugation by the linear
scaling gives the required rational solution `A`. This construction also
covers zero coefficients, whose reduced denominator is one.
-/

open PowerSeries
namespace D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans
    (sub_dvd_pow_sub_pow f g k))

private theorem pow_low {f : PowerSeries R} (hf : constantCoeff f = 0)
    {n k : ℕ} (hn : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) k) n hn

private theorem agree_subst {d : ℕ} {f g u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (ho : Agree d f g) (hi : Agree d u v) : Agree d (f.subst u) (g.subst v) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [ho k hk, agree_pow hi k n hn]
  · rw [pow_low hu (by omega : n < k), pow_low hv (by omega : n < k),
      smul_zero, smul_zero]

private theorem pow_agree_extra {d k : ℕ} {u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree d u v) (hk : 2 ≤ k) : Agree (d + 1) (u ^ k) (v ^ k) := by
  apply (agree_iff _ _ _).mpr
  have hd := (agree_iff _ _ _).mp h
  have hu' : X ∣ u ^ (k - 1) :=
    (X_dvd_iff.mpr hu).trans (dvd_pow_self u (by omega))
  have hp : X ^ d ∣ u ^ (k - 1) - v ^ (k - 1) :=
    hd.trans (sub_dvd_pow_sub_pow u v (k - 1))
  have hfirst : X ^ (d + 1) ∣ (u - v) * u ^ (k - 1) := by
    simpa only [pow_succ] using mul_dvd_mul hd hu'
  have hsecond : X ^ (d + 1) ∣ v * (u ^ (k - 1) - v ^ (k - 1)) := by
    simpa only [pow_succ, mul_comm X] using mul_dvd_mul (X_dvd_iff.mpr hv) hp
  have huk : u ^ k = u * u ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hvk : v ^ k = v * v ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  convert dvd_add hfirst hsecond using 1
  rw [huk, hvk]
  ring

private theorem pow_diagonal {v : PowerSeries R} (hv : constantCoeff v = 0)
    (hv1 : coeff 1 v = 1) (n : ℕ) : coeff n (v ^ n) = 1 := by
  obtain ⟨u, rfl⟩ := X_dvd_iff.mpr hv
  have hu : constantCoeff u = 1 := by simpa using hv1
  rw [mul_pow]
  simpa [coeff_zero_eq_constantCoeff, hu] using coeff_X_pow_mul (u ^ n) n 0

private theorem subst_inner_top {d : ℕ} {f u v : PowerSeries R}
    (hf1 : coeff 1 f = 1) (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree d u v) :
    coeff d (f.subst u) - coeff d (f.subst v) = coeff d u - coeff d v := by
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv),
    ← finsum_sub_distrib (coeff_subst_finite' (.of_constantCoeff_zero hu) f d)
      (coeff_subst_finite' (.of_constantCoeff_zero hv) f d)]
  rw [finsum_eq_single _ 1]
  · simp [hf1]
  · intro k hk
    obtain (_ | _ | k) := k
    · simp
    · exact (hk rfl).elim
    · rw [pow_agree_extra hu hv h (by omega) d (by omega)]
      simp

private theorem subst_outer_top {d : ℕ} {f g v : PowerSeries R}
    (hv : constantCoeff v = 0) (hv1 : coeff 1 v = 1) (h : Agree d f g) :
    coeff d (f.subst v) - coeff d (g.subst v) = coeff d f - coeff d g := by
  rw [coeff_subst' (.of_constantCoeff_zero hv), coeff_subst' (.of_constantCoeff_zero hv),
    ← finsum_sub_distrib (coeff_subst_finite' (.of_constantCoeff_zero hv) f d)
      (coeff_subst_finite' (.of_constantCoeff_zero hv) g d)]
  rw [finsum_eq_single _ d]
  · simp [pow_diagonal hv hv1]
  · intro k hk
    by_cases hkd : k < d
    · rw [h k hkd]; simp
    · rw [pow_low hv (by omega : d < k)]; simp

/-- The responsive coefficient has multiplier two, independently of its degree. -/
private theorem composition_top {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree d f g) :
    coeff d (f.subst f) - coeff d (g.subst g) = 2 * (coeff d f - coeff d g) := by
  have hi := subst_inner_top hf1 hf hg h
  have ho := subst_outer_top hg hg1 h
  linear_combination hi + ho

private noncomputable def residual (p : PowerSeries R) : PowerSeries R :=
  p.subst p - X - 4 * X * p

private theorem residual_agree {d : ℕ} {p q : PowerSeries R}
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0) (h : Agree d p q) :
    Agree d (residual p) (residual q) := by
  intro n hn
  have hs := agree_subst hp hq h h n hn
  simp only [residual, map_sub]
  rw [hs]
  congr 1
  cases n with
  | zero => simp
  | succ n =>
    rw [show (4 : PowerSeries R) * X * p = C 4 * (X * p) by change 4 * X * _ = 4 * (X * _); ring,
      show (4 : PowerSeries R) * X * q = C 4 * (X * q) by change 4 * X * _ = 4 * (X * _); ring]
    simp only [coeff_C_mul, coeff_succ_X_mul, h n (by omega)]

private theorem residual_top {d : ℕ} {p q : PowerSeries R} (hd : 1 ≤ d)
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0)
    (hp1 : coeff 1 p = 1) (hq1 : coeff 1 q = 1) (h : Agree d p q) :
    coeff d (residual p) - coeff d (residual q) = 2 * (coeff d p - coeff d q) := by
  have ht := composition_top hp hq hp1 hq1 h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hm : coeff (n+1) ((4 : PowerSeries R) * X * p) =
      coeff (n+1) ((4 : PowerSeries R) * X * q) := by
    rw [show (4 : PowerSeries R) * X * p = C 4 * (X * p) by change 4 * X * _ = 4 * (X * _); ring,
      show (4 : PowerSeries R) * X * q = C 4 * (X * q) by change 4 * X * _ = 4 * (X * _); ring]
    simp only [coeff_C_mul, coeff_succ_X_mul, h n (by omega)]
  simp only [residual, map_sub]
  linear_combination ht - hm

private theorem C_dvd_iff_coeff (a : R) (p : PowerSeries R) :
    C a ∣ p ↔ ∀ n, a ∣ coeff n p := by
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    classical
    choose q hq using h
    refine ⟨mk q, ?_⟩
    ext n
    simpa using hq n

private theorem coeff_subst_sum {p : PowerSeries R} (hp : constantCoeff p = 0)
    (f : PowerSeries R) (n : ℕ) :
    coeff n (f.subst p) = ∑ k ∈ Finset.range (n+1), coeff k f * coeff n (p ^ k) := by
  rw [coeff_subst' (.of_constantCoeff_zero hp)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra hn
  have hz := pow_low hp (by omega : n < k)
  exact hk (by simp [hz])

private theorem C_dvd_subst_sub {p q : PowerSeries R} (a : R)
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0)
    (h : C a ∣ p - q) (f : PowerSeries R) : C a ∣ f.subst p - f.subst q := by
  apply (C_dvd_iff_coeff _ _).mpr
  intro n
  rw [map_sub, coeff_subst_sum hp, coeff_subst_sum hq, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro k hk
  rw [← mul_sub]
  apply dvd_mul_of_dvd_right
  have hd := h.trans (sub_dvd_pow_sub_pow p q k)
  simpa only [map_sub] using (C_dvd_iff_coeff _ _).mp hd n

/-- Divisibility by four makes the forced half-residual an even integer. -/
private theorem residual_four {p : PowerSeries ℤ}
    (hp : constantCoeff p = 0) (h : C (2 : ℤ) ∣ p - X) :
    C (4 : ℤ) ∣ residual p := by
  obtain ⟨q, hq⟩ := h
  have hpq : p = X + C 2 * q := by linear_combination hq
  have hs := C_dvd_subst_sub 2 hp (constantCoeff_X (R := ℤ))
    (show C (2 : ℤ) ∣ p - X from ⟨q, hq⟩) q
  rw [X_subst] at hs
  obtain ⟨r, hr⟩ := hs
  refine ⟨q + r - X * p, ?_⟩
  have hcomp : p.subst p = p + C 2 * q.subst p := by
    nth_rw 2 [hpq]
    rw [subst_add (.of_constantCoeff_zero hp), subst_X (.of_constantCoeff_zero hp),
      subst_mul (.of_constantCoeff_zero hp), subst_C]
    rfl
  dsimp [residual]
  rw [hcomp]
  have htwo : C (2 : ℤ) = (2 : PowerSeries ℤ) := map_ofNat _ 2
  have hfour : C (4 : ℤ) = (4 : PowerSeries ℤ) := map_ofNat _ 4
  rw [htwo] at hq hr
  rw [hfour, htwo]
  linear_combination hq + 2 * hr

private noncomputable def correction (p : PowerSeries ℤ) (n : ℕ) : ℤ :=
  -(coeff n (residual p) / 2)

private noncomputable def extend (p : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  p + C (correction p n) * X ^ n

private theorem extend_agree (p : PowerSeries ℤ) (n : ℕ) : Agree n (extend p n) p := by
  intro k hk
  simp only [extend, map_add, coeff_C_mul, coeff_X_pow, if_neg (ne_of_lt hk),
    mul_zero, add_zero]

private theorem correction_even {p : PowerSeries ℤ}
    (hp : constantCoeff p = 0) (h : C (2 : ℤ) ∣ p - X) (n : ℕ) :
    2 ∣ correction p n ∧ 2 * correction p n = -coeff n (residual p) := by
  obtain ⟨q, hq⟩ := (C_dvd_iff_coeff _ _).mp (residual_four hp h) n
  dsimp [correction]
  rw [hq]
  constructor
  · refine ⟨-q, ?_⟩
    omega
  · omega

private theorem extend_zero {p : PowerSeries ℤ} (hp : constantCoeff p = 0)
    {n : ℕ} (hn : 2 ≤ n) : constantCoeff (extend p n) = 0 := by
  simpa only [coeff_zero_eq_constantCoeff, hp] using extend_agree p n 0 (by omega)

private theorem extend_one {p : PowerSeries ℤ} (hp1 : coeff 1 p = 1)
    {n : ℕ} (hn : 2 ≤ n) : coeff 1 (extend p n) = 1 :=
  (extend_agree p n 1 hn).trans hp1

private theorem extend_even {p : PowerSeries ℤ} (hp : constantCoeff p = 0)
    (h : C (2 : ℤ) ∣ p - X) (n : ℕ) : C (2 : ℤ) ∣ extend p n - X := by
  have hc := (correction_even hp h n).1
  have hd : C (2 : ℤ) ∣ C (correction p n) * X ^ n :=
    dvd_mul_of_dvd_left (map_dvd C hc) _
  convert dvd_add h hd using 1
  dsimp [extend]
  ring

private theorem extend_residual {p : PowerSeries ℤ} (hp : constantCoeff p = 0)
    (hp1 : coeff 1 p = 1) (h : C (2 : ℤ) ∣ p - X) {n : ℕ} (hn : 2 ≤ n)
    (hr : Agree n (residual p) 0) : Agree (n+1) (residual (extend p n)) 0 := by
  have he0 := extend_zero hp hn
  have he1 := extend_one hp1 hn
  intro k hk
  by_cases hkn : k < n
  · exact (residual_agree he0 hp (extend_agree p n) k hkn).trans (hr k hkn)
  · have hkn : k = n := by omega
    subst k
    have ht := residual_top (by omega : 1 ≤ n) he0 hp he1 hp1 (extend_agree p n)
    have hc := (correction_even hp h n).2
    have he : coeff n (extend p n) = coeff n p + correction p n := by
      simp only [extend, map_add, coeff_C_mul, coeff_X_pow_self, mul_one]
    simp only [map_zero]
    linear_combination ht + 2 * he + hc

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => X
  | n+1 => extend (approximation n) (n+2)

private theorem approximation_spec (n : ℕ) :
    constantCoeff (approximation n) = 0 ∧ coeff 1 (approximation n) = 1 ∧
    C (2 : ℤ) ∣ approximation n - X ∧ Agree (n+2) (residual (approximation n)) 0 := by
  induction n with
  | zero =>
    refine ⟨by simp [approximation], by simp [approximation], by simp [approximation], ?_⟩
    intro k hk
    have he : residual (X : PowerSeries ℤ) = -(4 * X ^ 2) := by
      simp [residual, subst_X (.of_constantCoeff_zero (constantCoeff_X (R := ℤ))), pow_two]
      ring
    change coeff k (residual (X : PowerSeries ℤ)) = coeff k 0
    rw [he]
    have hc : (4 : PowerSeries ℤ) = C 4 := (map_ofNat _ 4).symm
    rw [hc]
    simp only [map_neg, coeff_C_mul, coeff_X_pow, if_neg (ne_of_lt hk),
      mul_zero, neg_zero, map_zero]
  | succ n ih =>
    exact ⟨extend_zero ih.1 (by omega), extend_one ih.2.1 (by omega),
      extend_even ih.1 ih.2.2.1 _, extend_residual ih.1 ih.2.1 ih.2.2.1 (by omega) ih.2.2.2⟩

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree (n+2) (approximation m) (approximation n) := by
  induction m, h using Nat.le_induction with
  | base => intro k hk; rfl
  | succ m h ih =>
    intro k hk
    exact (extend_agree (approximation m) (m+2) k (by omega)).trans (ih k hk)

private noncomputable def integralSeries : PowerSeries ℤ :=
  mk (fun n => coeff n (approximation n))

private theorem integral_agree (n : ℕ) : Agree (n+2) integralSeries (approximation n) := by
  intro k hk
  simp only [integralSeries, coeff_mk]
  by_cases hkn : k ≤ n
  · exact (approximation_stable hkn k (by omega)).symm
  · exact approximation_stable (by omega : n ≤ k) k hk

private theorem integral_zero : constantCoeff integralSeries = 0 := by
  simpa only [coeff_zero_eq_constantCoeff] using
    (integral_agree 0 0 (by omega)).trans (by simp [approximation])

private theorem integral_one : coeff 1 integralSeries = 1 :=
  (integral_agree 0 1 (by omega)).trans (by simp [approximation])

private theorem integral_even : C (2 : ℤ) ∣ integralSeries - X := by
  apply (C_dvd_iff_coeff _ _).mpr
  intro n
  rw [map_sub, integral_agree n n (by omega)]
  simpa only [map_sub] using (C_dvd_iff_coeff _ _).mp (approximation_spec n).2.2.1 n

private theorem integral_equation : integralSeries.subst integralSeries =
    X + 4 * X * integralSeries := by
  have hr : residual integralSeries = 0 := by
    ext n
    exact (residual_agree integral_zero (approximation_spec n).1 (integral_agree n)
      n (by omega)).trans ((approximation_spec n).2.2.2 n (by omega))
  dsimp [residual] at hr
  linear_combination hr

private theorem solution_unique {p q : PowerSeries ℚ} (b : ℚ)
    (hp0 : constantCoeff p = 0) (hq0 : constantCoeff q = 0)
    (hp1 : coeff 1 p = 1) (hq1 : coeff 1 q = 1)
    (hep : p.subst p = X + C b * X * p)
    (heq : q.subst q = X + C b * X * q) : p = q := by
  have ha : ∀ d, Agree (d+2) p q := by
    intro d
    induction d with
    | zero =>
      intro n hn
      have h : n = 0 ∨ n = 1 := by omega
      rcases h with rfl | rfl
      · simp only [coeff_zero_eq_constantCoeff, hp0, hq0]
      · rw [hp1, hq1]
    | succ d ih =>
      intro n hn
      by_cases hnd : n < d+2
      · exact ih n hnd
      · have hn' : n = d+2 := by omega
        subst n
        have ht := composition_top hp0 hq0 hp1 hq1 ih
        rw [hep, heq] at ht
        have hm : coeff (d+2) (C b * X * p) = coeff (d+2) (C b * X * q) := by
          rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul,
            mul_assoc, coeff_C_mul, coeff_succ_X_mul, ih (d+1) (by omega)]
        simp only [map_add] at ht
        rw [hm] at ht
        linarith
  ext n
  exact ha n n (by omega)

private theorem rescale_as_subst (c : ℚ) (p : PowerSeries ℚ) :
    rescale c p = p.subst (C c * X) := by
  rw [rescale_eq_subst]
  congr 1
  ext n
  simp [coeff_C_mul]

private theorem rescale_inner (c : ℚ) (p q : PowerSeries ℚ)
    (hq : constantCoeff q = 0) :
    rescale c (p.subst q) = p.subst (rescale c q) := by
  rw [rescale_as_subst, rescale_as_subst,
    subst_comp_subst_apply (.of_constantCoeff_zero hq)
      (.of_constantCoeff_zero (by simp : constantCoeff (C c * X) = 0))]

private theorem rescale_outer (c : ℚ) (p q : PowerSeries ℚ)
    (hq : constantCoeff q = 0) :
    (rescale c p).subst q = p.subst (C c * q) := by
  rw [rescale_as_subst,
    subst_comp_subst_apply (.of_constantCoeff_zero (by simp : constantCoeff (C c * X) = 0))
      (.of_constantCoeff_zero hq),
    subst_mul (.of_constantCoeff_zero hq), subst_C, subst_X (.of_constantCoeff_zero hq)]
  rfl

private noncomputable def rationalIntegral : PowerSeries ℚ :=
  integralSeries.map (Int.castRingHom ℚ)

private theorem rational_zero : constantCoeff rationalIntegral = 0 := by
  rw [rationalIntegral, ← coeff_zero_eq_constantCoeff, coeff_map,
    coeff_zero_eq_constantCoeff, integral_zero, map_zero]

private theorem rational_one : coeff 1 rationalIntegral = 1 := by
  simp [rationalIntegral, coeff_map, integral_one]

private theorem rational_equation : rationalIntegral.subst rationalIntegral =
    X + 4 * X * rationalIntegral := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) integral_equation
  have hm : PowerSeries.map (Int.castRingHom ℚ) (integralSeries.subst integralSeries) =
      rationalIntegral.subst rationalIntegral :=
    map_subst (.of_constantCoeff_zero integral_zero) integralSeries
  rw [hm] at h
  have hfour : PowerSeries.map (Int.castRingHom ℚ) (4 : PowerSeries ℤ) =
      (4 : PowerSeries ℚ) := by
    change PowerSeries.map (Int.castRingHom ℚ) (C 4) = C 4
    rw [map_C]
    rfl
  simpa [rationalIntegral, hfour] using h

/-- The rational series obtained by undoing the integral scaling. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  C 4 * rescale (1/4) rationalIntegral

/-- The rational coefficient sequence whose denominators are A381670. -/
noncomputable def f (n : ℕ) : ℚ := coeff n generatingSeries

private theorem generating_zero : constantCoeff generatingSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [generatingSeries, coeff_C_mul, coeff_rescale, coeff_zero_eq_constantCoeff,
    rational_zero]

private theorem generating_one : coeff 1 generatingSeries = 1 := by
  simp [generatingSeries, coeff_C_mul, coeff_rescale, rational_one]

/-- The normalization and functional equation specified in OEIS A381670. -/
theorem functional_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    X * (generatingSeries + 1) = generatingSeries.subst generatingSeries := by
  refine ⟨generating_zero, generating_one, ?_⟩
  have ha : C (1/4 : ℚ) * generatingSeries = rescale (1/4) rationalIntegral := by
    dsimp [generatingSeries]
    rw [← mul_assoc, ← map_mul]
    norm_num
  have hcomp : generatingSeries.subst generatingSeries =
      C 4 * rescale (1/4) (rationalIntegral.subst rationalIntegral) := by
    change (C 4 * rescale (1/4) rationalIntegral).subst generatingSeries = _
    rw [subst_mul (.of_constantCoeff_zero generating_zero), subst_C,
      rescale_outer _ _ _ generating_zero, ha,
      ← rescale_inner _ _ _ rational_zero]
    rfl
  rw [hcomp, rational_equation]
  simp only [map_add, map_mul, rescale_X]
  have hc : rescale (1/4 : ℚ) (4 : PowerSeries ℚ) = C 4 := by
    exact (map_ofNat (rescale (1/4 : ℚ)) 4).trans (map_ofNat C 4).symm
  rw [hc]
  have h14 : C (1/4 : ℚ) * C 4 = (1 : PowerSeries ℚ) := by
    rw [← map_mul]; norm_num
  dsimp [generatingSeries]
  rw [show C (4 : ℚ) = (4 : PowerSeries ℚ) from map_ofNat _ 4] at *
  linear_combination -X * h14 - 4 * X * rescale (1/4) rationalIntegral * h14

/-- Uniqueness among rational series with the specified constant and linear terms. -/
theorem uniqueness (A : PowerSeries ℚ) (h0 : constantCoeff A = 0)
    (h1 : coeff 1 A = 1) (he : X * (A + 1) = A.subst A) :
    A = generatingSeries := by
  apply solution_unique 1 h0 generating_zero h1 generating_one
  · rw [← he]; simp; ring
  · rw [← functional_equation.2.2]; simp; ring

private theorem coefficient_rescale (n : ℕ) (hn : 1 ≤ n) :
    4 ^ (n-1) * f n = ((coeff n integralSeries : ℤ) : ℚ) := by
  have hpow : (4 : ℚ) ^ (n-1) * 4 = 4 ^ n := by
    rw [← pow_succ]; congr 1; omega
  dsimp [f, generatingSeries]
  rw [coeff_C_mul, coeff_rescale]
  have hcancel : (4 : ℚ) ^ (n-1) * (4 * ((1/4) ^ n)) = 1 := by
    rw [← mul_assoc, hpow, ← mul_pow]
    norm_num
  rw [← mul_assoc] at hcancel
  rw [← mul_assoc, ← mul_assoc, hcancel, one_mul]
  simp [rationalIntegral, coeff_map]

/-- Every coefficient of degree at least two of `A(4x)/4` is an even integer. -/
theorem rescaled_even (n : ℕ) (hn : 2 ≤ n) :
    ∃ z : ℤ, (4 : ℚ) ^ (n-1) * f n = ((2*z : ℤ) : ℚ) := by
  have hd := (C_dvd_iff_coeff _ _).mp integral_even n
  have hn1 : n ≠ 1 := by omega
  simp only [map_sub, coeff_X, if_neg hn1, sub_zero] at hd
  obtain ⟨z, hz⟩ := hd
  exact ⟨z, (coefficient_rescale n (by omega)).trans (congrArg (Int.cast : ℤ → ℚ) hz)⟩

/-- Every reduced denominator is a power of two, including that of a zero coefficient. -/
theorem scheuerle_conjecture (k : ℕ) : ∃ e : ℕ, (f k).den = 2 ^ e := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨0, ?_⟩
    have hf0 : f 0 = 0 := by simpa only [f, coeff_zero_eq_constantCoeff] using generating_zero
    simp [hf0]
  by_cases hk1 : k = 1
  · subst k
    refine ⟨0, ?_⟩
    have hf1 : f 1 = 1 := generating_one
    simp [hf1]
  have hk : 2 ≤ k := by omega
  obtain ⟨z, hz⟩ := rescaled_even k hk
  have hdiv : f k = Rat.divInt (2*z) ((4 : ℤ) ^ (k-1)) := by
    rw [Rat.divInt_eq_div, eq_div_iff]
    · push_cast at *
      linear_combination hz
    · positivity
  have hd : (f k).den ∣ (4 : ℕ) ^ (k-1) := by
    have hi := Rat.den_dvd (2*z) ((4 : ℤ) ^ (k-1))
    rw [← hdiv] at hi
    exact_mod_cast hi
  have hp : (4 : ℕ) ^ (k-1) = 2 ^ (2*(k-1)) := by rw [pow_mul]; rfl
  rw [hp] at hd
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨e, he⟩

#print axioms generatingSeries
#print axioms f
#print axioms functional_equation
#print axioms uniqueness
#print axioms rescaled_even
#print axioms scheuerle_conjecture

end D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
