/- GID: D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaSigmaProductExpModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sigma-product exponential satisfies Hanna's congruence modulo three. -/

/-
proof_shape: content (AIntegral, integerSeries_map, integerCube_map, result); bind-only
(cube_residues; consumers: result, HannaSigmaProductExpModThreeCube.result),
by inlining the arithmetic helpers; no escape witness is claimed here.
escape_witness: none.
admission_basis: open-problem-resolution (#18863; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19891
Direct frozen dependencies after inlining same-delivery helpers:
HannaLogarithmicPowerClosure.IntegralSeries;
CubicFifteenSubstitutionParity.prime_power_subst;
LinearExponentDyadicSupport.pow_change;
ParametricExponentialSquareCongruence.linear_ode_unique.
The formulas for A, B and claim are those of issue #18863, with the namespace
following this module. Rational formal substitution fixes the zero coefficient.
AIntegral supplies integerSeries; integerCube_map and cube_residues are used
also by HannaSigmaProductExpModThreeCube.result.
utility: none; no declaration refutes a claim or uses a finite certificate.
-/

import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree

open PowerSeries ArithmeticFunction

/-- OEIS A382124: "G.f. A(x) = exp( Sum_{n>=1} sigma(n)*sigma(2*n)/3 * x^n/n )". -/
noncomputable def A : PowerSeries ℚ :=
  (exp ℚ).subst (mk fun n => ((sigma 1 n : ℚ) * (sigma 1 (2 * n) : ℚ) / 3) / (n : ℚ))

/-- OEIS A382125: "G.f. A(x) = exp( Sum_{n>=1} sigma(n)*sigma(2*n) * x^n/n )". -/
noncomputable def B : PowerSeries ℚ :=
  (exp ℚ).subst (mk fun n => ((sigma 1 n : ℚ) * (sigma 1 (2 * n) : ℚ)) / (n : ℚ))

/-- OEIS A382124 (P. D. Hanna), conjecture: "a(n) == A382125(3*n) (mod 3) for n >= 0". The terms are
integers. -/
def claim : Prop :=
  ∀ n : ℕ, ∃ u v : ℤ, coeff n A = u ∧ coeff (3 * n) B = v ∧ u ≡ v [ZMOD 3]

end D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree

namespace D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree.Arithmetic
open ArithmeticFunction PowerSeries Finset
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

private theorem sigma_prime_step (p a k : ℕ) (hp : p.Prime) (hk : ¬ p ∣ k) :
    (sigma 1 (p ^ (a+1) * k) : ℤ) - sigma 1 (p ^ a * k) =
      (p : ℤ) ^ (a+1) * sigma 1 k := by
  have hc := hp.coprime_iff_not_dvd.mpr hk
  rw [isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left (a+1)),
    isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left a),
    sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, sum_range_succ]
  push_cast
  ring

private theorem sigma_two_succ (a : ℕ) :
    sigma 1 (2 ^ (a+1)) = 2 * sigma 1 (2 ^ a) + 1 := by
  have h a : sigma 1 (2 ^ a) + 1 = 2 ^ (a+1) := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    simpa using (geom_sum_mul_add (1 : ℕ) (a+1))
  have h1 := h a
  have h2 := h (a+1)
  rw [pow_succ 2 (a+1)] at h2
  omega

private theorem sigma_two_pair (a : ℕ) :
    3 ∣ sigma 1 (2 ^ a) * sigma 1 (2 ^ (a+1)) := by
  induction a with
  | zero =>
    simp only [sigma_one_apply_prime_pow Nat.prime_two]
    norm_num
  | succ a ih =>
    have h1 := sigma_two_succ a
    have h2 := sigma_two_succ (a+1)
    have he : sigma 1 (2 ^ (a+1)) * sigma 1 (2 ^ (a+1+1)) =
        4 * (sigma 1 (2 ^ a) * sigma 1 (2 ^ (a+1))) +
          3 * sigma 1 (2 ^ (a+1)) := by nlinarith
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right ih 4) (dvd_mul_right _ _)

private theorem sigma_product_three_dvd (n : ℕ) : 3 ∣ sigma 1 n * sigma 1 (2*n) := by
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨a,k,hk,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by decide)
  have hc := Nat.prime_two.coprime_iff_not_dvd.mpr hk
  rw [show 2 * (2 ^ a * k) = 2 ^ (a+1) * k by ring,
    isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left a),
    isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left (a+1))]
  convert dvd_mul_of_dvd_left (sigma_two_pair a) (sigma 1 k ^ 2) using 1 <;> ring

private noncomputable def c (n : ℕ) : ℤ := (sigma 1 n * sigma 1 (2*n) / 3 : ℕ)

private theorem three_c (n : ℕ) : 3 * c n = (sigma 1 n : ℤ) * sigma 1 (2*n) := by
  dsimp [c]
  norm_cast
  exact Nat.mul_div_cancel' (sigma_product_three_dvd n)

private theorem c_cast (n : ℕ) : (c n : ℚ) = (sigma 1 n : ℚ) * sigma 1 (2*n) / 3 := by
  have h : (3 : ℚ) * (c n : ℚ) = (sigma 1 n : ℚ) * sigma 1 (2*n) := by
    exact_mod_cast three_c n
  linarith

private theorem c_odd_prime_factor (p a k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : ¬ p ∣ k) :
    c (p ^ a * k) = (sigma 1 (p ^ a) : ℤ) ^ 2 * c k := by
  have hc := hp.coprime_iff_not_dvd.mpr hk
  have h2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
  have hc2 : (p ^ a).Coprime (2*k) := (h2.mul_right hc).pow_left a
  have h := three_c (p ^ a * k)
  rw [show 2 * (p ^ a * k) = p ^ a * (2*k) by ring,
    isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left a),
    isMultiplicative_sigma.map_mul_of_coprime hc2] at h
  have h' := three_c k
  push_cast at h
  have hmul := congrArg (fun t : ℤ => (sigma 1 (p ^ a) : ℤ) ^ 2 * t) h'
  nlinarith [hmul]

private theorem c_three_prime_step (a k : ℕ) (hk : ¬ 3 ∣ k) :
    (3 : ℤ) ^ (a+1) ∣ c (3 ^ (a+1) * k) - c (3 ^ a * k) := by
  rw [c_odd_prime_factor 3 (a+1) k (by decide) (by decide) hk,
    c_odd_prime_factor 3 a k (by decide) (by decide) hk]
  have h : (sigma 1 (3 ^ (a+1)) : ℤ) - sigma 1 (3 ^ a) = (3 : ℤ) ^ (a+1) := by
    simpa using sigma_prime_step 3 a 1 Nat.prime_three (by norm_num)
  refine ⟨((sigma 1 (3 ^ (a+1)) : ℤ) + sigma 1 (3 ^ a)) * c k, ?_⟩
  rw [← h]
  ring

private theorem padic_eq_of_split (p a k : ℕ) (hp : p.Prime) (hk : ¬ p ∣ k) :
    padicValNat p (p ^ a * k) = a := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hk0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hk, add_zero]

private theorem sigma_dold : Dold (fun n => (sigma 1 n : ℤ)) := by
  intro p hp m hm
  obtain ⟨a,k,hk,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  rw [padic_eq_of_split p a k hp hk,
    show p * (p ^ a * k) = p ^ (a+1) * k by ring,
    sigma_prime_step p a k hp hk]
  exact dvd_mul_right _ _

private theorem dold_mul (u v : ℕ → ℤ) (hu : Dold u) (hv : Dold v) :
    Dold (fun n => u n * v n) := by
  intro p hp m hm
  have he : u (p*m) * v (p*m) - u m * v m =
      u (p*m) * (v (p*m) - v m) + v m * (u (p*m) - u m) := by ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right (hv p hp m hm) _) (dvd_mul_of_dvd_right (hu p hp m hm) _)

private theorem dold_scale (u : ℕ → ℤ) (hu : Dold u) (k : ℕ) (hk : k ≠ 0) :
    Dold (fun n => u (k*n)) := by
  intro p hp m hm
  letI : Fact p.Prime := ⟨hp⟩
  have h := hu p hp (k*m) (mul_ne_zero hk hm)
  have hv : padicValNat p m ≤ padicValNat p (k*m) := by
    rw [padicValNat.mul hk hm]
    omega
  have hd : (p : ℤ) ^ (padicValNat p m + 1) ∣ (p : ℤ) ^ (padicValNat p (k*m) + 1) :=
    pow_dvd_pow _ (by omega)
  convert hd.trans h using 1 <;> congr 1 <;> ring

private theorem c_dold_away_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (m : ℕ) (hm : m ≠ 0) :
    (p : ℤ) ^ (padicValNat p m + 1) ∣ c (p*m) - c m := by
  have h := dold_mul _ _ sigma_dold (dold_scale _ sigma_dold 2 (by decide)) p hp m hm
  have hcop : p.Coprime 3 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hp3 (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left hp.ne_one))
  have hcop' : IsCoprime ((p : ℤ) ^ (padicValNat p m + 1)) 3 := by
    exact_mod_cast (hcop.pow_left (padicValNat p m + 1)).isCoprime
  apply hcop'.dvd_of_dvd_mul_left
  convert h using 1
  rw [mul_sub, three_c, three_c]

private theorem c_dold_three (m : ℕ) (hm : m ≠ 0) :
    (3 : ℤ) ^ (padicValNat 3 m + 1) ∣ c (3*m) - c m := by
  obtain ⟨a,k,hk,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm 3 (by decide)
  rw [padic_eq_of_split 3 a k (by decide) hk,
    show 3 * (3 ^ a * k) = 3 ^ (a+1) * k by ring]
  exact c_three_prime_step a k hk

private theorem c_dold : Dold c := by
  intro p hp m hm
  by_cases hp3 : p = 3
  · subst p
    exact c_dold_three m hm
  · exact c_dold_away_three p hp hp3 m hm

end D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree.Arithmetic

namespace D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree
open PowerSeries D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality ArithmeticFunction
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)

theorem AIntegral : IntegralSeries A := by
  have he : A = (PowerSeries.subst (logInput D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree.Arithmetic.c) (exp ℚ)) := by
    unfold A logInput
    congr 1
    ext n
    simp only [coeff_mk]
    rw [D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree.Arithmetic.c_cast]
  rw [he]
  exact integral_exp_of_dold _ D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree.Arithmetic.c_dold

private theorem B_eq_cube : B = A ^ 3 := by
  let h : PowerSeries ℚ := mk fun n => ((sigma 1 n : ℚ) * (sigma 1 (2*n) : ℚ) / 3) / n
  have h0 : constantCoeff h = 0 := by simp [h]
  have he : (mk fun n => ((sigma 1 n : ℚ) * (sigma 1 (2*n) : ℚ)) / n) = (3 : ℕ) • h := by
    ext n
    simp only [nsmul_eq_mul, coeff_natCast_mul, coeff_mul_natCast, h, coeff_mk]
    norm_num
    <;> ring
  change (PowerSeries.subst _ (exp ℚ)) = (PowerSeries.subst h (exp ℚ)) ^ 3
  rw [he, expSeries_nsmul h0]

noncomputable def integerSeries : PowerSeries ℤ :=
  mk fun n => Classical.choose (AIntegral n)

private theorem integerSeries_map : integerSeries.map (Int.castRingHom ℚ) = A := by
  ext n
  simp only [coeff_map, integerSeries, coeff_mk, Int.coe_castRingHom]
  exact (Classical.choose_spec (AIntegral n)).symm

theorem integerCube_map : (integerSeries ^ 3).map (Int.castRingHom ℚ) = B := by
  rw [map_pow, integerSeries_map, B_eq_cube]

theorem cube_residues (n : ℕ) :
    coeff (3*n) (integerSeries ^ 3) ≡ coeff n integerSeries [ZMOD 3] ∧
    coeff (3*n+1) (integerSeries ^ 3) ≡ 0 [ZMOD 3] ∧
    coeff (3*n+2) (integerSeries ^ 3) ≡ 0 [ZMOD 3] := by
  let f := integerSeries.map (Int.castRingHom (ZMod 3))
  have he : (integerSeries ^ 3).map (Int.castRingHom (ZMod 3)) = f.subst (X ^ 3) := by
    rw [map_pow]
    exact D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst 3 f
  have hc (j : ℕ) := congrArg (coeff j) he
  have h0 := hc (3*n)
  have h1 := hc (3*n+1)
  have h2 := hc (3*n+2)
  simp only [coeff_map, Int.coe_castRingHom,
    coeff_subst_X_pow (by decide : 3 ≠ 0), f] at h0 h1 h2
  simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ (by decide : 0 < 3),
    coeff_map, Int.coe_castRingHom] at h0
  have hnd1 : ¬ 3 ∣ 3*n+1 := by omega
  have hnd2 : ¬ 3 ∣ 3*n+2 := by omega
  simp only [if_neg hnd1] at h1
  simp only [if_neg hnd2] at h2
  exact ⟨(ZMod.intCast_eq_intCast_iff _ _ 3).mp h0,
    (ZMod.intCast_eq_intCast_iff _ 0 3).mp (by simpa using h1),
    (ZMod.intCast_eq_intCast_iff _ 0 3).mp (by simpa using h2)⟩

theorem result : claim := by
  intro n
  refine ⟨coeff n integerSeries, coeff (3*n) (integerSeries ^ 3), ?_, ?_,
    (cube_residues n).1.symm⟩
  · rw [← integerSeries_map, coeff_map]
    rfl
  · rw [← integerCube_map, coeff_map]
    rfl

end D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree
