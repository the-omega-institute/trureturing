/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceIdentities
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceIdentities
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   utility: none
   digest: Morgan–Voyce P_m: Laurent, Lucas and Fibonacci identities, P_m(-1), sine product. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairMorganVoyceShear
import D5.S1.Scale.Lucas
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Polynomial.Homogenize

/-! Laurent, Lucas, Fibonacci and alternating identities of the Morgan–Voyce polynomials. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairMorganVoyceIdentities

open Polynomial Finset D5.S1.Scale
open D5.S1.Recurrence.Invariants.AffinePolynomialPairMorganVoyceShear
noncomputable section

private theorem P_rec (m : ℕ) : P (m + 2) = (X + 2) * P (m + 1) - P m := rfl

/-- Homogeneous Laurent form: for `z * w = c` with `c * c = 1`,
`z^(2m+1) - w^(2m+1) = (z - w) c^m P_m((z - w)^2 c)`. -/
private theorem laurent_c {R : Type*} [CommRing R] (z w c : R) (hzw : z * w = c) (hc : c * c = 1)
    (m : ℕ) : z ^ (2 * m + 1) - w ^ (2 * m + 1) =
      (z - w) * c ^ m * aeval ((z - w) ^ 2 * c) (P m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [P]
    · simp [P, map_ofNat]
      linear_combination 3 * (z - w) * hzw - (z - w) ^ 3 * hc
    · have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have hP : aeval ((z - w) ^ 2 * c) (P (m + 2)) = ((z - w) ^ 2 * c + 2) *
          aeval ((z - w) ^ 2 * c) (P (m + 1)) - aeval ((z - w) ^ 2 * c) (P m) := by
        simp [P_rec, map_ofNat]
      rw [hP]
      linear_combination (z ^ 2 + w ^ 2) * h1 - (z * w) ^ 2 * h0 +
        (2 * ((z - w) * c ^ (m + 1) * aeval ((z - w) ^ 2 * c) (P (m + 1))) -
          (c + z * w) * ((z - w) * c ^ m * aeval ((z - w) ^ 2 * c) (P m))) * hzw -
        (z - w) ^ 2 * ((z - w) * c ^ (m + 1) * aeval ((z - w) ^ 2 * c) (P (m + 1))) * hc

private theorem natDegree_P (m : ℕ) : (P m).natDegree < m + 1 := by
  rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hk' : m < k := by exact_mod_cast hk
  rw [(result m k).2, Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem fib_sum (m n : ℕ) : (Nat.fib ((2 * m + 1) * n) : ℤ) = ∑ k ∈ range (m + 1),
    (P m).coeff k * (-1) ^ ((m + k) * n) * 5 ^ k * (Nat.fib n : ℤ) ^ (2 * k + 1) := by
  have h5 : (0 : ℝ) < √5 := by positivity
  have hs : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  set z : ℝ := Real.goldenRatio ^ n
  set w : ℝ := Real.goldenConj ^ n
  set c : ℝ := (-1) ^ n
  have hzw : z * w = c := by rw [← mul_pow, Real.goldenRatio_mul_goldenConj]
  have hc : c * c = 1 := by rw [← mul_pow]; norm_num
  have hL := laurent_c z w c hzw hc m
  have hF : (Nat.fib n : ℝ) * √5 = z - w := by rw [Real.coe_fib_eq]; field_simp; rfl
  have hN : (Nat.fib ((2 * m + 1) * n) : ℝ) * √5 = z ^ (2 * m + 1) - w ^ (2 * m + 1) := by
    rw [Real.coe_fib_eq]; field_simp; rw [← pow_mul, ← pow_mul, mul_comm n]
  rw [aeval_eq_sum_range' (natDegree_P m)] at hL
  have key : (Nat.fib ((2 * m + 1) * n) : ℝ) = ∑ k ∈ range (m + 1),
      ((P m).coeff k : ℝ) * (-1) ^ ((m + k) * n) * 5 ^ k * (Nat.fib n : ℝ) ^ (2 * k + 1) := by
    apply mul_right_cancel₀ h5.ne'
    rw [hN, hL, ← hF, sum_mul, mul_sum]
    apply sum_congr rfl
    intro k _
    rw [zsmul_eq_mul, show ((m + k) * n) = n * (m + k) by ring, pow_mul,
      mul_pow (Nat.fib n : ℝ) (√5) 2, hs]
    simp only [c]
    ring
  exact_mod_cast key

private theorem P_one (m : ℕ) : (P m).eval 1 = goldenLucas (2 * m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [P, golden_lucas_succ_eq_fib_add_fib]
    · rw [show 2 * (0 + 1) + 1 = 2 + 1 by rfl, golden_lucas_succ_eq_fib_add_fib]
      simp [P, Nat.fib_add_two]
    · rw [P_rec, eval_sub, eval_mul, eval_add, eval_X, ih (m + 1) (by omega), ih m (by omega)]
      rw [show 2 * (m + 2) + 1 = (2 * m + 4) + 1 by ring,
        show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring,
        golden_lucas_succ_eq_fib_add_fib, golden_lucas_succ_eq_fib_add_fib,
        golden_lucas_succ_eq_fib_add_fib]
      simp only [Nat.fib_add_two, Nat.cast_add]
      norm_num
      ring

private theorem P_neg_one_period (m : ℕ) : (P (m + 6)).eval (-1) = (P m).eval (-1) := by
  have h : ∀ k, (P (k + 2)).eval (-1) = (P (k + 1)).eval (-1) - (P k).eval (-1) := by
    intro k; rw [P_rec]; simp
  rw [h (m + 4), h (m + 3), h (m + 2), h (m + 1), h m]
  ring

private theorem P_neg_one_values : (P 0).eval (-1) = 1 ∧ (P 1).eval (-1) = 2 ∧ (P 2).eval (-1) = 1 ∧
    (P 3).eval (-1) = -1 ∧ (P 4).eval (-1) = -2 ∧ (P 5).eval (-1) = -1 := by
  simp [P]

/-- The Laurent identity with `w = z⁻¹`: `z^(2m+1) - w^(2m+1) = (z - w) P_m((z - w)^2)`. -/
private theorem laurent {R : Type*} [CommRing R] (z w : R) (hzw : z * w = 1) (m : ℕ) :
    z ^ (2 * m + 1) - w ^ (2 * m + 1) = (z - w) * aeval ((z - w) ^ 2) (P m) := by
  have h := laurent_c z w 1 hzw (mul_one 1) m
  simpa using h

/-- `-4 sin^2 θ` is a root of `P_m` whenever `sin((2m+1)θ) = 0` and `sin θ ≠ 0`. -/
private theorem root (m : ℕ) (θ : ℝ) (h1 : Real.sin ((2 * m + 1) * θ) = 0) (h2 : Real.sin θ ≠ 0) :
    aeval (-4 * Real.sin θ ^ 2) (P m) = 0 := by
  set z : ℂ := Complex.cos θ + Complex.sin θ * Complex.I
  set w : ℂ := Complex.cos (-θ) + Complex.sin (-θ) * Complex.I
  have hzw : z * w = 1 := by
    simp only [z, w, Complex.cos_neg, Complex.sin_neg]
    have := Complex.sin_sq_add_cos_sq (θ : ℂ)
    linear_combination this - Complex.sin (θ : ℂ) ^ 2 * Complex.I_sq
  have hN : z ^ (2 * m + 1) - w ^ (2 * m + 1) = 0 := by
    simp only [z, w, Complex.cos_add_sin_mul_I_pow]
    have hs : Complex.sin (((2 * m + 1 : ℕ) : ℂ) * (θ : ℂ)) = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sin]
      push_cast
      exact_mod_cast h1
    rw [mul_neg, Complex.cos_neg, Complex.sin_neg, hs]
    ring
  have hzw' : z - w = 2 * Complex.sin θ * Complex.I := by
    simp only [z, w, Complex.cos_neg, Complex.sin_neg]; ring
  have hL := laurent z w hzw m
  rw [hN] at hL
  have hne : z - w ≠ 0 := by
    rw [hzw']
    have : (Complex.sin (θ : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_sin]; exact_mod_cast h2
    simp [this, Complex.I_ne_zero]
  have h0 : aeval ((z - w) ^ 2) (P m) = 0 := by
    rcases mul_eq_zero.mp hL.symm with h | h
    · exact absurd h hne
    · exact h
  have hsq : (z - w) ^ 2 = ((-4 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
    rw [hzw']; push_cast; rw [← Complex.ofReal_sin]; push_cast
    linear_combination 4 * Complex.sin (θ : ℂ) ^ 2 * Complex.I_sq
  rw [hsq] at h0
  have htr := aeval_algHom_apply (Complex.ofRealAm.restrictScalars ℤ) (-4 * Real.sin θ ^ 2) (P m)
  simp only [AlgHom.coe_restrictScalars', Complex.ofRealAm_coe] at htr
  rw [htr] at h0
  exact_mod_cast h0


private theorem coeff_map_P (m k : ℕ) : ((P m).map (Int.castRingHom ℝ)).coeff k =
    ((Nat.choose (m + k) (2 * k) : ℝ) + 2 * (Nat.choose (m + k) (2 * k + 1) : ℝ)) := by
  rw [coeff_map, (result m k).2]; simp

private theorem natDegree_map_P (m : ℕ) : ((P m).map (Int.castRingHom ℝ)).natDegree = m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    have hk' : m < k := by exact_mod_cast hk
    rw [coeff_map_P, Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · rw [coeff_map_P, show m + m = 2 * m by ring, Nat.choose_self,
      Nat.choose_eq_zero_of_lt (by omega)]
    simp

private theorem monic_map_P (m : ℕ) : ((P m).map (Int.castRingHom ℝ)).Monic := by
  rw [Monic, leadingCoeff, natDegree_map_P, coeff_map_P, show m + m = 2 * m by ring,
    Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem product (m : ℕ) : (P m).map (Int.castRingHom ℝ) =
    ∏ j ∈ Icc 1 m, (X + C (4 * Real.sin (j * Real.pi / (2 * m + 1)) ^ 2)) := by
  set Q := (P m).map (Int.castRingHom ℝ) with hQ
  set θ : ℕ → ℝ := fun j => j * Real.pi / (2 * m + 1)
  set r : ℕ → ℝ := fun j => -4 * Real.sin (θ j) ^ 2
  have hpos : (0 : ℝ) < 2 * m + 1 := by positivity
  have hθ : ∀ j ∈ Icc 1 m, 0 < θ j ∧ θ j < Real.pi / 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := mem_Icc.mp hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast h1
    have hj2 : (j : ℝ) ≤ m := by exact_mod_cast h2
    constructor
    · exact div_pos (by nlinarith [Real.pi_pos]) hpos
    · rw [div_lt_div_iff₀ hpos (by norm_num)]; nlinarith [Real.pi_pos]
  have hroot : ∀ j ∈ Icc 1 m, Q.IsRoot (r j) := by
    intro j hj
    obtain ⟨h0, hπ⟩ := hθ j hj
    rw [IsRoot, hQ, eval_map, ← algebraMap_int_eq, ← aeval_def]
    apply root
    · rw [show (2 * (m : ℝ) + 1) * θ j = (j : ℕ) * Real.pi by
        simp only [θ]; field_simp]
      exact Real.sin_nat_mul_pi j
    · exact (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])).ne'
  have hinj : Set.InjOn r (Icc 1 m) := by
    intro a ha b hb hab
    obtain ⟨ha0, haπ⟩ := hθ a ha
    obtain ⟨hb0, hbπ⟩ := hθ b hb
    have hsa := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
    have hsb := Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith [Real.pi_pos])
    have hs : Real.sin (θ a) = Real.sin (θ b) := by
      simp only [r] at hab
      nlinarith [sq_nonneg (Real.sin (θ a) - Real.sin (θ b)),
        sq_nonneg (Real.sin (θ a) + Real.sin (θ b))]
    have hθab : θ a = θ b := Real.injOn_sin ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ hs
    simp only [θ] at hθab
    have : (a : ℝ) = b := by
      field_simp at hθab
      nlinarith [Real.pi_pos]
    exact_mod_cast this
  have hQ0 : Q ≠ 0 := (monic_map_P m).ne_zero
  set S : Finset ℝ := (Icc 1 m).image r
  have hScard : S.card = m := by rw [card_image_of_injOn hinj]; simp
  have hle : S.val ≤ Q.roots := by
    rw [Multiset.le_iff_subset S.nodup]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp (Finset.mem_val.mp hx)
    exact (mem_roots hQ0).mpr (hroot j hj)
  have heq : S.val = Q.roots := Multiset.eq_of_le_of_card_le hle (by
    have := card_roots' Q
    rw [natDegree_map_P] at this
    simpa [hScard] using this)
  have hcard : Q.roots.card = Q.natDegree := by
    rw [← heq, natDegree_map_P]; simpa using hScard
  have hprod : Q = (Q.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_map_P m) hcard).symm
  rw [hprod, ← heq, show (S.val.map fun a => X - C a).prod = ∏ a ∈ S, (X - C a) from rfl,
    prod_image hinj]
  apply prod_congr rfl
  intro j _
  simp only [r, θ]
  rw [C_mul, C_neg, C_pow]
  simp [sub_eq_add_neg, C_mul, C_pow]

private theorem homog_X2 : (X + 2 : Polynomial ℤ).homogenize 1 =
    MvPolynomial.X 0 + 2 * MvPolynomial.X 1 := by
  rw [show (X + 2 : Polynomial ℤ) = X + C 2 by simp, homogenize_add, homogenize_X one_ne_zero,
    homogenize_C]
  simp

private theorem homog_shift (p : Polynomial ℤ) (n : ℕ) (h : p.natDegree ≤ n) :
    p.homogenize (n + 2) = p.homogenize n * MvPolynomial.X 1 ^ 2 := by
  have := homogenize_mul p 1 h (n := 2) (by simp)
  rw [mul_one] at this; rw [this, homogenize_one]

/-- The homogeneous Laurent identity in every commutative ring:
`z^(2m+1) - w^(2m+1) = (z - w) ∑_k [x^k]P_m (z - w)^(2k) (z w)^(m-k)`. -/
private theorem general {R : Type u} [CommRing R] (z w : R) (m : ℕ) :
    z ^ (2 * m + 1) - w ^ (2 * m + 1) =
      (z - w) * MvPolynomial.aeval ![(z - w) ^ 2, z * w] ((P m).homogenize m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [P, homogenize_one]
    · rw [show P 1 = X + C 3 by simp [P]; ring, show 0 + 1 = 1 from rfl, homogenize_add,
        homogenize_X one_ne_zero, homogenize_C]
      simp
      ring
    · have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have hd1 : (P (m + 1)).natDegree ≤ m + 1 := Nat.lt_succ_iff.mp (natDegree_P (m + 1))
      have hd0 : (P m).natDegree ≤ m := Nat.lt_succ_iff.mp (natDegree_P m)
      have hrec : (P (m + 2)).homogenize (m + 2) =
          (MvPolynomial.X 0 + 2 * MvPolynomial.X 1) * (P (m + 1)).homogenize (m + 1) -
            (P m).homogenize m * MvPolynomial.X 1 ^ 2 := by
        rw [P_rec, homogenize_sub, ← homog_shift _ _ hd0, show m + 2 = 1 + (m + 1) by ring,
          homogenize_mul _ _ (by compute_degree!) hd1, homog_X2]
      rw [hrec]
      simp only [map_sub, map_mul, map_add, map_pow, MvPolynomial.aeval_X, map_ofNat,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (z ^ 2 + w ^ 2) * h1 - (z * w) ^ 2 * h0

/-- Corollary 3 of the Ma–Zhang note on A208509: in every commutative ring, without any
hypothesis on `z` and `w`, `z^(2m+1) - w^(2m+1) = (z - w) ∑_k [x^k]P_m (z - w)^(2k) (z w)^(m-k)`,
written with the degree-`m` homogenization of `P_m` (with `w = z⁻¹` this is the source identity
`z^(2m+1) - z^(-(2m+1)) = (z - z⁻¹) P_m((z - z⁻¹)^2)`), `P_m(1) = L_(2m+1)`,
`F_((2m+1)n) = ∑_k [x^k]P_m (-1)^((m+k)n) 5^k F_n^(2k+1)`, the values `P_m(-1)` repeat
`1, 2, 1, -1, -2, -1`, and `P_m(x) = ∏_{j=1}^m (x + 4 sin^2(jπ/(2m+1)))` over `ℝ` for every `m`
(the source states `m ≥ 1`; at `m = 0` both sides are `1`). -/
theorem result :
    (∀ (R : Type u) [CommRing R] (z w : R) (m : ℕ), z ^ (2 * m + 1) - w ^ (2 * m + 1) =
      (z - w) * MvPolynomial.aeval ![(z - w) ^ 2, z * w] ((P m).homogenize m)) ∧
    (∀ m : ℕ, (P m).eval 1 = goldenLucas (2 * m + 1)) ∧
    (∀ m n : ℕ, (Nat.fib ((2 * m + 1) * n) : ℤ) = ∑ k ∈ range (m + 1),
      (P m).coeff k * (-1) ^ ((m + k) * n) * 5 ^ k * (Nat.fib n : ℤ) ^ (2 * k + 1)) ∧
    (∀ m : ℕ, (P (m + 6)).eval (-1) = (P m).eval (-1)) ∧
    ((P 0).eval (-1) = 1 ∧ (P 1).eval (-1) = 2 ∧ (P 2).eval (-1) = 1 ∧
      (P 3).eval (-1) = -1 ∧ (P 4).eval (-1) = -2 ∧ (P 5).eval (-1) = -1) ∧
    (∀ m : ℕ, (P m).map (Int.castRingHom ℝ) =
      ∏ j ∈ Icc 1 m, (X + C (4 * Real.sin (j * Real.pi / (2 * m + 1)) ^ 2))) :=
  ⟨fun _ _ z w m => general z w m, P_one, fib_sum, P_neg_one_period,
    P_neg_one_values,
    product⟩

end
end D5.S1.Recurrence.Invariants.AffinePolynomialPairMorganVoyceIdentities
