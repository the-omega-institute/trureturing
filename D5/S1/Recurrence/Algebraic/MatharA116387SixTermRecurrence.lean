/- GID: D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: []
   utility: none
   digest: The six-term recurrence for the native Motzkin transform A116387. -/

import D5.S1.Recurrence.A308815DFiniteRecurrence
import Mathlib.RingTheory.PowerSeries.Inverse

/-! All series are ordinary formal power series over the rationals. The Motzkin
series is constructed by inserting arbitrary horizontal steps into Catalan paths.
The normalized square root and the inverse defining A116387 are units. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence

open PowerSeries

/-- The native Motzkin generating function c(X²/(1-X)²)/(1-X). -/
noncomputable def M : PowerSeries ℚ :=
  let u : PowerSeries ℚ := (1 - X)⁻¹
  u * subst (X ^ 2 * u ^ 2) (catalanSeries.map (Nat.castRingHom ℚ))

/-- The constant-one branch of the native Motzkin discriminant. -/
noncomputable def y : PowerSeries ℚ := 1 - X - 2 * X ^ 2 * M

/-- The exact ordinary generating function printed in OEIS A116387. -/
noncomputable def F : PowerSeries ℚ := (y * (2 - M))⁻¹

/-- The offset-zero coefficient sequence of the native generating function. -/
noncomputable def a (n : ℕ) : ℚ := coeff n F

/-- Existence, the Motzkin quadratic, uniqueness, and root normalization. -/
def native_spec : Prop :=
  (constantCoeff M = 1 ∧ M = 1 + X * M + X ^ 2 * M ^ 2) ∧
  (∀ m : PowerSeries ℚ, m = 1 + X * m + X ^ 2 * m ^ 2 → m = M) ∧
  (constantCoeff y = 1 ∧ y ^ 2 = 1 - 2 * X - 3 * X ^ 2) ∧
  (∀ z : PowerSeries ℚ, constantCoeff z = 1 →
    z ^ 2 = 1 - 2 * X - 3 * X ^ 2 → z = y) ∧
  y * (2 - M) * F = 1

/-- Mathar's printed six-term identity, over every well-formed offset-zero index,
together with the constructed native source and its uniqueness. -/
def claim : Prop := native_spec ∧ ∀ n : ℕ, 5 ≤ n →
  (n : ℚ) * (17 * (n : ℚ) - 142) * a n +
    (17 * (n : ℚ) ^ 2 + 95 * (n : ℚ) + 138) * a (n - 1) +
    (-391 * (n : ℚ) ^ 2 + 2488 * (n : ℚ) - 2908) * a (n - 2) +
    (-17 * (n : ℚ) ^ 2 - 603 * (n : ℚ) + 1892) * a (n - 3) +
    2 * (697 * (n : ℚ) - 2021) * ((n : ℚ) - 4) * a (n - 4) +
    60 * (17 * (n : ℚ) - 47) * ((n : ℚ) - 4) * a (n - 5) = 0

private theorem motzkin_spec :
    constantCoeff M = 1 ∧ M = 1 + X * M + X ^ 2 * M ^ 2 := by
  let u : PowerSeries ℚ := (1 - X)⁻¹
  let t : PowerSeries ℚ := X ^ 2 * u ^ 2
  let c : PowerSeries ℚ :=
    subst t (catalanSeries.map (Nat.castRingHom ℚ))
  have hu : (1 - X) * u = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have ht0 : constantCoeff t = 0 := by simp [t]
  have ht : HasSubst t := HasSubst.of_constantCoeff_zero' ht0
  have hc0 : constantCoeff c = 1 := by
    change constantCoeff (subst t (catalanSeries.map (Nat.castRingHom ℚ))) = 1
    rw [constantCoeff_subst_of_constantCoeff_zero ht0]
    simp
  have hu0 : constantCoeff u = 1 := by simp [u]
  have hcat : (catalanSeries.map (Nat.castRingHom ℚ)) ^ 2 * X + 1 =
      catalanSeries.map (Nat.castRingHom ℚ) := by
    simpa using congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      catalanSeries_sq_mul_X_add_one
  have hc := congrArg (substAlgHom (R := ℚ) ht) hcat
  simp only [map_add, map_mul, map_pow, map_one, substAlgHom_X,
    coe_substAlgHom] at hc
  change c ^ 2 * t + 1 = c at hc
  have hm : (1 - X) * M = c := by
    change (1 - X) * (u * c) = c
    rw [← mul_assoc, hu, one_mul]
  refine ⟨?_, ?_⟩
  · change constantCoeff (u * c) = 1
    rw [map_mul, hu0, hc0, mul_one]
  · change u * c = 1 + X * (u * c) + X ^ 2 * (u * c) ^ 2
    change (1 - X) * (u * c) = c at hm
    dsimp only [t] at hc
    linear_combination hm - hc

private theorem native_certificate : native_spec := by
  have hm := motzkin_spec
  have hy0 : constantCoeff y = 1 := by simp [y]
  have hy : y ^ 2 = 1 - 2 * X - 3 * X ^ 2 := by
    dsimp only [y]
    linear_combination -4 * X ^ 2 * hm.2
  refine ⟨hm, ?_, ⟨hy0, hy⟩, ?_, ?_⟩
  · intro m h
    have hn : (1 - X - X ^ 2 * (m + M) : PowerSeries ℚ) ≠ 0 := by
      intro hz
      have hc := congrArg constantCoeff hz
      norm_num at hc
    have he : (1 - X - X ^ 2 * (m + M)) * (m - M) = 0 := by
      linear_combination h - hm.2
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)
  · intro z hz0 hz
    have hn : z + y ≠ 0 := by
      intro he
      have hc := congrArg constantCoeff he
      rw [map_add, hz0, hy0, map_zero] at hc
      norm_num at hc
    have he : (z + y) * (z - y) = 0 := by linear_combination hz - hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)
  · exact PowerSeries.mul_inv_cancel _ (by simp [y, hm.1])

private noncomputable def p : PowerSeries ℚ := 1 - X - 4 * X ^ 2
private noncomputable def q : PowerSeries ℚ := 1 - 2 * X - 4 * X ^ 2
private noncomputable def d : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2
private noncomputable def D : PowerSeries ℚ := p * q * d
private noncomputable def e : PowerSeries ℚ :=
  2 - 2 * X - 14 * X ^ 2 - 14 * X ^ 3 + 40 * X ^ 4 + 48 * X ^ 5
private noncomputable def f : PowerSeries ℚ := 2 * X - 6 * X ^ 2 - 6 * X ^ 3

private theorem source_bridge : 2 * q * y * F = y + p := by
  have hm := motzkin_spec.2
  have hf := native_certificate.2.2.2.2
  have hn : y * (2 - M) ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    norm_num [y, motzkin_spec.1] at hc
  apply (mul_left_inj' hn).mp
  calc
    y * (2 - M) * (2 * q * y * F) = 2 * q * y * (y * (2 - M) * F) := by ring
    _ = 2 * q * y := by rw [hf, mul_one]
    _ = y * (2 - M) * (y + p) := by
      dsimp only [y, p, q]
      linear_combination -2 * (2 * M * X ^ 2 + X - 1) * hm

private theorem differential_equation : D * derivative F - e * F = f := by
  have hr : y ^ 2 = d := native_certificate.2.2.1.2
  have hd := congrArg (derivative (R := ℚ)) hr
  simp only [d, map_sub, derivative_pow, Derivation.leibniz, derivative_one,
    derivative_X, Derivation.map_natCast, smul_eq_mul] at hd
  have hyr : y * derivative y = -1 - 3 * X := by
    apply (mul_left_inj' (show (2 : PowerSeries ℚ) ≠ 0 by
      intro hz; have hc := congrArg constantCoeff hz; norm_num at hc)).mp
    linear_combination hd
  have hb := source_bridge
  have h1 := congrArg (derivative (R := ℚ)) hb
  simp only [map_add, Derivation.leibniz, Derivation.map_natCast, derivative_one,
    zero_mul, zero_add, smul_eq_mul] at h1
  apply (mul_left_inj' (show (2 : PowerSeries ℚ) ≠ 0 by
    intro hz; have hc := congrArg constantCoeff hz; norm_num at hc)).mp
  have hc :
      2 * (D * derivative F - e * F - f) = 0 := by
    dsimp only [D, e, f, p, q, d] at hr hb h1 ⊢
    simp only [map_sub, map_add, Derivation.leibniz, derivative_pow,
      derivative_one, derivative_X, Derivation.map_natCast,
      smul_eq_mul, zero_mul, mul_zero, zero_add, add_zero] at h1
    linear_combination
      (1 - X - 4 * X ^ 2) * y * h1 -
      (-1 - 8 * X) * y * hb -
      (2 * (1 - X - 4 * X ^ 2) * (1 - 2 * X - 4 * X ^ 2) * derivative F +
        2 * (1 - X - 4 * X ^ 2) * (-2 - 8 * X) * F -
        2 * (-1 - 8 * X) * (1 - 2 * X - 4 * X ^ 2) * F + (-1 - 8 * X)) * hr -
      (2 * (1 - X - 4 * X ^ 2) * (1 - 2 * X - 4 * X ^ 2) * F -
        (1 - X - 4 * X ^ 2)) * hyr
  linear_combination hc

private noncomputable def U : PowerSeries ℚ :=
  17 + 17 * X - 391 * X ^ 2 - 17 * X ^ 3 + 1394 * X ^ 4 + 1020 * X ^ 5
private noncomputable def V : PowerSeries ℚ :=
  -142 + 129 * X + 924 * X ^ 2 - 705 * X ^ 3 + 1534 * X ^ 4 + 3300 * X ^ 5
private noncomputable def W : PowerSeries ℚ :=
  250 * X + 504 * X ^ 2 - 70 * X ^ 3 + 2280 * X ^ 5
private noncomputable def H : PowerSeries ℚ := 6 * X ^ 2 * (5 * X - 36)

private theorem operator_equation :
    U * (X * derivative (X * derivative F)) + V * (X * derivative F) + W * F = H := by
  have h0 := differential_equation
  have h1 := congrArg (derivative (R := ℚ)) h0
  simp only [map_sub, Derivation.leibniz, smul_eq_mul] at h1
  have hn : p ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    norm_num [p] at hc
  have hc : p *
      (U * (X * derivative (X * derivative F)) + V * (X * derivative F) + W * F - H) = 0 := by
    dsimp only [D, e, f, p, q, d, U, V, W, H] at h0 h1 ⊢
    simp only [map_sub, map_add, Derivation.leibniz, derivative_pow,
      derivative_one, derivative_X, Derivation.map_natCast,
      smul_eq_mul, zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul] at h1 ⊢
    linear_combination 17 * X ^ 2 * (5 * X + 1) * h1 - 5 * X * (47 * X + 25) * h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hn)

/-- The complete six-term assertion and the native source specification. -/
theorem result : claim := by
  refine ⟨native_certificate, ?_⟩
  intro n hn
  have hop := operator_equation
  have hexp : U * (X * derivative (X * derivative F)) + V * (X * derivative F) + W * F =
      (17 * (X * derivative (X * derivative F)) - 142 * (X * derivative F)) +
      X ^ 1 * (17 * (X * derivative (X * derivative F)) + 129 * (X * derivative F) + 250 * F) +
      X ^ 2 * (-391 * (X * derivative (X * derivative F)) + 924 * (X * derivative F) + 504 * F) +
      X ^ 3 * (-17 * (X * derivative (X * derivative F)) - 705 * (X * derivative F) - 70 * F) +
      X ^ 4 * (1394 * (X * derivative (X * derivative F)) + 1534 * (X * derivative F)) +
      X ^ 5 * (1020 * (X * derivative (X * derivative F)) + 3300 * (X * derivative F) + 2280 * F) := by
    dsimp only [U, V, W]
    ring
  have hh : coeff n H = 0 := by
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have he : H = 30 * X ^ 3 - 216 * X ^ 2 := by dsimp [H]; ring
    rw [he]
    simp [coeff_ofNat_mul, coeff_X_pow, hn2, hn3]
  rw [hexp] at hop
  have hc := congrArg (coeff n) hop
  rw [hh] at hc
  simp (disch := omega) only [map_add, map_sub, map_neg, neg_mul, coeff_ofNat_mul,
    coeff_X_pow_mul', ite_eq_left,
    D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff] at hc
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub hn] at hc
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at hc
  dsimp only [a]
  linear_combination hc

end D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence
