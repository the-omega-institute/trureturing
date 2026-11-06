/- GID: D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/BalaA337389Diagonal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Normalized reversion proves Bala's all-column diagonal formula for A337389. -/

/-
admission_basis: open-problem-resolution (#21933; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26904
Every theorem has proof_shape: bind-only.
Core.reciprocal_quadratic: proof_shape: bind-only; consumer: canonical_column.
Core.discriminant: proof_shape: bind-only; consumers: Core.outer_identity, canonical_column.
Core.outer_identity: proof_shape: bind-only; consumer: canonical_column.
diagonal_coefficient: proof_shape: bind-only; consumer: canonical_column.
canonical_column: proof_shape: bind-only; consumer: result.
normalized_square_unique: proof_shape: bind-only; consumer: result.
result: proof_shape: bind-only; escape_witness: none.
Direct frozen dependencies (merged dev declaration identity before publication):
D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.lagrange_subst
  private-owner declaration statement_id:
  sha256:82155501b04fee91ff46f3a0762e99d2c8f9dfb3954cf56c15fc92b45bf24d94
This dependency belongs to diagonal_coefficient, canonical_column and result;
the other four theorems have no direct frozen dependencies.
The public identity after publication is read by the canonical freeze writer.
The source expressions for delta, IsColumn and phi are retained in full.
The natural parameter includes zero and four without division by the parameter.
Utility none: the coefficient identity ranges over all natural columns and degrees.
-/

import D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix

/-! Definitions for the final FORMULA conjecture in OEIS A337389.
The two square roots are encoded by their equations and constant coefficient 1.
The existence clause prevents a vacuous assertion about missing source series.
-/

namespace D5.S3.Combinatorics.PowerSeries.BalaA337389Diagonal

open _root_.PowerSeries

/-- The source discriminant 1 - 2(k+4)t + ((k-4)t)^2. -/
noncomputable def delta (k : ℕ) : PowerSeries ℚ :=
  1 - C (2 * ((k : ℚ) + 4)) * X + (C ((k : ℚ) - 4) * X) ^ 2

/-- The literal two constant-1 square roots defining column k of the source array. -/
def IsColumn (k : ℕ) (d A : PowerSeries ℚ) : Prop :=
  constantCoeff d = 1 ∧ d ^ 2 = delta k ∧
    constantCoeff A = 1 ∧
      A ^ 2 = (1 + C ((k : ℚ) - 4) * X + d) * (2 * delta k)⁻¹

/-- The source's rational expression, expanded at u=0 where (1-u)^2 is a unit. -/
noncomputable def phi (k : ℕ) : PowerSeries ℚ :=
  (1 + C ((k : ℚ) - 2) * X + X ^ 2) * (1 + X) ^ 2 * ((1 - X) ^ 2)⁻¹

/-- Bala's entire conjecture: for every nonnegative integer column and degree. -/
def claim : Prop :=
  ∀ (k : ℕ),
    (∃ (d : PowerSeries ℚ) (A : PowerSeries ℚ), IsColumn k d A) ∧
      ∀ (d : PowerSeries ℚ) (A : PowerSeries ℚ), IsColumn k d A →
        ∀ (n : ℕ), coeff n A = coeff n (phi k ^ n)

end D5.S3.Combinatorics.PowerSeries.BalaA337389Diagonal

namespace D5.S3.Combinatorics.PowerSeries.BalaA337389Diagonal.Core
open _root_.PowerSeries

set_option maxHeartbeats 800000 in
private theorem reciprocal_quadratic (K t w v Y : PowerSeries ℚ)
    (ht : t = w * v) (hY : Y = t * w + v)
    (he : v * (1 + (K - 2) * w + w ^ 2) * (1 + w) ^ 2 = (1 - w) ^ 2) :
    Y ^ 2 + (K * t - 1) * Y + 2 * (K - 2) * t ^ 2 + 2 * t = 0 := by
  rw [hY, ht]
  linear_combination v * he

set_option maxHeartbeats 800000 in
private theorem discriminant (K t Y : PowerSeries ℚ)
    (hq : Y ^ 2 + (K * t - 1) * Y + 2 * (K - 2) * t ^ 2 + 2 * t = 0) :
    (2 * Y + K * t - 1) ^ 2 = 1 - 2 * (K + 4) * t + ((K - 4) * t) ^ 2 := by
  have hq' : (1 : PowerSeries ℚ) * (Y * Y) + (K * t - 1) * Y +
      (2 * (K - 2) * t ^ 2 + 2 * t) = 0 := by
    linear_combination hq
  have h := discrim_eq_sq_of_quadratic_eq_zero hq'
  dsimp only [discrim] at h
  linear_combination -h

set_option maxHeartbeats 800000 in
private theorem outer_identity (K w v Y D : PowerSeries ℚ)
    (hK : derivative (R := ℚ) K = 0)
    (ht : (X : PowerSeries ℚ) = w * v)
    (hY : Y = X * w + v)
    (hD : D = derivative (R := ℚ) w * v)
    (hq : Y ^ 2 + (K * X - 1) * Y + 2 * (K - 2) * X ^ 2 + 2 * X = 0)
    (hY0 : constantCoeff Y = 1) :
    (1 - 2 * (K + 4) * X + ((K - 4) * X) ^ 2) * D ^ 2 = Y + (K - 2) * X := by
  let d := 2 * Y + K * X - 1
  let J := X * derivative (R := ℚ) Y - Y
  have hd : d ^ 2 = 1 - 2 * (K + 4) * X + ((K - 4) * X) ^ 2 :=
    discriminant K X Y hq
  have htwo : derivative (R := ℚ) (2 : PowerSeries ℚ) = 0 :=
    Derivation.map_natCast (derivative (R := ℚ)) 2
  have hq' := congrArg (derivative (R := ℚ)) hq
  simp only [map_add, map_sub, map_zero, derivative_pow, derivative_X,
    derivative_one, Derivation.leibniz, hK, add_zero,
    mul_zero, sub_zero, htwo, smul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at hq'
  have hJ : d * J = -(Y - 2 * X) := by
    dsimp only [d, J]
    linear_combination X * hq' - 2 * hq
  have ht' := congrArg (derivative (R := ℚ)) ht
  simp only [derivative_X, Derivation.leibniz, smul_eq_mul] at ht'
  have hY' := congrArg (derivative (R := ℚ)) hY
  simp only [map_add, Derivation.leibniz, smul_eq_mul, derivative_X] at hY'
  have hJD : J = D * (X * w - v) := by
    dsimp only [J]
    rw [hD]
    linear_combination X * hY' - hY - v * ht' +
      (X * derivative (R := ℚ) w + derivative (R := ℚ) v) * ht
  have hnorm : (X * w - v) ^ 2 = Y ^ 2 - 4 * X ^ 2 := by
    rw [hY, ht]
    ring
  have hsquare : d ^ 2 * D ^ 2 * (Y ^ 2 - 4 * X ^ 2) = (Y - 2 * X) ^ 2 := by
    calc
      _ = (d * (D * (X * w - v))) ^ 2 := by rw [← hnorm]; ring
      _ = (Y - 2 * X) ^ 2 := by rw [← hJD, hJ]; ring
  have hu : IsUnit (Y - 2 * X) := by
    rw [isUnit_iff_constantCoeff]
    simp [hY0]
  have hc : d ^ 2 * D ^ 2 * (Y + 2 * X) = Y - 2 * X := by
    apply hu.mul_left_cancel
    linear_combination hsquare
  have hvu : IsUnit (Y + 2 * X) := by
    rw [isUnit_iff_constantCoeff]
    simp [hY0]
  apply hvu.mul_right_cancel
  rw [← hd]
  linear_combination hc - hq

end D5.S3.Combinatorics.PowerSeries.BalaA337389Diagonal.Core

namespace D5.S3.Combinatorics.PowerSeries.BalaA337389Diagonal
open _root_.PowerSeries

set_option maxHeartbeats 800000 in
private theorem diagonal_coefficient (f w : PowerSeries ℚ)
    (hf : constantCoeff f = 1) (hw0 : constantCoeff w = 0)
    (hw : w = X * f.subst w) (n : ℕ) :
    coeff n (derivative (R := ℚ) w * f⁻¹.subst w) = coeff n (f ^ n) := by
  let H : PowerSeries ℚ := mk fun n => if n = 0 then 0 else coeff (n - 1) f⁻¹ / (n : ℚ)
  have hH : derivative (R := ℚ) H = f⁻¹ := by
    ext j
    simp only [coeff_derivative, H, coeff_mk, Nat.add_sub_cancel,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    exact div_mul_cancel₀ _ (by positivity)
  have hi : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f (by rw [hf]; norm_num)
  have hp : f⁻¹ * f ^ (n + 1) = f ^ n := by
    calc
      _ = (f * f⁻¹) * f ^ n := by ring
      _ = f ^ n := by rw [hi, one_mul]
  have h := D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.lagrange_subst w f H hw0 hw n
  rw [hH, hp] at h
  have hc := coeff_derivative (H.subst w) n
  rw [derivative_subst (.of_constantCoeff_zero hw0), hH,
    mul_comm (f⁻¹.subst w) (derivative (R := ℚ) w)] at hc
  simp only [Nat.cast_add, Nat.cast_one] at h
  linear_combination hc + h

set_option maxHeartbeats 800000 in
private theorem canonical_column (k : ℕ) :
    ∃ (d A : PowerSeries ℚ), IsColumn k d A ∧
      ∀ n, coeff n A = coeff n (phi k ^ n) := by
  let f := phi k
  have hf : constantCoeff f = 1 := by simp [f, phi, constantCoeff_inv]
  let P : PowerSeries ℚ := X * f⁻¹
  have hP0 : constantCoeff P = 0 := by simp [P]
  have hP1 : coeff 1 P = 1 := by
    change coeff (0 + 1) (X * f⁻¹) = 1
    simp [coeff_succ_X_mul, coeff_zero_eq_constantCoeff, constantCoeff_inv, hf]
  let w : PowerSeries ℚ := P.substInvOfIsUnit (hP1 ▸ isUnit_one)
  have hw0 : constantCoeff w = 0 := constantCoeff_substInvOfIsUnit _ _
  have hws : HasSubst w := .of_constantCoeff_zero hw0
  have hwP : P.subst w = X := subst_substInvOfIsUnit_right _ hP0 _
  let v : PowerSeries ℚ := f⁻¹.subst w
  have htv : (X : PowerSeries ℚ) = w * v := by
    simpa only [P, subst_mul hws, subst_X hws] using hwP.symm
  have hv0 : constantCoeff v = 1 := by
    change MvPowerSeries.constantCoeff (f⁻¹.subst w) = 1
    rw [constantCoeff_subst_of_constantCoeff_zero hw0]
    change constantCoeff f⁻¹ = 1
    rw [constantCoeff_inv, hf]
    norm_num
  have hfc : constantCoeff (f.subst w) = 1 := by
    change MvPowerSeries.constantCoeff (f.subst w) = 1
    rw [constantCoeff_subst_of_constantCoeff_zero hw0]
    change constantCoeff f = 1
    exact hf
  have hzv : f.subst w * v = 1 := by
    have hi := congrArg (substAlgHom hws)
      (PowerSeries.mul_inv_cancel f (by rw [hf]; norm_num))
    simpa only [map_mul, map_one, coe_substAlgHom] using hi
  have hw : w = X * f.subst w := by
    linear_combination -w * hzv - f.subst w * htv
  have hw1 : coeff 1 w = 1 := by
    rw [hw, coeff_succ_X_mul, coeff_zero_eq_constantCoeff, hfc]
  let K : PowerSeries ℚ := C (k : ℚ)
  let Y : PowerSeries ℚ := X * w + v
  let d : PowerSeries ℚ := 2 * Y + K * X - 1
  let A : PowerSeries ℚ := derivative (R := ℚ) w * v
  have hY0 : constantCoeff Y = 1 := by simp [Y, hv0]
  have hd0 : constantCoeff d = 1 := by norm_num [d, hY0, map_ofNat]
  have hA0 : constantCoeff A = 1 := by
    simp only [A, map_mul, hv0, mul_one, ← coeff_zero_eq_constantCoeff,
      coeff_derivative, zero_add, Nat.cast_zero, zero_add, mul_one, hw1]
  have hden : f * (1 - X) ^ 2 =
      (1 + (K - 2) * X + X ^ 2) * (1 + X) ^ 2 := by
    have hi := PowerSeries.inv_mul_cancel ((1 - X : PowerSeries ℚ) ^ 2) (by simp)
    dsimp only [f, phi, K]
    rw [map_sub, map_ofNat, mul_assoc, hi, mul_one]
  have hdenw : f.subst w * (1 - w) ^ 2 =
      (1 + (K - 2) * w + w ^ 2) * (1 + w) ^ 2 := by
    have hC : K.subst w = K := by
      dsimp only [K]
      exact subst_C (k : ℚ)
    have h := congrArg (substAlgHom hws) hden
    simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat,
      coe_substAlgHom, subst_X hws, hC] using h
  have he : v * (1 + (K - 2) * w + w ^ 2) * (1 + w) ^ 2 = (1 - w) ^ 2 := by
    linear_combination -v * hdenw + (1 - w) ^ 2 * hzv
  have hq : Y ^ 2 + (K * X - 1) * Y + 2 * (K - 2) * X ^ 2 + 2 * X = 0 :=
    Core.reciprocal_quadratic K X w v Y htv rfl he
  have hd : d ^ 2 = delta k := by
    simpa only [d, K, delta, map_sub, map_add, map_mul, map_ofNat] using
      Core.discriminant K X Y hq
  have houter : delta k * A ^ 2 = Y + (K - 2) * X := by
    simpa only [K, delta, map_sub, map_add, map_mul, map_ofNat] using
      Core.outer_identity K w v Y A (by simp [K]) htv rfl rfl hq hY0
  have hmul : (2 * delta k) * A ^ 2 = 1 + C ((k : ℚ) - 4) * X + d := by
    dsimp only [d, K] at houter ⊢
    simp only [map_sub, map_ofNat] at houter ⊢
    linear_combination 2 * houter
  have hcc : constantCoeff (2 * delta k) ≠ 0 := by norm_num [delta, map_ofNat]
  have hAi : A ^ 2 = (1 + C ((k : ℚ) - 4) * X + d) * (2 * delta k)⁻¹ := by
    have hi := PowerSeries.mul_inv_cancel (2 * delta k) hcc
    linear_combination -A ^ 2 * hi + (2 * delta k)⁻¹ * hmul
  refine ⟨d, A, ⟨hd0, hd, hA0, hAi⟩, ?_⟩
  exact diagonal_coefficient f w hf hw0 hw

set_option maxHeartbeats 800000 in
private theorem normalized_square_unique (a b : PowerSeries ℚ)
    (ha : constantCoeff a = 1) (hb : constantCoeff b = 1)
    (he : a ^ 2 = b ^ 2) : a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact h
  · have hc := congrArg (constantCoeff (R := ℚ)) h
    rw [ha, map_neg, hb] at hc
    norm_num at hc

set_option maxHeartbeats 800000 in
theorem result : D5.S3.Combinatorics.PowerSeries.BalaA337389Diagonal.claim := by
  intro k
  obtain ⟨d, A, hcol, hc⟩ := canonical_column k
  refine ⟨⟨d, A, hcol⟩, ?_⟩
  intro e B hB n
  have he : e = d := normalized_square_unique e d hB.1 hcol.1
    (hB.2.1.trans hcol.2.1.symm)
  have hBA : B = A := normalized_square_unique B A hB.2.2.1 hcol.2.2.1 (by
    rw [hB.2.2.2, hcol.2.2.2, he])
  rw [hBA]
  exact hc n

end D5.S3.Combinatorics.PowerSeries.BalaA337389Diagonal

