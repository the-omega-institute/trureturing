/- GID: D5/S1/Recurrence/Algebraic/SchroderIntegralEGF
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/SchroderIntegralEGF
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A338193 EGF coefficients equal Kurkov's two-index recurrence. -/

import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)

namespace D5.S1.Recurrence.Algebraic.SchroderIntegralEGF

/-- Kurkov's three recurrences, constructed in naturals by degree then row index. -/
def f : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, m + 1 => f 0 m + (m + 1) * f 1 m
  | j + 1, m + 1 => f j (m + 1) + (m + 1) * (f (j + 1) m + f (j + 2) m)
termination_by j m => (m, j)

private noncomputable def F (j : ℕ) : PowerSeries ℚ := encode (fun m => f j m)
private noncomputable def R : PowerSeries ℚ := largeSchroderSeries.map (Nat.castRingHom ℚ)

private theorem R_eq : R = 1 + X * R + X * R ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
    largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  simpa only [map_add, map_one, map_mul, map_X, map_pow, R] using h

private theorem R_zero : constantCoeff R = 1 := by
  simp [R, ← coeff_zero_eq_constantCoeff, coeff_map]
private theorem F_zero (j : ℕ) : constantCoeff (F j) = 1 := by simp [F, f]
private theorem F_coeff (j m : ℕ) : eCoeff (F j) m = (f j m : ℚ) := eCoeff_encode _ _

private theorem row_eq (j : ℕ) : F (j + 1) = F j + X * (F (j + 1) + F (j + 2)) := by
  apply eCoeff_ext
  intro m
  cases m with
  | zero => simp [eCoeff_zero, F_zero]
  | succ m =>
    have hadd (a b : PowerSeries ℚ) (k : ℕ) : eCoeff (a+b) k = eCoeff a k + eCoeff b k := by
      simp [eCoeff, mul_add]
    rw [hadd, eCoeff_X_mul, hadd, F_coeff, F_coeff, F_coeff, F_coeff, f]
    push_cast
    ring

private theorem model_row (j : ℕ) : F 0 * R ^ (j+1) = F 0 * R ^ j +
    X * (F 0 * R ^ (j+1) + F 0 * R ^ (j+2)) := by
  have h := R_eq
  rw [pow_succ, show j+2 = (j+1)+1 by omega, pow_succ, pow_succ]
  linear_combination F 0 * R ^ j * h

/-- At each degree, induction along the rows identifies the entire infinite family. -/
private theorem row_factor (j : ℕ) : F j = F 0 * R ^ j := by
  have h : ∀ m j, coeff m (F j) = coeff m (F 0 * R ^ j) := by
    intro m
    induction m with
    | zero => intro j; simp [coeff_zero_eq_constantCoeff, F_zero, R_zero]
    | succ m ih =>
      intro j
      induction j with
      | zero => simp
      | succ j hj =>
        have hF := congrArg (coeff (m+1)) (row_eq j)
        have hG := congrArg (coeff (m+1)) (model_row j)
        simp only [map_add, coeff_succ_X_mul] at hF hG
        rw [hj, ih, ih] at hF
        exact hF.trans hG.symm
  ext m
  exact h m j

private noncomputable def B : PowerSeries ℚ := F 0 * (1 - X * R)
private theorem B_zero : constantCoeff B = 1 := by simp [B, F_zero]
private theorem B_derivative : derivative ℚ B = F 0 := by
  have hb : B = F 0 - X * F 1 := by rw [row_factor 1]; simp only [pow_one, B]; ring
  apply eCoeff_ext
  intro m
  rw [eCoeff_derivative, hb]
  have hsub (a b : PowerSeries ℚ) (k : ℕ) : eCoeff (a-b) k = eCoeff a k - eCoeff b k := by
    simp [eCoeff, mul_sub]
  rw [hsub]
  rw [F_coeff, eCoeff_X_mul, F_coeff, F_coeff, f]
  push_cast
  ring

private noncomputable def D : PowerSeries ℚ := 1 - X * R

private theorem D_zero : constantCoeff D = 1 := by simp [D]
private theorem D_quadratic : D ^ 2 - (1 + X) * D + 2 * X = 0 := by
  dsimp [D]
  linear_combination -X * R_eq

private def Algebraic (S : PowerSeries ℚ) : Prop :=
  (1 + X) * S * derivative ℚ S - 2 * X * (derivative ℚ S) ^ 2 - S ^ 2 = 0

private theorem B_algebraic : Algebraic B := by
  unfold Algebraic
  rw [B_derivative]
  change (1+X) * (F 0 * D) * F 0 - 2*X*(F 0)^2 - (F 0 * D)^2 = 0
  linear_combination -(F 0)^2 * D_quadratic

private theorem algebraic_iff_linear (S : PowerSeries ℚ) (hS : constantCoeff S = 1) :
    Algebraic S ↔ D * derivative ℚ S = S := by
  constructor
  · intro h
    have hz : (D * derivative ℚ S - S) *
        (2*X*D*derivative ℚ S - D^2*S) = 0 := by
      unfold Algebraic at h
      linear_combination -D^2 * h - D * S * derivative ℚ S * D_quadratic
    have hn : 2*X*D*derivative ℚ S - D^2*S ≠ 0 := by
      intro he
      have hc := congrArg constantCoeff he
      simp [D_zero, hS] at hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)
  · intro h
    have hD : D ≠ 0 := by intro hz; have := congrArg constantCoeff hz; simp [D_zero] at this
    apply (mul_left_cancel₀ (pow_ne_zero 2 hD))
    linear_combination -S^2 * D_quadratic +
      ((1+X)*D*S - 2*X*(D*derivative ℚ S+S)) * h

private noncomputable def primitive (S : PowerSeries ℚ) : PowerSeries ℚ :=
  mk (fun n => if n = 0 then 0 else coeff (n-1) S / n)

private theorem primitive_zero (S : PowerSeries ℚ) : constantCoeff (primitive S) = 0 := by
  simp [primitive]

private theorem derivative_primitive (S : PowerSeries ℚ) : derivative ℚ (primitive S) = S := by
  ext n
  simp [primitive, coeff_derivative, Nat.cast_add, Nat.cast_one,
    show (n : ℚ) + 1 ≠ 0 by positivity]

/-- The original formal integral equation, with integral constant zero. -/
def Original (S : PowerSeries ℚ) : Prop :=
  constantCoeff S = 1 ∧ S = 1 + primitive
    (derivative ℚ (X*S⁻¹) * (derivative ℚ (X*(S^2)⁻¹))⁻¹)

private theorem original_iff_cleared (S : PowerSeries ℚ) (hS : constantCoeff S = 1) :
    Original S ↔ derivative ℚ S * derivative ℚ (X*(S^2)⁻¹) = derivative ℚ (X*S⁻¹) := by
  have hd : constantCoeff (derivative ℚ (X*(S^2)⁻¹)) ≠ 0 := by
    simp [Derivation.leibniz, constantCoeff_inv, hS]
  constructor
  · intro h
    have he := congrArg (derivative ℚ) h.2
    simp only [map_add, derivative_one, derivative_primitive, zero_add] at he
    exact (eq_mul_inv_iff_mul_eq hd).mp he
  · intro h
    refine ⟨hS, PowerSeries.derivative.ext ?_ ?_⟩
    · simpa only [map_add, derivative_one, derivative_primitive, zero_add] using
        (eq_mul_inv_iff_mul_eq hd).mpr h
    · simp [hS, primitive_zero]

private theorem original_iff_algebraic (S : PowerSeries ℚ) (hS : constantCoeff S = 1) :
    Original S ↔ Algebraic S := by
  rw [original_iff_cleared S hS]
  have hSU : S * S⁻¹ = 1 := PowerSeries.mul_inv_cancel S (by simp [hS])
  have hS0 : S ≠ 0 := by intro hz; have := congrArg constantCoeff hz; simp [hS] at this
  have hN : derivative ℚ (X*S⁻¹) * S^2 = S - X*derivative ℚ S := by
    simp only [Derivation.leibniz, derivative_X, derivative_inv', smul_eq_mul]
    calc
      _ = S*(S*S⁻¹) - X*derivative ℚ S*(S*S⁻¹)^2 := by ring
      _ = _ := by rw [hSU]; ring
  have hQ : derivative ℚ (X*(S^2)⁻¹) * S^3 = S - 2*X*derivative ℚ S := by
    rw [pow_two, PowerSeries.mul_inv_rev]
    simp only [Derivation.leibniz, derivative_X, derivative_inv', smul_eq_mul]
    calc
      _ = S*(S*S⁻¹)^2 - 2*X*derivative ℚ S*(S*S⁻¹)^3 := by ring
      _ = _ := by rw [hSU]; ring
  have he : (derivative ℚ S * derivative ℚ (X*(S^2)⁻¹) - derivative ℚ (X*S⁻¹)) * S^3 =
      (1+X)*S*derivative ℚ S - 2*X*(derivative ℚ S)^2 - S^2 := by
    calc
      _ = derivative ℚ S * (derivative ℚ (X*(S^2)⁻¹)*S^3) -
          S*(derivative ℚ (X*S⁻¹)*S^2) := by ring
      _ = _ := by rw [hN, hQ]; ring
  unfold Algebraic
  rw [← he]
  exact ⟨fun h => by rw [h, sub_self, zero_mul],
    fun h => sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (pow_ne_zero 3 hS0))⟩

private theorem original_unique (S T : PowerSeries ℚ) (hS : Original S) (hT : Original T) :
    S = T := by
  have hlS := (algebraic_iff_linear S hS.1).mp ((original_iff_algebraic S hS.1).mp hS)
  have hlT := (algebraic_iff_linear T hT.1).mp ((original_iff_algebraic T hT.1).mp hT)
  have hD : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel D (by simp [D_zero])
  have heS : derivative ℚ S = D⁻¹ * S := by
    conv_rhs => rw [← hlS, ← mul_assoc, hD, one_mul]
  have heT : derivative ℚ T = D⁻¹ * T := by
    conv_rhs => rw [← hlT, ← mul_assoc, hD, one_mul]
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [coeff_zero_eq_constantCoeff] using hS.1.trans hT.1.symm
    | succ n =>
      have hs : coeff n (D⁻¹*S) = coeff n (D⁻¹*T) := by
        rw [coeff_mul, coeff_mul]
        apply sum_congr rfl
        intro ij hij
        have hb := Finset.mem_antidiagonal.mp hij
        rw [ih ij.2 (by omega)]
      have hS' := congrArg (coeff n) heS
      have hT' := congrArg (coeff n) heT
      rw [coeff_derivative] at hS' hT'
      exact mul_right_cancel₀ (by positivity : (n : ℚ)+1 ≠ 0)
        (hS'.trans (hs.trans hT'.symm))

private theorem B_original : Original B := (original_iff_algebraic B B_zero).mpr B_algebraic

/-- The source integral equation has exactly one rational formal solution of constant term one. -/
theorem original_exists_unique : ∃! S : PowerSeries ℚ, Original S :=
  ⟨B, B_original, fun S hS => original_unique S B hS B_original⟩

/-- A is chosen solely by the original integral equation and its initial condition. -/
noncomputable def A : PowerSeries ℚ := Classical.choose original_exists_unique

/-- The chosen series satisfies the original equation. -/
theorem A_original : Original A := (Classical.choose_spec original_exists_unique).1

/-- The OEIS conjecture, for every positive index, with factorial normalization. -/
theorem egf_coeff_eq_f (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℚ) * PowerSeries.coeff n A = (f 0 (n - 1) : ℚ) := by
  have hBA : B = A := original_unique B A B_original A_original
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change eCoeff A (m+1) = (f 0 m : ℚ)
  rw [← hBA, ← eCoeff_derivative, B_derivative, F_coeff]

#print axioms egf_coeff_eq_f
#print axioms original_exists_unique

end D5.S1.Recurrence.Algebraic.SchroderIntegralEGF
