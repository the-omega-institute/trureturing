/- GID: D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral diagonal construction proves square divisibility for every integer k. -/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.NumberTheory.Basic

/-!
Hanna's A365095 is the normalized integer series whose degree-(n-1) diagonal
of `(1 + (n-1) * X * A^2)^n * invOfUnit A 1 ^ n` vanishes for every n > 1.
Source: `Library/ArithSums/hanna2023a365095.md`.

The leading coefficient in the degree-m equation has multiplier -(m+1).
This is not an integer unit. Differentiating an (m+1)-st power proves that
its degree-m coefficient is divisible by m+1, making the triangular update
integral. The inverse-difference identity gives its exact leading change;
the resulting contraction constructs the series and proves uniqueness.

For every integer k, changing the parameter from n-1 to k*n-1 changes the
base of the n-th power by n times an integer series. Mathlib's
`dvd_sub_pow_of_dvd_sub` gives divisibility of the power difference by n^2.
Coefficient extraction after multiplication by the unit inverse power
transfers this congruence to the defining zero diagonal. The case n=1
uses divisibility by one.
-/

open PowerSeries
namespace D5.S1.Recurrence.Residue.PerturbedDiagonalSquareDivisibility

private def Agree (n : ℕ) (A B : PowerSeries ℤ) : Prop :=
  ∀ j < n, coeff j A = coeff j B

private theorem agree_iff (n : ℕ) (A B : PowerSeries ℤ) :
    Agree n A B ↔ (X : PowerSeries ℤ) ^ n ∣ A - B := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {A B : PowerSeries ℤ}
    (h : Agree n A B) (m : ℕ) : Agree n (A ^ m) (B ^ m) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow A B m))

private theorem leading_mul {n : ℕ} {U : PowerSeries ℤ}
    (h : X ^ n ∣ U) (V : PowerSeries ℤ) :
    coeff n (U * V) = coeff n U * constantCoeff V := by
  obtain ⟨W, rfl⟩ := h
  rw [mul_assoc]
  have hc (T : PowerSeries ℤ) : coeff n (X ^ n * T) = constantCoeff T := by
    simpa only [zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul T n 0
  rw [hc, hc, map_mul]

private theorem power_difference {n : ℕ} {A B : PowerSeries ℤ}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) (m : ℕ) :
    coeff n (A ^ m) - coeff n (B ^ m) =
      (m : ℤ) * (coeff n A - coeff n B) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow := (agree_iff _ _ _).mp (agree_pow h m)
    have hd := (agree_iff _ _ _).mp h
    have he : A ^ (m + 1) - B ^ (m + 1) =
        (A ^ m - B ^ m) * A + (A - B) * B ^ m := by ring
    rw [← map_sub, he, map_add, leading_mul hpow, leading_mul hd]
    simp only [map_sub, map_pow, hA, hB, one_pow, mul_one, ih, Nat.cast_add,
      Nat.cast_one]
    ring

private noncomputable def root (A : PowerSeries ℤ) (t : ℤ) : PowerSeries ℤ :=
  invOfUnit A 1 + C t * X * A

private theorem root_zero (A : PowerSeries ℤ) (t : ℤ) :
    constantCoeff (root A t) = 1 := by simp [root]

private theorem root_difference (A B : PowerSeries ℤ) (t : ℤ)
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) :
    root A t - root B t =
      (A - B) * (-(invOfUnit A 1 * invOfUnit B 1) + C t * X) := by
  have hAI := mul_invOfUnit A 1 hA
  have hBI := mul_invOfUnit B 1 hB
  have hi : invOfUnit A 1 - invOfUnit B 1 =
      (A - B) * (-(invOfUnit A 1 * invOfUnit B 1)) := by
    calc
      _ = (B * invOfUnit B 1) * invOfUnit A 1 -
          (A * invOfUnit A 1) * invOfUnit B 1 := by rw [hAI, hBI]; ring
      _ = _ := by ring
  dsimp [root]
  linear_combination hi

private noncomputable def residual (A : PowerSeries ℤ) (m : ℕ) : ℤ :=
  coeff m (root A m ^ (m + 1))

private theorem residual_difference {m : ℕ} {A B : PowerSeries ℤ}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree m A B) :
    residual A m - residual B m = -((m : ℤ) + 1) * (coeff m A - coeff m B) := by
  have hd := (agree_iff _ _ _).mp h
  have hr : Agree m (root A m) (root B m) := by
    apply (agree_iff _ _ _).mpr
    rw [root_difference A B m hA hB]
    exact dvd_mul_of_dvd_left hd _
  have hc : coeff m (root A m) - coeff m (root B m) =
      -(coeff m A - coeff m B) := by
    rw [← map_sub, root_difference A B m hA hB, leading_mul hd]
    simp
  unfold residual
  rw [power_difference (root_zero _ _) (root_zero _ _) hr, hc]
  push_cast
  ring

-- Differentiation makes the division in the triangular solve exact over the integers.
private theorem degree_power_dvd (F : PowerSeries ℤ) (m : ℕ) :
    ((m : ℤ) + 1) ∣ coeff m (F ^ (m + 1)) := by
  cases m with
  | zero => simp
  | succ r =>
    have hd := congrArg (coeff r) (derivative_pow F (r + 2))
    rw [coeff_derivative] at hd
    simp only [show r + 2 - 1 = r + 1 by omega, mul_assoc] at hd
    have hcast : (↑(r + 2) : PowerSeries ℤ) = C ((r : ℤ) + 2) := by simp
    rw [hcast, coeff_C_mul] at hd
    refine ⟨coeff (r + 1) (F ^ (r + 2)) -
      coeff r (F ^ (r + 1) * derivative ℤ F), ?_⟩
    push_cast at *
    linear_combination -hd

private theorem residual_dvd (A : PowerSeries ℤ) (m : ℕ) :
    ((m : ℤ) + 1) ∣ residual A m := degree_power_dvd _ _

private noncomputable def step (A : PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun m => if m = 0 then 1 else coeff m A + residual A m / ((m : ℤ) + 1)

private theorem step_zero (A : PowerSeries ℤ) : constantCoeff (step A) = 1 := by
  simp [step]

private theorem step_contract {n : ℕ} {A B : PowerSeries ℤ}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) : Agree (n + 1) (step A) (step B) := by
  intro m hm
  simp only [step, coeff_mk]
  split_ifs with hm0
  · rfl
  · have hd := residual_difference hA hB (m := m) (fun j hj => h j (by omega))
    have hqa := Int.ediv_mul_cancel (residual_dvd A m)
    have hqb := Int.ediv_mul_cancel (residual_dvd B m)
    have hp : (0 : ℤ) < (m : ℤ) + 1 := by positivity
    nlinarith

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | d + 1 => step (approximation d)

private theorem approximation_zero (d : ℕ) :
    constantCoeff (approximation d) = 1 := by
  cases d with
  | zero => simp [approximation]
  | succ d => exact step_zero _

private theorem approximation_stable {d s : ℕ} (h : d ≤ s) :
    Agree d (approximation d) (approximation s) := by
  induction d generalizing s with
  | zero => intro k hk; omega
  | succ d ih =>
    cases s with
    | zero => omega
    | succ s =>
      exact step_contract (approximation_zero d) (approximation_zero s) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) :
    Agree d generatingSeries (approximation d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  have h0 : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_zero]
  ext n
  exact (generating_agree (n + 2) n (by omega)).trans
    (step_contract h0 (approximation_zero (n + 1))
      (generating_agree (n + 1)) n (by omega)).symm

private theorem root_identity (A : PowerSeries ℤ) (t : ℤ)
    (hA : constantCoeff A = 1) :
    root A t = (1 + C t * X * A ^ 2) * invOfUnit A 1 := by
  have hi := mul_invOfUnit A 1 hA
  dsimp [root]
  linear_combination -(C t * X * A) * hi

private theorem diagonal_identity (A : PowerSeries ℤ) (t : ℤ) (n : ℕ)
    (hA : constantCoeff A = 1) :
    coeff (n - 1) ((1 + C t * X * A ^ 2) ^ n * invOfUnit A 1 ^ n) =
      coeff (n - 1) (root A t ^ n) := by
  rw [root_identity A t hA, mul_pow]

private theorem equation_iff (A : PowerSeries ℤ) :
    (coeff 0 A = 1 ∧ ∀ m : ℕ, 0 < m → residual A m = 0) ↔ A = step A := by
  constructor
  · rintro ⟨h0, hr⟩
    ext m
    simp only [step, coeff_mk]
    split_ifs with hm
    · subst m; exact h0
    · rw [hr m (by omega), Int.zero_ediv, add_zero]
  · intro hf
    have hc (m : ℕ) := congrArg (coeff m) hf
    refine ⟨?_, ?_⟩
    · simpa [step] using hc 0
    · intro m hm
      have hd := hc m
      simp only [step, coeff_mk, if_neg (by omega : m ≠ 0)] at hd
      have hq : residual A m / ((m : ℤ) + 1) = 0 := by omega
      have he := Int.ediv_mul_cancel (residual_dvd A m)
      rw [hq, zero_mul] at he
      exact he.symm

theorem generating_equation : coeff 0 generatingSeries = 1 ∧
    ∀ n : ℕ, 1 < n →
      coeff (n - 1) ((1 + C ((n : ℤ) - 1) * X * generatingSeries ^ 2) ^ n *
        invOfUnit generatingSeries 1 ^ n) = 0 := by
  obtain ⟨h0, hr⟩ := (equation_iff _).mpr generating_fixed
  refine ⟨h0, ?_⟩
  intro n hn
  rw [diagonal_identity _ _ _ (by simpa only [coeff_zero_eq_constantCoeff] using h0)]
  simpa only [residual, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one,
    Nat.sub_add_cancel (by omega : 1 ≤ n)] using hr (n - 1) (by omega)

private theorem fixed_unique {A B : PowerSeries ℤ}
    (hA : A = step A) (hB : B = step B) : A = B := by
  have hA0 : constantCoeff A = 1 := by rw [hA, step_zero]
  have hB0 : constantCoeff B = 1 := by rw [hB, step_zero]
  have ha : ∀ n, Agree n A B := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih => simpa only [← hA, ← hB] using step_contract hA0 hB0 ih
  ext n
  exact ha (n + 1) n (by omega)

theorem generating_unique (B : PowerSeries ℤ) (h0 : coeff 0 B = 1)
    (he : ∀ n : ℕ, 1 < n →
      coeff (n - 1) ((1 + C ((n : ℤ) - 1) * X * B ^ 2) ^ n *
        invOfUnit B 1 ^ n) = 0) : B = generatingSeries := by
  apply fixed_unique _ generating_fixed
  apply (equation_iff B).mp
  refine ⟨h0, ?_⟩
  intro m hm
  have hd := he (m + 1) (by omega)
  rw [diagonal_identity _ _ _ (by simpa only [coeff_zero_eq_constantCoeff] using h0)] at hd
  simpa [residual] using hd

noncomputable def perturbedDiagonal (k : ℤ) (n : ℕ) : ℤ :=
  coeff (n - 1) ((1 + C (k * (n : ℤ) - 1) * X * generatingSeries ^ 2) ^ n *
    invOfUnit generatingSeries 1 ^ n)

private theorem perturbation_square {R : Type*} [CommRing R] (B C : R) (n : ℕ) :
    (n : R) ^ 2 ∣ (B + (n : R) * C) ^ n - B ^ n := by
  have h : (n : R) ∣ (B + (n : R) * C) - B := by
    simpa only [add_sub_cancel_left] using dvd_mul_right (n : R) C
  simpa only [pow_one] using dvd_sub_pow_of_dvd_sub h 1

private theorem coeff_dvd_of_C_dvd (d : ℤ) (F : PowerSeries ℤ) (j : ℕ)
    (h : C d ∣ F) : d ∣ coeff j F := by
  obtain ⟨G, rfl⟩ := h
  rw [coeff_C_mul]
  exact dvd_mul_right _ _

theorem hanna_conjecture (k : ℤ) (n : ℕ) (hn : 0 < n) :
    (n : ℤ) ^ 2 ∣ perturbedDiagonal k n := by
  by_cases h1 : n = 1
  · subst n; simp
  have hn1 : 1 < n := by omega
  let A := generatingSeries
  let B : PowerSeries ℤ := 1 + C ((n : ℤ) - 1) * X * A ^ 2
  let T : PowerSeries ℤ := C (k - 1) * X * A ^ 2
  have hp : 1 + C (k * (n : ℤ) - 1) * X * A ^ 2 = B + (n : PowerSeries ℤ) * T := by
    dsimp [B, T]
    have hc : C (k * (n : ℤ) - 1) = C ((n : ℤ) - 1) +
        (n : PowerSeries ℤ) * C (k - 1) := by
      simp only [map_sub, map_mul, map_one, map_natCast]
      ring
    rw [hc]
    ring
  have hd : C ((n : ℤ) ^ 2) ∣
      ((1 + C (k * (n : ℤ) - 1) * X * A ^ 2) ^ n - B ^ n) *
        invOfUnit A 1 ^ n := by
    rw [hp]
    have hh : C ((n : ℤ) ^ 2) = (n : PowerSeries ℤ) ^ 2 := by simp
    rw [hh]
    exact dvd_mul_of_dvd_left (perturbation_square B T n) _
  have hc := coeff_dvd_of_C_dvd _ _ (n - 1) hd
  have hz : coeff (n - 1) (B ^ n * invOfUnit A 1 ^ n) = 0 :=
    generating_equation.2 n hn1
  rw [sub_mul, map_sub, hz, sub_zero] at hc
  exact hc

#print axioms a
#print axioms generatingSeries
#print axioms perturbedDiagonal
#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Residue.PerturbedDiagonalSquareDivisibility
