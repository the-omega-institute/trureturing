/- GID: D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The diagonal derivative equation has Hanna's two Mersenne parity supports. -/

/-
proof_shape: G: bind-only (definition); consumers: Q_equation, G_odd_coeff, P_fixed, G_mul.
proof_shape: Q: bind-only (definition); consumers: Q_equation, Q_algebra, P_nonlinear, P_fixed.
proof_shape: solution: bind-only (definition); consumers: diagonal_integral_parity, solution_fixed, exists_integral, integral_unique.
proof_shape: step: bind-only (definition); consumers: fixed_map, solution, solution_fixed, P_fixed, step_zero, fixed_unique, fixed_exists_unique, exists_integral, step_agree, diagonal_iff, integral_unique.
proof_shape: T: bind-only (definition); consumers: P_euler, Q_equation, Q, Q_algebra, T_zero, P_zero, P_nonlinear, P_support, T_support, P_fixed, T_euler, T_fixed, T_fraction, P, cube_euler, recip_P, T_even_coeff.
proof_shape: claim: bind-only (definition); consumers: result.
proof_shape: IsDiagonal: bind-only (definition); consumers: diagonal_integral_parity, D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParityA375452.result, exists_integral, result, diagonal_iff, integral_unique.
proof_shape: euler: bind-only (definition); consumers: P_euler, euler_agree, square_odd_coeff, nonlinear_agree, P_nonlinear, P_fixed, nonlinear_map, T_euler, cube_euler, euler_zero, quotient_coeff, nonlinear, euler_map, T_even_coeff, euler_coeff.
proof_shape: P: bind-only (definition); consumers: P_euler, diagonal_integral_parity, Q_equation, Q, Q_algebra, P_zero, P_nonlinear, P_support, P_fixed, recip_P.
proof_shape: IsGF: bind-only (definition); consumers: claim, result.
proof_shape: nonlinear: bind-only (definition); consumers: fixed_map, nonlinear_agree, step, P_nonlinear, P_fixed, step_zero, nonlinear_map, quotient_coeff, step_agree, diagonal_iff.
proof_shape: euler_coeff: bind-only; consumers: euler_agree, euler_map, square_odd_coeff, T_even_coeff, quotient_coeff.
proof_shape: euler_zero: bind-only; consumers: nonlinear_agree.
proof_shape: recip_mul: bind-only; consumers: recip_map, recip_P, quotient_coeff.
proof_shape: euler_agree: bind-only; consumers: nonlinear_agree.
proof_shape: recip_agree: bind-only; consumers: nonlinear_agree.
proof_shape: nonlinear_agree: bind-only; consumers: step_agree.
proof_shape: step_zero: bind-only; consumers: fixed_exists_unique, fixed_map, diagonal_iff.
proof_shape: step_agree: bind-only; consumers: fixed_exists_unique.
proof_shape: fixed_exists_unique: bind-only; consumers: solution, solution_fixed, fixed_unique.
proof_shape: solution_fixed: bind-only; consumers: exists_integral, diagonal_integral_parity.
proof_shape: fixed_unique: bind-only; consumers: integral_unique, diagonal_integral_parity.
proof_shape: euler_map: bind-only; consumers: nonlinear_map.
proof_shape: recip_map: bind-only; consumers: nonlinear_map.
proof_shape: nonlinear_map: bind-only; consumers: fixed_map.
proof_shape: fixed_map: bind-only; consumers: exists_integral, diagonal_integral_parity.
proof_shape: T_zero: bind-only; consumers: P_zero, T_support.
proof_shape: T_fixed: bind-only; consumers: T_euler, T_fraction.
proof_shape: P_zero: bind-only; consumers: recip_P, P_fixed.
proof_shape: derivative_square: bind-only; consumers: T_euler, P_euler, square_odd_coeff.
proof_shape: T_euler: bind-only; consumers: P_euler, cube_euler, T_even_coeff.
proof_shape: P_euler: bind-only; consumers: P_nonlinear, P_fixed.
proof_shape: cube_euler: bind-only; consumers: T_even_coeff.
proof_shape: square_odd_coeff: bind-only; consumers: P_fixed, P_support.
proof_shape: T_even_coeff: bind-only; consumers: P_fixed, P_support.
proof_shape: recip_P: bind-only; consumers: Q_algebra, Q_equation, P_nonlinear.
proof_shape: Q_algebra: bind-only; consumers: Q_equation.
proof_shape: T_fraction: bind-only; consumers: Q_equation.
proof_shape: G_mul: bind-only; consumers: Q_equation.
proof_shape: Q_equation: bind-only; consumers: P_fixed.
proof_shape: P_nonlinear: bind-only; consumers: P_fixed.
proof_shape: G_odd_coeff: bind-only; consumers: P_fixed.
proof_shape: P_fixed: bind-only; consumers: diagonal_integral_parity.
proof_shape: quotient_coeff: bind-only; consumers: diagonal_iff.
proof_shape: diagonal_iff: bind-only; consumers: exists_integral, integral_unique.
proof_shape: exists_integral: bind-only; consumers: integral_unique, diagonal_integral_parity.
proof_shape: integral_unique: bind-only; consumers: diagonal_integral_parity.
proof_shape: T_support: bind-only; consumers: P_support.
proof_shape: even_support: bind-only; consumers: P_support.
proof_shape: odd_support: bind-only; consumers: P_support.
proof_shape: P_support: bind-only; consumers: diagonal_integral_parity.
proof_shape: diagonal_integral_parity: bind-only; consumers: result, D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParityA375452.result.
proof_shape: result: bind-only; settles A375449.
escape_witness: none
admission_basis: open-problem-resolution (#18827; Proved)
Direct frozen dependency identities are provided in the handover.
Escape audit unfinished for the published step definition: https://github.com/the-omega-institute/trureturing/issues/21518.
Escape audit unfinished for HannaDiagonalDerivativeParity.diagonal_integral_parity, HannaDiagonalDerivativeParity.result, HannaDiagonalDerivativeParityA375452.result, UnitReversionSquareParity.mersenne_zero, UnitReversionSquareParity.mersenne_step, LinearExponentDyadicSupport.square_odd and LinearExponentDyadicSupport.derivative_map: https://github.com/the-omega-institute/trureturing/issues/19834.
The definitions state Hanna's generating equation and parity conjecture.
The strict contraction is instantiated through PowerSeriesNormalizedContraction.exists_unique_fixed.
This unbounded symbolic proof performs no finite-instance computation; utility is none.
-/

import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
import D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
import Mathlib.RingTheory.PowerSeries.Derivative


set_option autoImplicit false
set_option maxHeartbeats 800000
open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_iff agree_mul)

section General
variable {R : Type*} [CommRing R]
private noncomputable def euler (f : PowerSeries R) : PowerSeries R := X * derivative (R := R) f
private noncomputable def nonlinear (c : R) (f : PowerSeries R) : PowerSeries R := euler f * f * (invOfUnit (1 - C c * f) 1)
noncomputable def step (t : ℕ → R) (f : PowerSeries R) : PowerSeries R :=
  mk fun n => if n = 0 then 0 else t n - coeff n (nonlinear (n : R) f)

private theorem euler_coeff (f : PowerSeries R) (n : ℕ) : coeff n (euler f) = (n : R) * coeff n f := by
  cases n with
  | zero => simp [euler]
  | succ n => simp [euler, coeff_succ_X_mul, coeff_derivative, mul_comm]

private theorem euler_zero (f : PowerSeries R) : constantCoeff (euler f) = 0 := by
  simp [euler]

private theorem recip_mul (c : R) {f : PowerSeries R} (hf : constantCoeff f = 0) :
    (invOfUnit (1 - C c * f) 1) * (1 - C c * f) = 1 := by
  exact invOfUnit_mul _ _ (by simp [hf])

private theorem euler_agree {d : ℕ} {f g : PowerSeries R} (h : Agree d f g) :
    Agree d (euler f) (euler g) := by
  intro n hn
  simp only [euler_coeff, h n hn]

private theorem recip_agree (c : R) {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree d f g) :
    Agree d ((invOfUnit (1 - C c * f) 1)) ((invOfUnit (1 - C c * g) 1)) := by
  apply D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_inv (by simp [hf]) (by simp [hg])
  intro n hn
  simp only [map_sub, coeff_C_mul, h n hn]

private theorem nonlinear_agree (c : R) {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree d f g) :
    Agree (d + 1) (nonlinear c f) (nonlinear c g) := by
  have hi := agree_mul h (recip_agree c hf hg h)
  apply (agree_iff _ _ _).mpr
  have h1 := mul_dvd_mul (X_dvd_iff.mpr (euler_zero f)) ((agree_iff _ _ _).mp hi)
  have h2 := mul_dvd_mul ((agree_iff _ _ _).mp (euler_agree h))
    (X_dvd_iff.mpr (show constantCoeff (g * (invOfUnit (1 - C c * g) 1)) = 0 by simp [hg]))
  rw [mul_comm X, ← pow_succ] at h1
  rw [← pow_succ] at h2
  convert dvd_add h1 h2 using 1 <;> dsimp only [nonlinear] <;> ring

private theorem step_zero (t : ℕ → R) (f : PowerSeries R) : constantCoeff (step t f) = 0 := by
  simp [step]

private theorem step_agree (t : ℕ → R) {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree d f g) :
    Agree (d + 1) (step t f) (step t g) := by
  intro n hn
  simp only [step, coeff_mk]
  split_ifs with h0
  · rfl
  · rw [nonlinear_agree (n : R) hf hg h n hn]

private theorem fixed_exists_unique (t : ℕ → R) :
    ∃ f : PowerSeries R, constantCoeff f = 0 ∧ f = step t f ∧
      ∀ g, g = step t g → g = f := by
  let F : PowerSeries R → PowerSeries R := fun b => 1 + step t (b - 1)
  have h0 : ∀ b, constantCoeff b = 1 → constantCoeff (F b) = 1 := by
    intro b hb
    simp [F, step_zero]
  have hc : ∀ {d : ℕ} {f g : PowerSeries R}, 1 ≤ d →
      constantCoeff f = 1 → constantCoeff g = 1 → Agree d f g →
      Agree (d + 1) (F f) (F g) := by
    intro d f g hd hf hg h n hn
    have he : Agree d (f - 1) (g - 1) := by
      intro k hk
      simp only [map_sub, h k hk]
    have hs := step_agree t (by simp [hf]) (by simp [hg]) he n hn
    simpa only [F, map_add] using congrArg (fun r => coeff n (1 : PowerSeries R) + r) hs
  obtain ⟨b, hb, hfix, huniq⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed F h0 hc
  refine ⟨b - 1, by simp [hb], ?_, ?_⟩
  · have he := congrArg (fun f : PowerSeries R => f - 1) hfix
    simpa [F] using he
  · intro g hg
    have hg0 : constantCoeff g = 0 := by rw [hg]; exact step_zero t g
    have he := huniq (g + 1) (by simp [hg0]) (by simpa [F, add_comm] using congrArg (fun f : PowerSeries R => f + 1) hg)
    exact eq_sub_iff_add_eq.mpr he

private noncomputable def solution (t : ℕ → R) : PowerSeries R :=
  Classical.choose (fixed_exists_unique t)

private theorem solution_fixed (t : ℕ → R) : solution t = step t (solution t) :=
  (Classical.choose_spec (fixed_exists_unique t)).2.1

private theorem fixed_unique (t : ℕ → R) {f g : PowerSeries R}
    (hf : f = step t f) (hg : g = step t g) : f = g :=
  ((Classical.choose_spec (fixed_exists_unique t)).2.2 f hf).trans
    ((Classical.choose_spec (fixed_exists_unique t)).2.2 g hg).symm

variable {S : Type*} [CommRing S]

private theorem euler_map (hom : R →+* S) (f : PowerSeries R) :
    (euler f).map hom = euler (f.map hom) := by
  unfold euler
  rw [map_mul, map_X]
  congr 1
  exact D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.derivative_map hom f

private theorem recip_map (hom : R →+* S) (c : R) {f : PowerSeries R} (hf : constantCoeff f = 0) :
    ((invOfUnit (1 - C c * f) 1)).map hom = (invOfUnit (1 - C (hom c) * (f.map hom)) 1) := by
  simpa only [map_sub, map_one, map_mul, map_C] using
    D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.map_inverse hom
      (1 - C c * f) (by simp [hf])

private theorem nonlinear_map (hom : R →+* S) (c : R) {f : PowerSeries R} (hf : constantCoeff f = 0) :
    (nonlinear c f).map hom = nonlinear (hom c) (f.map hom) := by
  simp only [nonlinear, map_mul, euler_map, recip_map hom c hf]

private theorem fixed_map (hom : R →+* S) (t : ℕ → R) {f : PowerSeries R}
    (hf : f = step t f) : f.map hom = step (fun n => hom (t n)) (f.map hom) := by
  have hf0 : constantCoeff f = 0 := by rw [hf]; exact step_zero t f
  ext n
  have h := congrArg (fun f => hom (coeff n f)) hf
  simp only [coeff_map, step, coeff_mk] at h ⊢
  by_cases hn : n = 0
  · simpa [hn] using h
  · simp only [if_neg hn] at h ⊢
    have he : hom (coeff n (nonlinear (n : R) f)) =
        coeff n (nonlinear (n : S) (f.map hom)) := by
      conv_lhs => rw [← coeff_map]
      rw [nonlinear_map hom (n : R) hf0, map_natCast]
    simpa only [map_sub, he] using h

end General
end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity


set_option autoImplicit false
set_option maxHeartbeats 400000
open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_iff agree_mul)
private noncomputable def T : PowerSeries (ZMod 2) := D5.S1.Recurrence.Invariants.UnitReversionSquareParity.generatingSeries.map (Int.castRingHom (ZMod 2))
private noncomputable def P : PowerSeries (ZMod 2) := T + T ^ 2
private noncomputable def Q : PowerSeries (ZMod 2) := T * (invOfUnit (1 - C 1 * P) 1)
private noncomputable def G : PowerSeries (ZMod 2) := X * (mk fun _ : ℕ => (1 : ZMod 2)) ^ 2

private theorem T_zero : constantCoeff T = 0 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  rw [T, ← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
    D5.S1.Recurrence.Invariants.UnitReversionSquareParity.generating_equation.1, map_zero]

private theorem T_fixed : T = X + X * T ^ 2 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  rw [D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst 2]
  exact D5.S1.Recurrence.Invariants.UnitReversionSquareParity.mod_two_fixed

private theorem P_zero : constantCoeff P = 0 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  simp [P, T_zero]

private theorem derivative_square (f : PowerSeries (ZMod 2)) : derivative (R := ZMod 2) (f ^ 2) = 0 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  rw [derivative_pow, CharP.cast_eq_zero, zero_mul, zero_mul]

private theorem T_euler : euler T = T := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  have h := congrArg (derivative (R := ZMod 2)) T_fixed
  simp only [map_add, Derivation.leibniz, derivative_X, derivative_square, smul_eq_mul,
    mul_zero, mul_one, zero_add, one_mul] at h
  dsimp only [euler]
  rw [h]
  exact (by rw [mul_add, mul_one]; exact T_fixed.symm)

private theorem P_euler : euler P = T := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  simp only [P, euler, map_add, derivative_square, add_zero]
  exact T_euler

private theorem cube_euler : euler (T ^ 3) = T ^ 3 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  dsimp only [euler]
  rw [derivative_pow]
  have h3 : (3 : PowerSeries (ZMod 2)) = 1 := by
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
    linear_combination h2
  simp only [Nat.cast_ofNat]
  rw [h3, one_mul]
  change X * (T ^ 2 * derivative (R := ZMod 2) T) = _
  calc
    _ = T ^ 2 * euler T := by dsimp [euler]; ring
    _ = T ^ 3 := by rw [T_euler]; ring

private theorem square_odd_coeff (f : PowerSeries (ZMod 2)) (n : ℕ) (hn : Odd n) :
    coeff n (f ^ 2) = 0 := by
  obtain ⟨k, hk⟩ := hn
  have hindex : n = 2 * k + 1 := by omega
  rw [hindex]
  exact D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.square_odd f k

private theorem T_even_coeff (n : ℕ) (hn : Even n) : coeff n T = 0 ∧ coeff n (T ^ 3) = 0 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  have h := congrArg (coeff n) T_euler
  have h' := congrArg (coeff n) cube_euler
  have hn0 : (n : ZMod 2) = 0 := hn.natCast_zmod_two
  simp only [euler_coeff, hn0, zero_mul] at h h'
  exact ⟨h.symm, h'.symm⟩

private theorem recip_P : (invOfUnit (1 - C (1 : ZMod 2) * P) 1) * (1 + T + T ^ 2) = 1 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  have h := recip_mul (1 : ZMod 2) P_zero
  simpa [P, sub_eq_add_neg, CharTwo.neg_eq, add_assoc] using h

private theorem Q_algebra : Q + Q ^ 2 = T * (1 + T ^ 2) * ((invOfUnit (1 - C 1 * P) 1)) ^ 2 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  have h := recip_P
  dsimp only [Q]
  linear_combination (norm := (ring_nf; simp [show (2 : PowerSeries (ZMod 2)) = 0 from CharP.ofNat_eq_zero _ 2])) -T * (invOfUnit (1 - C 1 * P) 1) * h

private theorem T_fraction : T * (1 + T ^ 2) * (1 + X ^ 2) = X * (1 + T ^ 2 + T ^ 4) := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  have h := T_fixed
  have h' : T ^ 2 = X ^ 2 + X ^ 2 * T ^ 4 := by
    conv_lhs => rw [T_fixed, CharTwo.add_sq, mul_pow, ← pow_mul]
  linear_combination (norm := (ring_nf; simp [show (2 : PowerSeries (ZMod 2)) = 0 from CharP.ofNat_eq_zero _ 2]))
    (1 + T ^ 2) * (1 + X ^ 2) * h + X * h'

private theorem G_mul : G * (1 + X ^ 2) = X := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  let H : PowerSeries (ZMod 2) := mk fun _ : ℕ => 1
  have h : H * (1 + X) = 1 := by
    change (mk (1 : ℕ → ZMod 2)) * (1 + X) = 1
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using mk_one_mul_one_sub_eq_one (ZMod 2)
  have h' := congrArg (fun f : PowerSeries (ZMod 2) => f ^ 2) h
  rw [mul_pow, CharTwo.add_sq] at h'
  change (X * H ^ 2) * (1 + X ^ 2) = X
  have hs : H ^ 2 * (1 + X ^ 2) = 1 := by simpa only [one_pow] using h'
  rw [mul_assoc, hs, mul_one]

private theorem Q_equation : Q + Q ^ 2 = G := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  have hu := congrArg (fun f : PowerSeries (ZMod 2) => f ^ 2) recip_P
  rw [mul_pow, CharTwo.add_sq, CharTwo.add_sq] at hu
  have hu' : ((invOfUnit (1 - C (1 : ZMod 2) * P) 1)) ^ 2 * (1 + T ^ 2 + T ^ 4) = 1 := by
    simpa only [one_pow, ← pow_mul] using hu
  apply mul_right_cancel₀ (show (1 + X ^ 2 : PowerSeries (ZMod 2)) ≠ 0 by
    intro he; have hc := congrArg constantCoeff he; simpa using hc)
  rw [G_mul, Q_algebra]
  calc
    _ = (T * (1 + T ^ 2) * (1 + X ^ 2)) * ((invOfUnit (1 - C 1 * P) 1)) ^ 2 := by ring
    _ = X * (((invOfUnit (1 - C 1 * P) 1)) ^ 2 * (1 + T ^ 2 + T ^ 4)) := by rw [T_fraction]; ring
    _ = X := by rw [hu', mul_one]

private theorem P_nonlinear : P + nonlinear (1 : ZMod 2) P = T ^ 2 + Q := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  rw [nonlinear, P_euler]
  change (T + T ^ 2) + T * (T + T ^ 2) * (invOfUnit (1 - C 1 * P) 1) = T ^ 2 + T * (invOfUnit (1 - C 1 * P) 1)
  linear_combination (norm := (ring_nf; simp [show (2 : PowerSeries (ZMod 2)) = 0 from CharP.ofNat_eq_zero _ 2])) T * recip_P

private theorem G_odd_coeff (n : ℕ) (hn : Odd n) : coeff n G = 1 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  rcases n with _ | n
  · simp at hn
  · have hd : 2 ∣ n := (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn)).two_dvd
    rw [G, coeff_succ_X_mul, D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst 2, coeff_subst_X_pow (by decide), if_pos hd]
    simp

private theorem P_fixed (t : ℕ → ZMod 2) (ht : ∀ n, 1 ≤ n → t n = (n : ZMod 2)) :
    P = step t P := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [step, coeff_zero_eq_constantCoeff, P_zero]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  rcases Nat.even_or_odd n with he | ho
  · have hncast : (n : ZMod 2) = 0 := he.natCast_zmod_two
    have heT := T_even_coeff n he
    have hr : (invOfUnit (1 - C (0 : ZMod 2) * P) 1) = 1 := by
      rw [map_zero, zero_mul, sub_zero, invOfUnit_eq' _ _ (by simp)]
      simp
    have hB : nonlinear (0 : ZMod 2) P = T ^ 2 + T ^ 3 := by
      rw [nonlinear, P_euler, hr, mul_one, P]; ring
    rw [step, coeff_mk, if_neg hn0, ht n hn, hncast, hB]
    simp only [P, map_add, heT.1, heT.2, zero_add, add_zero, zero_sub, CharTwo.neg_eq]
  · have hncast : (n : ZMod 2) = 1 := ho.natCast_zmod_two
    have h := congrArg (coeff n) P_nonlinear
    have hq := congrArg (coeff n) Q_equation
    simp only [map_add, square_odd_coeff _ n ho, zero_add, add_zero, G_odd_coeff n ho] at h hq
    rw [hq] at h
    simp only [step, coeff_mk, if_neg hn0, ht n hn, hncast]
    exact eq_sub_iff_add_eq.mpr h

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity

set_option autoImplicit false
set_option maxHeartbeats 400000
open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_iff agree_mul)

def IsDiagonal (t : ℕ → ℚ) (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ ∀ n, 1 ≤ n →
    coeff n (X * derivative (R := ℚ) A * (1 - C (n : ℚ) * A)⁻¹) = (n : ℚ) * t n

private theorem quotient_coeff (A : PowerSeries ℚ) (hA : constantCoeff A = 0) (n : ℕ) :
    coeff n (X * derivative (R := ℚ) A * (1 - C (n : ℚ) * A)⁻¹) =
      (n : ℚ) * (coeff n A + coeff n (nonlinear (n : ℚ) A)) := by
  have hr : (invOfUnit (1 - C (n : ℚ) * A) 1) = (1 - C (n : ℚ) * A)⁻¹ :=
    invOfUnit_eq' _ _ (by simp [hA])
  have hu := recip_mul (n : ℚ) hA
  have he : euler A * (invOfUnit (1 - C (n : ℚ) * A) 1) = euler A + C (n : ℚ) * nonlinear (n : ℚ) A := by
    dsimp only [nonlinear]
    linear_combination euler A * hu
  change coeff n (euler A * (1 - C (n : ℚ) * A)⁻¹) = _
  rw [← hr, he, map_add, euler_coeff, coeff_C_mul]
  ring

private theorem diagonal_iff (t : ℕ → ℚ) (A : PowerSeries ℚ) : IsDiagonal t A ↔ A = step t A := by
  constructor
  · intro h
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp [step, coeff_zero_eq_constantCoeff, h.1]
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have he := h.2 n hn
    rw [quotient_coeff A h.1 n] at he
    simp only [step, coeff_mk, if_neg hn0]
    apply eq_sub_iff_add_eq.mpr
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn0) he
  · intro h
    have hz : constantCoeff A = 0 := by rw [h]; exact step_zero t A
    refine ⟨hz, fun n hn => ?_⟩
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
    have hc := congrArg (coeff n) h
    simp only [step, coeff_mk, if_neg hn0] at hc
    rw [quotient_coeff A hz n, hc]
    ring

private theorem exists_integral (t : ℕ → ℤ) :
    IsDiagonal (fun n => (t n : ℚ)) ((solution t).map (Int.castRingHom ℚ)) := by
  rw [diagonal_iff]
  exact fixed_map (Int.castRingHom ℚ) t (solution_fixed t)

private theorem integral_unique (t : ℕ → ℤ) (A : PowerSeries ℚ)
    (hA : IsDiagonal (fun n => (t n : ℚ)) A) :
    A = (solution t).map (Int.castRingHom ℚ) := by
  exact fixed_unique _ ((diagonal_iff _ _).mp hA)
    ((diagonal_iff _ _).mp (exists_integral t))

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity

set_option autoImplicit false
set_option maxHeartbeats 400000
open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_iff agree_mul)

private theorem T_support (n : ℕ) : coeff n T = 1 ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 1 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  by_cases hn : n = 0
  · subst n
    simp only [coeff_zero_eq_constantCoeff, T_zero, zero_ne_one, false_iff]
    exact D5.S1.Recurrence.Invariants.UnitReversionSquareParity.mersenne_zero
  · change ((D5.S1.Recurrence.Invariants.UnitReversionSquareParity.a n : ℤ) : ZMod 2) = 1 ↔ _
    rw [ZMod.intCast_eq_one_iff_odd]
    exact D5.S1.Recurrence.Invariants.UnitReversionSquareParity.hanna_conjecture n (by omega)

private theorem even_support (n : ℕ) (he : Even n) :
    (∃ k : ℕ, 1 ≤ k ∧ n / 2 = 2 ^ k - 1) ↔
      ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1) := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  by_cases hn : n = 0
  · subst n
    have hz : ¬ ∃ k : ℕ, 1 ≤ k ∧ 0 = 2 ^ k - 1 :=
      D5.S1.Recurrence.Invariants.UnitReversionSquareParity.mersenne_zero
    constructor
    · intro h
      exact False.elim (hz (by simpa using h))
    · rintro ⟨k, hk, h | h⟩
      · have hp : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k)
        omega
      · have hp : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k)
        omega
  · have hs : (∃ k : ℕ, 1 ≤ k ∧ n + 1 = 2 ^ k - 1) ↔
        2 ∣ n ∧ ∃ k : ℕ, 1 ≤ k ∧ n / 2 = 2 ^ k - 1 :=
      D5.S1.Recurrence.Invariants.UnitReversionSquareParity.mersenne_step n (Nat.pos_of_ne_zero hn)
    constructor
    · intro h
      obtain ⟨k, hk, heq⟩ := hs.mpr ⟨he.two_dvd, h⟩
      have hk1 : k ≠ 1 := by
        intro h1
        have he1 : n + 1 = 0 + 1 := by simpa only [h1, pow_one, Nat.reduceSub] using heq
        exact hn (Nat.add_right_cancel he1)
      refine ⟨k, by omega, Or.inl ?_⟩
      omega
    · rintro ⟨k, hk, h | h⟩
      · have hp : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k)
        exact (hs.mp ⟨k, by omega, by omega⟩).2
      · have hp : Even (2 ^ k) := Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (by omega : k ≠ 0)
        rcases he with ⟨a, ha⟩
        rcases hp with ⟨b, hb⟩
        omega

private theorem odd_support (n : ℕ) (hn : 1 < n) (ho : Odd n) :
    (∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 1) ↔
      ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1) := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  constructor
  · rintro ⟨k, hk, h⟩
    refine ⟨k, ?_, Or.inr h⟩
    by_contra hk'
    have : k = 1 := by omega
    simp [this] at h
    omega
  · rintro ⟨k, hk, h | h⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hp := Nat.one_le_pow j 2 (by omega)
      rw [pow_succ] at h
      rcases ho with ⟨m, hm⟩
      omega
    · exact ⟨k, by omega, h⟩

private theorem P_support (n : ℕ) (hn : 1 < n) : coeff n P = 1 ↔
    ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1) := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom (f := C) C_injective 2
  rcases Nat.even_or_odd n with he | ho
  · have hd := he.two_dvd
    rw [P, map_add, (T_even_coeff n he).1, zero_add, D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst 2,
      coeff_subst_X_pow (by decide), if_pos hd, Algebra.algebraMap_self, RingHom.id_apply,
      T_support, even_support n he]
  · rw [P, map_add, square_odd_coeff T n ho, add_zero, T_support, odd_support n hn ho]

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity

set_option autoImplicit false
set_option maxHeartbeats 400000
open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree agree_iff agree_mul)

theorem diagonal_integral_parity (t : ℕ → ℤ)
    (ht : ∀ n, 1 ≤ n → (t n : ZMod 2) = (n : ZMod 2)) :
    (∃ A, IsDiagonal (fun n => (t n : ℚ)) A) ∧
    ∀ A, IsDiagonal (fun n => (t n : ℚ)) A → ∀ n : ℕ, 1 < n →
      ∃ m : ℤ, coeff n A = m ∧
        (Odd m ↔ ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1)) := by
  refine ⟨⟨_, exists_integral t⟩, ?_⟩
  intro A hA n hn
  refine ⟨coeff n (solution t), ?_, ?_⟩
  · rw [integral_unique t A hA, coeff_map]
    rfl
  · rw [← ZMod.intCast_eq_one_iff_odd]
    have he := fixed_unique (fun n => (t n : ZMod 2))
      (fixed_map (Int.castRingHom (ZMod 2)) t (solution_fixed t))
      (P_fixed _ ht)
    have hc := congrArg (coeff n) he
    simp only [coeff_map, Int.coe_castRingHom] at hc
    rw [hc]
    exact P_support n hn

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity



set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity

open PowerSeries

/-- OEIS A375449: "Expansion of g.f. A(x) satisfying [x^n] x*A'(x) / (1 - n*A(x)) = n^(n+1) for n >= 1",
offset 1. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧
    ∀ n : ℕ, 1 ≤ n → coeff n (X * derivative (R := ℚ) A * (1 - C (n : ℚ) * A)⁻¹) = (n : ℚ) ^ (n + 1)

/-- OEIS A375449 (P. D. Hanna), conjecture: "for n > 1, a(n) is odd iff n is of the form 2^k-2 or 2^k-1
for some k > 1." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 1 < n → ∃ m : ℤ, coeff n A = m ∧
      (Odd m ↔ ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1))

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity

namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
open PowerSeries

theorem result : claim := by
  let t : ℕ → ℤ := fun n => (n : ℤ) ^ n
  have ht : ∀ n, 1 ≤ n → (t n : ZMod 2) = (n : ZMod 2) := by
    intro n hn
    dsimp only [t]
    push_cast
    rcases Nat.even_or_odd n with he | ho
    · rw [he.natCast_zmod_two, zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
    · rw [ho.natCast_zmod_two, one_pow]
  have hp : ∀ n : ℕ, 1 ≤ n → (n : ℚ) * (t n : ℚ) = (n : ℚ) ^ (n + 1) := by
    intro n hn
    dsimp only [t]
    push_cast
    rw [pow_succ]; ring
  have hequiv : ∀ A : PowerSeries ℚ, IsGF A ↔ IsDiagonal (fun n => (t n : ℚ)) A := by
    intro A
    constructor
    · rintro ⟨h0, hA⟩
      exact ⟨h0, fun n hn => (hA n hn).trans (hp n hn).symm⟩
    · rintro ⟨h0, hA⟩
      exact ⟨h0, fun n hn => (hA n hn).trans (hp n hn)⟩
  have h := diagonal_integral_parity t ht
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA⟩ := h.1
    exact ⟨A, (hequiv A).mpr hA⟩
  · intro A hA
    exact h.2 A ((hequiv A).mp hA)

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
