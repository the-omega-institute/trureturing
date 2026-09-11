/- GID: D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Absolute reciprocal contraction and Lucas recursions prove Hanna's A380709 parity. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Parity.AbsoluteReciprocalCubeParity

noncomputable def absSeries (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => |coeff n F|)

private def Agree (n : ℕ) (F G : PowerSeries ℤ) : Prop :=
  ∀ i < n, coeff i F = coeff i G

private theorem agree_iff (n : ℕ) (F G : PowerSeries ℤ) :
    Agree n F G ↔ (X : PowerSeries ℤ) ^ n ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {F G : PowerSeries ℤ}
    (h : Agree n F G) (k : ℕ) : Agree n (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G k))

private theorem agree_abs {n : ℕ} {F G : PowerSeries ℤ} (h : Agree n F G) :
    Agree n (absSeries F) (absSeries G) := by
  intro i hi
  simp only [absSeries, coeff_mk, h i hi]

private theorem agree_inv {n : ℕ} {F G : PowerSeries ℤ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree n (invOfUnit F 1) (invOfUnit G 1) := by
  have hFI := mul_invOfUnit F 1 (by simpa using hF)
  have hGI := mul_invOfUnit G 1 (by simpa using hG)
  apply (agree_iff _ _ _).mpr
  have hd := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h)
    (-(invOfUnit F 1 * invOfUnit G 1))
  convert hd using 1
  linear_combination invOfUnit G 1 * hFI - invOfUnit F 1 * hGI

private noncomputable def step (F : PowerSeries ℤ) : PowerSeries ℤ :=
  1 + X * (absSeries (invOfUnit F 1)) ^ 3

private theorem step_constant (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  simp [step]

private theorem step_agree {n : ℕ} {F G : PowerSeries ℤ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree (n + 1) (step F) (step G) := by
  have hm := (agree_iff _ _ _).mp (agree_pow (agree_abs (agree_inv hF hG h)) 3)
  apply (agree_iff _ _ _).mpr
  convert mul_dvd_mul_left X hm using 1
  · ring
  · dsimp [step]; ring

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_constant (n : ℕ) : constantCoeff (approximation n) = 1 := by
  cases n with
  | zero => simp [approximation]
  | succ n => exact step_constant _

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree n (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero => intro i hi; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      exact step_agree (approximation_constant n) (approximation_constant m) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (n : ℕ) : Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = 1 + X * (absSeries (invOfUnit generatingSeries 1)) ^ 3 := by
  have h0 : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_constant]
  refine ⟨h0, ?_⟩
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree h0 (approximation_constant (i + 1))
      (generating_agree (i + 1)) i (by omega)).symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B = 1 + X * (absSeries (invOfUnit B 1)) ^ 3) : B = generatingSeries := by
  have h : ∀ n, Agree n B generatingSeries := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      have hs := step_agree h0 generating_equation.1 ih
      simpa only [step, ← hB, ← generating_equation.2] using hs
  ext i
  exact h (i + 1) i (by omega)

private theorem map_abs (F : PowerSeries ℤ) :
    (absSeries F).map (Int.castRingHom (ZMod 2)) = F.map (Int.castRingHom (ZMod 2)) := by
  ext n
  simp [coeff_map, absSeries, ZMod.intCast_abs_mod_two]

private noncomputable def reduced : PowerSeries (ZMod 2) :=
  generatingSeries.map (Int.castRingHom (ZMod 2))

private noncomputable def reciprocal : PowerSeries (ZMod 2) :=
  (invOfUnit generatingSeries 1).map (Int.castRingHom (ZMod 2))

private theorem reduced_constant : constantCoeff reduced = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [reduced, coeff_map, coeff_zero_eq_constantCoeff, generating_equation.1]

private theorem reciprocal_mul : reciprocal * reduced = 1 := by
  simpa only [reciprocal, reduced, map_mul, map_one] using
    congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
      (invOfUnit_mul generatingSeries 1 generating_equation.1)

private theorem reciprocal_equation : reciprocal = 1 + X * reciprocal ^ 4 := by
  have he : reduced = 1 + X * reciprocal ^ 3 := by
    simpa only [reduced, reciprocal, map_add, map_one, map_mul, map_X, map_pow, map_abs]
      using congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) generating_equation.2
  have hi : 1 = reciprocal + X * reciprocal ^ 4 := by
    calc
      1 = reciprocal * reduced := reciprocal_mul.symm
      _ = reciprocal + X * reciprocal ^ 4 := by rw [he]; ring
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (CharTwo.two_eq_zero (R := ZMod 2))
  linear_combination -hi - (X * reciprocal ^ 4) * htwo

private theorem reduced_quadratic : reduced = reduced ^ 2 + X * reciprocal ^ 2 := by
  have h := reciprocal_equation
  have hi := reciprocal_mul
  linear_combination reduced ^ 2 * h -
    (reduced - X * reciprocal ^ 2 * (reciprocal * reduced + 1)) * hi

private theorem digit (n k : ℕ) :
    (Nat.choose n k : ZMod 2) =
      (Nat.choose (n % 2) (k % 2) : ZMod 2) * (Nat.choose (n / 2) (k / 2) : ZMod 2) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := 2)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  exact_mod_cast h

private theorem ee (n k : ℕ) :
    (Nat.choose (2*n) (2*k) : ZMod 2) = (Nat.choose n k : ZMod 2) := by
  rw [digit]
  simp

private theorem eo (n k : ℕ) :
    (Nat.choose (2*n) (2*k+1) : ZMod 2) = 0 := by
  rw [digit]
  simp

private theorem oe (n k : ℕ) :
    (Nat.choose (2*n+1) (2*k) : ZMod 2) = (Nat.choose n k : ZMod 2) := by
  rw [digit]
  simp [show (2*n+1)/2 = n by omega]

private theorem oo (n k : ℕ) :
    (Nat.choose (2*n+1) (2*k+1) : ZMod 2) = (Nat.choose n k : ZMod 2) := by
  rw [digit]
  simp [show (2*n+1)/2 = n by omega, show (2*k+1)/2 = k by omega]

-- Repeated binary division reaches an odd lower index beneath an even upper index.
private theorem four_diag (r : ℕ) (hr : 0 < r) : (Nat.choose (4*r) r : ZMod 2) = 0 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rcases Nat.even_or_odd r with ⟨s, rfl⟩ | ⟨s, hs⟩
    · rw [show 4*(s+s) = 2*(4*s) by omega, show s+s = 2*s by omega, ee]
      exact ih s (by omega) (by omega)
    · rw [hs, show 4*(2*s+1) = 2*(4*s+2) by omega, eo]

private theorem q_even (r : ℕ) (hr : 0 < r) :
    (Nat.choose (4*(2*r)+1) (2*r) : ZMod 2) = 0 := by
  rw [show 4*(2*r)+1 = 2*(4*r)+1 by omega, oe, four_diag r hr]

private theorem q_one (r : ℕ) :
    (Nat.choose (4*(4*r+1)+1) (4*r+1) : ZMod 2) = (Nat.choose (4*r+1) r : ZMod 2) := by
  rw [show 4*(4*r+1)+1 = 2*(8*r+2)+1 by omega,
    show 4*r+1 = 2*(2*r)+1 by omega, oo,
    show 8*r+2 = 2*(4*r+1) by omega, ee]
  congr 2; omega

private theorem q_three (r : ℕ) :
    (Nat.choose (4*(4*r+3)+1) (4*r+3) : ZMod 2) = 0 := by
  rw [show 4*(4*r+3)+1 = 2*(8*r+6)+1 by omega,
    show 4*r+3 = 2*(2*r+1)+1 by omega, oo,
    show 8*r+6 = 2*(4*r+3) by omega, eo]

theorem lucas_recursion_q (r : ℕ) :
    Nat.choose (4 * (4 * r + 1) + 1) (4 * r + 1) % 2 = Nat.choose (4 * r + 1) r % 2 ∧
    Nat.choose (4 * (4 * r + 3) + 1) (4 * r + 3) % 2 = 0 ∧
    Nat.choose (4 * (2 * r) + 1) (2 * r) % 2 = (if r = 0 then 1 else 0) := by
  refine ⟨(ZMod.natCast_eq_natCast_iff' _ _ 2).mp (q_one r), ?_, ?_⟩
  · exact (ZMod.natCast_eq_natCast_iff' _ 0 2).mp (by simpa using q_three r)
  · by_cases hr : r = 0
    · simp [hr]
    · rw [if_neg hr]
      exact (ZMod.natCast_eq_natCast_iff' _ 0 2).mp (by simpa using q_even r (by omega))

private theorem h_even (r : ℕ) (hr : 0 < r) :
    (Nat.choose (4*(2*r)-1) (2*r) : ZMod 2) = (Nat.choose (4*r-1) r : ZMod 2) := by
  rw [show 4*(2*r)-1 = 2*(4*r-1)+1 by omega, oe]

private theorem h_odd (r : ℕ) :
    (Nat.choose (4*(2*r+1)-1) (2*r+1) : ZMod 2) = (Nat.choose (4*r+1) r : ZMod 2) := by
  rw [show 4*(2*r+1)-1 = 2*(4*r+1)+1 by omega, oo]

private noncomputable def Q : PowerSeries (ZMod 2) :=
  mk (fun n => (Nat.choose (4*n+1) n : ZMod 2))

private noncomputable def H : PowerSeries (ZMod 2) :=
  mk (fun n => if n = 0 then 1 else (Nat.choose (4*n-1) n : ZMod 2))

private theorem square_subst (f : PowerSeries (ZMod 2)) :
    f ^ 2 = f.subst (X ^ 2) := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
    2 (by decide) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm.trans (expand_apply 2 (by decide) f)

private theorem fourth_subst (f : PowerSeries (ZMod 2)) :
    f ^ 4 = f.subst (X ^ 4) := by
  rw [show 4 = 2*2 from rfl, pow_mul, square_subst (f ^ 2), square_subst f,
    subst_comp_subst_apply (.X_pow (by decide)) (.X_pow (by decide)),
    subst_pow (.X_pow (by decide)), subst_X (.X_pow (by decide)), ← pow_mul]

private theorem Q_equation : Q = 1 + X * Q ^ 4 := by
  rw [fourth_subst]
  ext n
  cases n with
  | zero => simp [Q]
  | succ n =>
    rw [map_add, coeff_one, if_neg (by omega : n+1 ≠ 0), zero_add, coeff_succ_X_mul,
      coeff_subst_X_pow (by decide : 4 ≠ 0)]
    simp only [Q, coeff_mk, Algebra.algebraMap_self]
    have hn : n = 4*(n/4) ∨ n = 4*(n/4)+1 ∨ n = 4*(n/4)+2 ∨ n = 4*(n/4)+3 := by omega
    rcases hn with hn | hn | hn | hn
    · have hd : 4 ∣ n := ⟨n/4, hn⟩
      rw [if_pos hd, hn]
      simpa using q_one (n/4)
    · have hd : ¬4 ∣ n := by omega
      rw [if_neg hd, hn, show 4*(n/4)+1+1 = 2*(2*(n/4)+1) by omega]
      exact q_even _ (by omega)
    · have hd : ¬4 ∣ n := by omega
      rw [if_neg hd, hn]
      simpa [Nat.add_assoc] using q_three (n/4)
    · have hd : ¬4 ∣ n := by omega
      rw [if_neg hd, hn, show 4*(n/4)+3+1 = 2*(2*(n/4)+2) by omega]
      exact q_even _ (by omega)

private theorem H_equation : H = H ^ 2 + X * Q ^ 2 := by
  rw [square_subst H, square_subst Q]
  ext n
  rw [map_add, coeff_subst_X_pow (by decide : 2 ≠ 0)]
  rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, hr⟩
  · rw [show r+r = 2*r by omega, if_pos (dvd_mul_right 2 r)]
    by_cases hr : r = 0
    · simp [hr, H]
    · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr
      have hx : coeff (2*r) (X * Q.subst ((X : PowerSeries (ZMod 2))^2)) = 0 := by
        rw [show 2*r = (2*s+1)+1 by omega, coeff_succ_X_mul,
          coeff_subst_X_pow (by decide : 2 ≠ 0), if_neg (by omega : ¬2 ∣ 2*s+1)]
      rw [hx, add_zero]
      simpa [H, hr, show 2*r ≠ 0 by omega] using h_even r (by omega)
  · rw [hr, if_neg (by omega : ¬2 ∣ 2*r+1), zero_add, coeff_succ_X_mul,
      coeff_subst_X_pow (by decide : 2 ≠ 0), if_pos (dvd_mul_right 2 r)]
    simpa [H, Q, show 2*r+1 ≠ 0 by omega] using h_odd r

private theorem Q_eq_reciprocal : Q = reciprocal := by
  let U := 1 - X * (Q ^ 3 + Q ^ 2 * reciprocal + Q * reciprocal ^ 2 + reciprocal ^ 3)
  have hu : IsUnit U := by
    rw [isUnit_iff_constantCoeff]
    simp [U]
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  dsimp [U]
  linear_combination Q_equation - reciprocal_equation

private theorem reduced_eq_H : reduced = H := by
  have hh : H = H ^ 2 + X * reciprocal ^ 2 := by
    rw [← Q_eq_reciprocal]
    exact H_equation
  have hu : IsUnit (1 - reduced - H) := by
    rw [isUnit_iff_constantCoeff]
    simp [reduced_constant, H]
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  linear_combination reduced_quadratic - hh

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    mk (fun n => if n = 0 then 1 else (Nat.choose (4 * n - 1) n : ZMod 2)) :=
  reduced_eq_H

theorem a_zero : a 0 = 1 := by
  calc
    a 0 = coeff 0 generatingSeries := (coeff_mk 0 a).symm
    _ = constantCoeff generatingSeries := congrFun coeff_zero_eq_constantCoeff _
    _ = 1 := generating_equation.1

theorem hanna_conjecture (n : ℕ) (hn : 0 < n) :
    a n % 2 = (Nat.choose (4 * n - 1) n : ℤ) % 2 := by
  have he := congrArg (coeff n) mod_two_identity
  simp only [coeff_map, generatingSeries, coeff_mk, if_neg (by omega : n ≠ 0)] at he
  apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mp
  simpa using he

#print axioms generating_equation
#print axioms generating_unique
#print axioms lucas_recursion_q
#print axioms mod_two_identity
#print axioms a_zero
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.AbsoluteReciprocalCubeParity
