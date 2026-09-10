/- GID: D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral contraction and reflected elimination prove Hanna's A369083 parity. -/

import D5.S1.Recurrence.Parity.AbsoluteReciprocalCubeParity

open PowerSeries

namespace D5.S1.Recurrence.Parity.ReflectedQuadraticQuarterParity

private def Agree (n : ℕ) (F G : PowerSeries ℤ) : Prop :=
  ∀ i < n, coeff i F = coeff i G

private theorem agree_iff (n : ℕ) (F G : PowerSeries ℤ) :
    Agree n F G ↔ (X : PowerSeries ℤ) ^ n ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {F G : PowerSeries ℤ}
    (h : Agree n F G) (k : ℕ) : Agree n (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G k))

private theorem square_odd_even (F : PowerSeries ℤ) (n : ℕ) (hn : ¬ Even n) :
    2 ∣ coeff n (F ^ 2) := by
  let f := F.map (Int.castRingHom (ZMod 2))
  have hs : f ^ 2 = f.subst (X ^ 2) := by
    have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
      2 (by decide) (f := f)
    rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
    exact h.symm.trans (expand_apply 2 (by decide) f)
  have hz : coeff n (f ^ 2) = 0 := by
    rw [hs, coeff_subst_X_pow (by decide : 2 ≠ 0), if_neg]
    simpa only [even_iff_two_dvd] using hn
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff n (F ^ 2)) 2).mp
  simpa only [f, ← map_pow, coeff_map, Int.coe_castRingHom] using hz

private noncomputable def step (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => match n with
    | 0 => 1
    | k + 1 => if Even k then coeff k (F ^ 2) else 3 * (coeff k (F ^ 2) / 2))

private theorem step_constant (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  simp [step]

private theorem step_agree {n : ℕ} {F G : PowerSeries ℤ} (h : Agree n F G) :
    Agree (n + 1) (step F) (step G) := by
  intro i hi
  cases i with
  | zero => simp [step]
  | succ i => simp only [step, coeff_mk, agree_pow h 2 i (by omega)]

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree n (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero => intro i hi; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m => exact step_agree (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (n : ℕ) : Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree (generating_agree (i + 1)) i (by omega)).symm

private theorem step_equation (F : PowerSeries ℤ) :
    4 * (step F - 1) = X * (5 * F ^ 2 - (rescale (-1) F) ^ 2) := by
  ext n
  cases n with
  | zero => simp [step]
  | succ n =>
    rw [← map_pow]
    simp only [map_sub, coeff_succ_X_mul, coeff_rescale]
    simp only [show (4 : PowerSeries ℤ) = C 4 by simp,
      show (5 : PowerSeries ℤ) = C 5 by simp, coeff_C_mul, map_sub, coeff_one,
      if_neg (by omega : n + 1 ≠ 0), sub_zero, step, coeff_mk]
    by_cases hn : Even n
    · rw [if_pos hn, hn.neg_one_pow]
      ring
    · rw [if_neg hn, (Nat.not_even_iff_odd.mp hn).neg_one_pow]
      have hd := Int.ediv_mul_cancel (square_odd_even F n hn)
      linear_combination 6 * hd

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    4 * (generatingSeries - 1) =
      X * (5 * generatingSeries ^ 2 - (rescale (-1) generatingSeries) ^ 2) := by
  refine ⟨?_, ?_⟩
  · rw [generating_fixed]; exact step_constant _
  · conv_lhs => rw [generating_fixed]
    exact step_equation _

private theorem four_ne_zero : (4 : PowerSeries ℤ) ≠ 0 := by
  intro h
  rw [show (4 : PowerSeries ℤ) = C 4 by simp] at h
  have hc := congrArg constantCoeff h
  simp only [constantCoeff_C, map_zero] at hc
  norm_num at hc

theorem generating_unique (B : PowerSeries ℤ) (_h0 : constantCoeff B = 1)
    (hB : 4 * (B - 1) = X * (5 * B ^ 2 - (rescale (-1) B) ^ 2)) :
    B = generatingSeries := by
  have hf : B = step B := by
    have he := hB.trans (step_equation B).symm
    exact sub_left_inj.mp (mul_left_cancel₀ four_ne_zero he)
  have h : ∀ n, Agree n B generatingSeries := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      simpa only [← hf, ← generating_fixed] using step_agree ih
  ext i
  exact h (i + 1) i (by omega)

theorem reflection_linear : rescale (-1) generatingSeries =
    5 * generatingSeries - 4 - 6 * X * generatingSeries ^ 2 := by
  have h := generating_equation.2
  have hr := congrArg (rescale (-1 : ℤ)) h
  simp only [map_mul, map_sub, map_ofNat, map_one, map_pow, rescale_rescale,
    neg_mul_neg, one_mul, rescale_one, RingHom.id_apply] at hr
  rw [rescale_neg_one_X] at hr
  apply mul_left_cancel₀ four_ne_zero
  linear_combination hr - 5 * h

theorem quartic_equation :
    1 - 4 * X + (10 * X - 1) * generatingSeries -
      (5 * X + 12 * X ^ 2) * generatingSeries ^ 2 +
      15 * X ^ 2 * generatingSeries ^ 3 - 9 * X ^ 3 * generatingSeries ^ 4 = 0 := by
  have h := generating_equation.2
  rw [reflection_linear] at h
  apply mul_left_cancel₀ four_ne_zero
  linear_combination -h

theorem choose_shift (n : ℕ) :
    Nat.choose (4 * n + 3) (n + 1) = 3 * Nat.choose (4 * n + 3) n := by
  classical
  apply Classical.byContradiction
  intro h
  apply h
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < n + 1)
  rw [Nat.choose_succ_right_eq, show 4 * n + 3 - n = 3 * (n + 1) by omega]
  ring

private theorem map_abs (F : PowerSeries ℤ) :
    (AbsoluteReciprocalCubeParity.absSeries F).map (Int.castRingHom (ZMod 2)) =
      F.map (Int.castRingHom (ZMod 2)) := by
  ext n
  simp [coeff_map, AbsoluteReciprocalCubeParity.absSeries, ZMod.intCast_abs_mod_two]

private theorem two_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C (R := ZMod 2)) (CharTwo.two_eq_zero (R := ZMod 2))

private theorem reduced_product :
    generatingSeries.map (Int.castRingHom (ZMod 2)) *
      (1 + X * generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 3 = 1 := by
  let F := generatingSeries.map (Int.castRingHom (ZMod 2))
  have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) quartic_equation
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_X, map_zero] at h
  change F * (1 + X * F) ^ 3 = 1
  change 1 - 4 * X + (10 * X - 1) * F - (5 * X + 12 * X ^ 2) * F ^ 2 +
    15 * X ^ 2 * F ^ 3 - 9 * X ^ 3 * F ^ 4 = 0 at h
  linear_combination -h + (-X * F ^ 2 + 9 * X ^ 2 * F ^ 3 - 4 * X ^ 3 * F ^ 4 +
    5 * X * F - 2 * X - 6 * X ^ 2 * F ^ 2) * two_zero

theorem mod_two_identity :
    1 + X * generatingSeries.map (Int.castRingHom (ZMod 2)) =
      AbsoluteReciprocalCubeParity.generatingSeries.map (Int.castRingHom (ZMod 2)) := by
  let F := generatingSeries.map (Int.castRingHom (ZMod 2))
  let H := 1 + X * F
  let G := AbsoluteReciprocalCubeParity.generatingSeries.map (Int.castRingHom (ZMod 2))
  let J := (invOfUnit AbsoluteReciprocalCubeParity.generatingSeries 1).map
    (Int.castRingHom (ZMod 2))
  have hH0 : constantCoeff H = 1 := by simp [H]
  have hG0 : constantCoeff G = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [G, coeff_map,
      coeff_zero_eq_constantCoeff, AbsoluteReciprocalCubeParity.generating_equation.1]
  have hJG : J * G = 1 := by
    simpa only [J, G, map_mul, map_one] using
      congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
        (invOfUnit_mul AbsoluteReciprocalCubeParity.generatingSeries 1
          AbsoluteReciprocalCubeParity.generating_equation.1)
  have hG : G = 1 + X * J ^ 3 := by
    simpa only [G, J, map_add, map_one, map_mul, map_X, map_pow, map_abs] using
      congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
        AbsoluteReciprocalCubeParity.generating_equation.2
  have hHpoly : H ^ 4 - H ^ 3 = X := by
    have hp : F * H ^ 3 = 1 := reduced_product
    calc
      H ^ 4 - H ^ 3 = X * (F * H ^ 3) := by dsimp [H]; ring
      _ = X := by rw [hp, mul_one]
  have hGpoly : G ^ 4 - G ^ 3 = X := by
    calc
      G ^ 4 - G ^ 3 = (G - 1) * G ^ 3 := by ring
      _ = X * (J * G) ^ 3 := by rw [hG]; ring
      _ = X := by rw [hJG]; ring
  let U := H ^ 3 + H ^ 2 * G + H * G ^ 2 + G ^ 3 - (H ^ 2 + H * G + G ^ 2)
  have hu : IsUnit U := by
    rw [isUnit_iff_constantCoeff]
    norm_num [U, hH0, hG0]
  change H = G
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  dsimp [U]
  linear_combination hHpoly - hGpoly

theorem hanna_conjecture (n : ℕ) :
    a n % 2 = (Nat.choose (4 * n + 3) n : ℤ) % 2 := by
  have h := congrArg (coeff (n + 1))
    (mod_two_identity.trans AbsoluteReciprocalCubeParity.mod_two_identity)
  simp only [map_add, coeff_one, if_neg (by omega : n + 1 ≠ 0), zero_add,
    coeff_succ_X_mul, coeff_map, generatingSeries, coeff_mk] at h
  rw [show 4 * (n + 1) - 1 = 4 * n + 3 by omega, choose_shift] at h
  apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mp
  simpa [show (3 : ZMod 2) = 1 by decide] using h

#print axioms generating_equation
#print axioms generating_unique
#print axioms reflection_linear
#print axioms quartic_equation
#print axioms choose_shift
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.ReflectedQuadraticQuarterParity
