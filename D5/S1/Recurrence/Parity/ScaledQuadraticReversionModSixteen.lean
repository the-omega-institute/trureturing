/- GID: D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Contracting normalization and alternating dyadic support correct Hanna A396844. -/

import D5.S1.Recurrence.Invariants.AlternatingDyadicReversionModFour

open PowerSeries
namespace D5.S1.Recurrence.Parity.ScaledQuadraticReversionModSixteen

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_refl (d : ℕ) (f : PowerSeries R) : Agree d f f := fun _ _ => rfl

private theorem agree_mono {d e : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (he : e ≤ d) : Agree e f g :=
  fun n hn => h n (lt_of_lt_of_le hn he)

private theorem agree_add {d : ℕ} {f g u v : PowerSeries R}
    (h : Agree d f g) (h' : Agree d u v) : Agree d (f + u) (g + v) := by
  intro n hn; simp only [map_add, h n hn, h' n hn]

private theorem agree_sub {d : ℕ} {f g u v : PowerSeries R}
    (h : Agree d f g) (h' : Agree d u v) : Agree d (f - u) (g - v) := by
  intro n hn; simp only [map_sub, h n hn, h' n hn]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private theorem agree_mul {d : ℕ} {f g u v : PowerSeries R}
    (h : Agree d f g) (h' : Agree d u v) : Agree d (f * u) (g * v) := by
  apply (agree_iff _ _ _).mpr
  have h1 := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) u
  have h2 := dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h') g
  convert dvd_add h1 h2 using 1
  ring

private theorem agree_X {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (X * f) (X * g) := by
  intro n hn
  cases n with
  | zero => simp
  | succ n => simpa using h n (by omega)

private theorem pow_low {f : PowerSeries R} (h : constantCoeff f = 0)
    {n k : ℕ} (hn : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h) k) n hn

private theorem agree_subst {d : ℕ} {f g u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (ho : Agree d f g) (hi : Agree d u v) :
    Agree d (f.subst u) (g.subst v) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [ho k hk, agree_pow hi k n hn]
  · rw [pow_low hu (by omega : n < k), pow_low hv (by omega : n < k),
      smul_zero, smul_zero]

private noncomputable def unitPart (c : PowerSeries R) : PowerSeries R := 1 + X * c
private noncomputable def factor (c : PowerSeries R) : PowerSeries R :=
  unitPart c * (1 - 4 * X * unitPart c)
private noncomputable def argument (c : PowerSeries R) : PowerSeries R := X ^ 2 * factor c
private noncomputable def step (c : PowerSeries R) : PowerSeries R :=
  4 * unitPart c ^ 2 - X * (factor c ^ 2 * c.subst (argument c))

private theorem argument_zero (c : PowerSeries R) : constantCoeff (argument c) = 0 := by
  simp [argument]

private theorem unitPart_agree {d : ℕ} {c e : PowerSeries R} (h : Agree d c e) :
    Agree (d + 1) (unitPart c) (unitPart e) := agree_add (agree_refl _ _) (agree_X h)

private theorem factor_agree {d : ℕ} {c e : PowerSeries R} (h : Agree d c e) :
    Agree (d + 1) (factor c) (factor e) := by
  exact agree_mul (unitPart_agree h) (agree_sub (agree_refl _ _)
    (agree_mul (agree_refl _ _) (unitPart_agree h)))

private theorem step_agree {d : ℕ} {c e : PowerSeries R} (h : Agree d c e) :
    Agree (d + 1) (step c) (step e) := by
  have hf := factor_agree h
  have ha : Agree d (argument c) (argument e) :=
    agree_mul (agree_refl _ _) (agree_mono hf (by omega))
  exact agree_sub (agree_mul (agree_refl _ _) (agree_pow (unitPart_agree h) 2))
    (agree_X (agree_mul (agree_pow (agree_mono hf (by omega)) 2)
      (agree_subst (argument_zero c) (argument_zero e) h ha)))

private theorem fixed_unique {c e : PowerSeries R} (hc : c = step c) (he : e = step e) :
    c = e := by
  have hall : ∀ d, Agree d c e := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← hc, ← he] using step_agree ih
  ext n
  exact hall (n + 1) n (by omega)

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => step (approximation n)

private theorem approximation_stable {d k : ℕ} (h : d ≤ k) :
    Agree d (approximation (R := R) d) (approximation k) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => exact step_agree (ih (by omega))

private noncomputable def solution : PowerSeries R :=
  mk fun n => coeff n (approximation (n + 1))

private theorem solution_agree (d : ℕ) :
    Agree d (solution (R := R)) (approximation d) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approximation_stable (R := R) (by omega : n + 1 ≤ d) n (by omega)

private theorem solution_fixed : solution (R := R) = step solution := by
  ext n
  have h1 := solution_agree (R := R) (n + 2) n (by omega)
  have h2 := step_agree (solution_agree (R := R) (n + 1)) n (by omega)
  exact h1.trans h2.symm

private noncomputable def assemble (c : PowerSeries R) : PowerSeries R := X + X ^ 2 * c

private theorem equation_iff (c : PowerSeries R) :
    (assemble c).subst (X * assemble c - 4 * X * assemble c ^ 2) = X ^ 2 ↔
      c = step c := by
  have hi : X * assemble c - 4 * X * assemble c ^ 2 = argument c := by
    simp only [assemble, argument, factor, unitPart]
    ring
  have hs : HasSubst (argument c) := .of_constantCoeff_zero (argument_zero c)
  rw [hi, assemble, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs]
  have hid : argument c + argument c ^ 2 * c.subst (argument c) =
      X ^ 2 + X ^ 3 * (c - step c) := by
    simp only [step, argument, factor, unitPart]
    ring
  rw [hid, add_eq_left]
  constructor
  · intro h
    have he : X * (X * (X * (c - step c))) = X * (X * (X * 0)) := by
      simpa [pow_succ, mul_assoc] using h
    exact sub_eq_zero.mp (X_mul_cancel (X_mul_cancel (X_mul_cancel he)))
  · intro h; rw [sub_eq_zero.mpr h, mul_zero]

noncomputable def generatingSeries : PowerSeries ℤ := assemble solution
noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries.subst (X * generatingSeries - 4 * X * generatingSeries ^ 2) = X ^ 2 := by
  refine ⟨by simp [generatingSeries, assemble], ?_, (equation_iff _).mpr solution_fixed⟩
  simp [generatingSeries, assemble, pow_two, mul_assoc]

private theorem exists_assemble (B : PowerSeries R) (h0 : constantCoeff B = 0)
    (h1 : coeff 1 B = 1) : ∃ c, B = assemble c := by
  have hd : X ^ 2 ∣ B - X := by
    apply X_pow_dvd_iff.mpr
    intro n hn
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp [h0, h1]
  obtain ⟨c, hc⟩ := hd
  exact ⟨c, by dsimp [assemble]; linear_combination hc⟩

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (h1 : coeff 1 B = 1)
    (hB : B.subst (X * B - 4 * X * B ^ 2) = X ^ 2) : B = generatingSeries := by
  obtain ⟨c, rfl⟩ := exists_assemble B h0 h1
  exact congrArg assemble (fixed_unique ((equation_iff c).mp hB) solution_fixed)

private theorem map_step {S : Type*} [CommRing S] (hom : R →+* S) (c : PowerSeries R) :
    (step c).map hom = step (c.map hom) := by
  have hm : (c.subst (argument c)).map hom =
      (c.map hom).subst ((argument c).map hom) :=
    map_subst (.of_constantCoeff_zero (argument_zero c)) c
  simp only [argument, factor, unitPart, map_mul, map_pow, map_X, map_sub, map_one,
    map_add, map_ofNat] at hm
  simp only [step, factor, unitPart, argument, map_sub, map_mul, map_pow, map_X,
    map_add, map_one, map_ofNat]
  simp only [PowerSeries.map] at hm ⊢
  rw [hm]

theorem mod_four_identity : generatingSeries.map (Int.castRingHom (ZMod 4)) = X := by
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
    rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]
  have hf : (solution (R := ℤ)).map (Int.castRingHom (ZMod 4)) = step
      ((solution (R := ℤ)).map (Int.castRingHom (ZMod 4))) := by
    rw [← map_step, ← solution_fixed]
  have hz : (0 : PowerSeries (ZMod 4)) = step 0 := by
    simp [step, unitPart, h4, ← coe_substAlgHom (.of_constantCoeff_zero (argument_zero 0))]
  have he := fixed_unique hf hz
  simp [generatingSeries, assemble, he]

private theorem scalar_pow_congr (s : PowerSeries R) {u v : PowerSeries R}
    (h : s * u = s * v) (k : ℕ) : s * u ^ k = s * v ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      s * u ^ (k + 1) = (s * u ^ k) * u := by ring
      _ = (s * v ^ k) * u := by rw [ih]
      _ = (s * u) * v ^ k := by ring
      _ = (s * v) * v ^ k := by rw [h]
      _ = s * v ^ (k + 1) := by ring

-- An annihilated difference of arguments remains annihilated after substitution.
private theorem scalar_subst_congr (s : R) (F : PowerSeries R) {u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : C s * u = C s * v) : C s * F.subst u = C s * F.subst v := by
  have hsU : HasSubst u := .of_constantCoeff_zero hu
  have hsV : HasSubst v := .of_constantCoeff_zero hv
  have hCU : (C s).subst u = C s := subst_C s
  have hCV : (C s).subst v = C s := subst_C s
  suffices he : (C s * F).subst u = (C s * F).subst v by
    simpa only [subst_mul hsU, subst_mul hsV, hCU, hCV] using he
  ext n
  rw [coeff_subst' hsU, coeff_subst' hsV]
  apply finsum_congr
  intro k
  have hk := congrArg (coeff n) (scalar_pow_congr (C s) h k)
  simp only [coeff_C_mul] at hk ⊢
  simp only [smul_eq_mul]
  linear_combination coeff k F * hk

private noncomputable def dyadic : PowerSeries ℤ :=
  D5.S1.Recurrence.Invariants.AlternatingDyadicReversionModFour.inverseSeries

private theorem dyadic_equation : dyadic + dyadic.subst (X ^ 2) = X :=
  D5.S1.Recurrence.Invariants.AlternatingDyadicReversionModFour.inverse_equation

private theorem dyadic_zero : constantCoeff dyadic = 0 := by
  have h := congrArg constantCoeff dyadic_equation
  rw [map_add, constantCoeff_subst_X_pow (by omega : 2 ≠ 0), constantCoeff_X] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  omega

private noncomputable def shiftedDyadic : PowerSeries ℤ := mk fun n => coeff (n + 1) dyadic

private theorem shift_dyadic : X * shiftedDyadic = dyadic := by
  ext n
  cases n with
  | zero => simpa using dyadic_zero.symm
  | succ n => simp [shiftedDyadic]

private theorem shifted_equation : shiftedDyadic + X * shiftedDyadic.subst (X ^ 2) = 1 := by
  apply X_mul_cancel
  have hs : HasSubst ((X : PowerSeries ℤ) ^ 2) := .X_pow (by omega)
  have he := dyadic_equation
  rw [← shift_dyadic, subst_mul hs, subst_X hs] at he
  linear_combination he

private theorem sixteen_zero : (16 : PowerSeries (ZMod 16)) = 0 := by
  rw [← map_ofNat C 16, show (16 : ZMod 16) = 0 by decide, map_zero]

private theorem scaled_fixed (T : PowerSeries (ZMod 16))
    (hT : T + X * T.subst (X ^ 2) = 1) : 4 * T = step (4 * T) := by
  have hunit : 4 * unitPart (4 * T) = 4 := by
    dsimp [unitPart]
    linear_combination X * T * sixteen_zero
  have hfac : 4 * factor (4 * T) = 4 := by
    dsimp [factor]
    linear_combination hunit - X * unitPart (4 * T) ^ 2 * sixteen_zero
  have harg : 4 * argument (4 * T) = 4 * X ^ 2 := by
    dsimp [argument]
    linear_combination X ^ 2 * hfac
  have hsub : 4 * T.subst (argument (4 * T)) = 4 * T.subst (X ^ 2) := by
    have hc : (4 : PowerSeries (ZMod 16)) = C 4 := (map_ofNat C 4).symm
    rw [hc] at harg ⊢
    exact scalar_subst_congr 4 T (argument_zero _) (by simp) harg
  have hu2 : 4 * unitPart (4 * T) ^ 2 = 4 := by
    simpa only [one_pow, mul_one] using scalar_pow_congr (R := ZMod 16) 4
      (u := unitPart (4 * T)) (v := 1)
      (by simpa only [mul_one] using hunit) 2
  have hf2 : 4 * factor (4 * T) ^ 2 = 4 := by
    simpa only [one_pow, mul_one] using scalar_pow_congr (R := ZMod 16) 4
      (u := factor (4 * T)) (v := 1)
      (by simpa only [mul_one] using hfac) 2
  have hs : HasSubst (argument (4 * T)) := .of_constantCoeff_zero (argument_zero _)
  have hfour : (4 : PowerSeries (ZMod 16)).subst (argument (4 * T)) = 4 := by
    rw [← coe_substAlgHom hs]
    exact map_ofNat _ 4
  rw [step, subst_mul hs, hfour]
  linear_combination -hu2 + X * T.subst (argument (4 * T)) * hf2 + X * hsub + 4 * hT

private theorem generating_mod_sixteen :
    generatingSeries.map (Int.castRingHom (ZMod 16)) =
      X + 4 * X * dyadic.map (Int.castRingHom (ZMod 16)) := by
  let hom := Int.castRingHom (ZMod 16)
  let T := shiftedDyadic.map hom
  have hm : (shiftedDyadic.subst (X ^ 2)).map hom = T.subst (X ^ 2) := by
    have he : (shiftedDyadic.subst (X ^ 2)).map hom =
        T.subst (((X : PowerSeries ℤ) ^ 2).map hom) := map_subst (.X_pow (by omega)) _
    simpa using he
  have hT : T + X * T.subst (X ^ 2) = 1 := by
    have he := congrArg (PowerSeries.map hom) shifted_equation
    simp only [map_add, map_mul, map_X, map_one] at he
    simp only [PowerSeries.map] at he
    rw [hm] at he
    exact he
  have hf : (solution (R := ℤ)).map hom = step ((solution (R := ℤ)).map hom) := by
    rw [← map_step, ← solution_fixed]
  have hc := fixed_unique hf (scaled_fixed T hT)
  have hd : X * T = dyadic.map hom := by
    simpa only [map_mul, map_X] using congrArg (PowerSeries.map hom) shift_dyadic
  change (assemble (solution (R := ℤ))).map hom = X + 4 * X * dyadic.map hom
  simp only [assemble, map_add, map_mul, map_pow, map_X, hc]
  rw [← hd]
  ring

private theorem dyadic_coeff_power (k : ℕ) : coeff (2 ^ k) dyadic = (-1 : ℤ) ^ k := by
  induction k with
  | zero =>
    have he := congrArg (coeff 1) dyadic_equation
    simpa using he
  | succ k ih =>
    have hp : 0 < (2 : ℕ) ^ k := pow_pos (by omega) _
    have hn : (2 : ℕ) ^ (k + 1) ≠ 1 := by rw [pow_succ]; omega
    have hd : 2 ∣ (2 : ℕ) ^ (k + 1) := by rw [pow_succ]; exact dvd_mul_left _ _
    have he := congrArg (coeff (2 ^ (k + 1))) dyadic_equation
    simp only [map_add, coeff_subst_X_pow (by omega : 2 ≠ 0), if_pos hd,
      Algebra.algebraMap_self, RingHom.id_apply, coeff_X, if_neg hn] at he
    rw [pow_succ, Nat.mul_div_cancel _ (by omega), ih] at he
    rw [pow_succ]
    linear_combination he

private theorem dyadic_coeff_off (n : ℕ) (hn : ¬ ∃ k : ℕ, n = 2 ^ k) :
    coeff n dyadic = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n; simpa using dyadic_zero
    have h1 : n ≠ 1 := by rintro rfl; exact hn ⟨0, by simp⟩
    have he := congrArg (coeff n) dyadic_equation
    simp only [map_add, coeff_subst_X_pow (by omega : 2 ≠ 0),
      Algebra.algebraMap_self, RingHom.id_apply, coeff_X, if_neg h1] at he
    by_cases hd : 2 ∣ n
    · have hh : ¬ ∃ k : ℕ, n / 2 = 2 ^ k := by
        rintro ⟨k, hk⟩
        apply hn
        refine ⟨k + 1, ?_⟩
        rw [pow_succ, ← hk, Nat.div_mul_cancel hd]
      rw [if_pos hd, ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) hh, add_zero] at he
      exact he
    · simpa only [if_neg hd, add_zero] using he

private theorem coefficient_cast (m : ℕ) (hm : 0 < m) :
    (a (m + 1) : ZMod 16) = 4 * ((coeff m dyadic : ℤ) : ZMod 16) := by
  have he := congrArg (coeff (m + 1)) generating_mod_sixteen
  have hfour : (4 : PowerSeries (ZMod 16)) = C 4 := (map_ofNat C 4).symm
  simpa only [a, coeff_map, Int.coe_castRingHom, map_add, coeff_X,
    if_neg (by omega : m + 1 ≠ 1), zero_add, mul_assoc, hfour, coeff_C_mul,
    coeff_succ_X_mul] using he

private theorem residue_power (k : ℕ) :
    a (2 ^ k + 1) % 16 = if Even k then 4 else 12 := by
  have hc := coefficient_cast (2 ^ k) (pow_pos (by omega) _)
  rw [dyadic_coeff_power] at hc
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow] at hc
    simp only [Int.cast_one, mul_one] at hc
    rw [if_pos hk]
    exact (ZMod.intCast_eq_intCast_iff' (a (2 ^ k + 1)) 4 16).mp hc
  · rw [hk.neg_one_pow] at hc
    have hcast : (a (2 ^ k + 1) : ZMod 16) = (12 : ℤ) := by
      rw [hc]; decide
    rw [if_neg (by simpa using hk)]
    exact (ZMod.intCast_eq_intCast_iff' (a (2 ^ k + 1)) 12 16).mp hcast

private theorem residue_off (n : ℕ) (hn : 2 ≤ n) (hs : ¬ ∃ k : ℕ, n = 2 ^ k + 1) :
    a n % 16 = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hc := coefficient_cast m (by omega)
  have hm : ¬ ∃ k : ℕ, m = 2 ^ k := by
    rintro ⟨k, hk⟩; exact hs ⟨k, by omega⟩
  rw [dyadic_coeff_off m hm, Int.cast_zero, mul_zero] at hc
  exact (ZMod.intCast_eq_intCast_iff' (a (m + 1)) 0 16).mp hc

theorem mod_sixteen_classification (n : ℕ) (hn : 2 ≤ n) :
    (a n % 16 = 4 ↔ ∃ k : ℕ, Even k ∧ n = 2 ^ k + 1) ∧
    (a n % 16 = 12 ↔ ∃ k : ℕ, Odd k ∧ n = 2 ^ k + 1) ∧
    (16 ∣ a n ↔ ¬ ∃ k : ℕ, n = 2 ^ k + 1) := by
  have hi : ∀ j k : ℕ, (2 : ℕ) ^ j + 1 = 2 ^ k + 1 → j = k := by
    intro j k h
    exact Nat.pow_right_injective (by omega : 2 ≤ 2) (Nat.add_right_cancel h)
  by_cases hs : ∃ k : ℕ, n = 2 ^ k + 1
  · obtain ⟨k, rfl⟩ := hs
    have hev : (∃ j : ℕ, Even j ∧ 2 ^ k + 1 = 2 ^ j + 1) ↔ Even k := by
      constructor
      · rintro ⟨j, hj, he⟩; rwa [hi k j he]
      · intro hk; exact ⟨k, hk, rfl⟩
    have hod : (∃ j : ℕ, Odd j ∧ 2 ^ k + 1 = 2 ^ j + 1) ↔ Odd k := by
      constructor
      · rintro ⟨j, hj, he⟩; rwa [hi k j he]
      · intro hk; exact ⟨k, hk, rfl⟩
    rw [hev, hod, Int.dvd_iff_emod_eq_zero, residue_power]
    rcases Nat.even_or_odd k with hk | hk
    · simp [hk, show ¬ Odd k by simpa using hk]
    · simp [hk, show ¬ Even k by simpa using hk]
  · have hev : ¬ ∃ k : ℕ, Even k ∧ n = 2 ^ k + 1 := by
      rintro ⟨k, _, hk⟩; exact hs ⟨k, hk⟩
    have hod : ¬ ∃ k : ℕ, Odd k ∧ n = 2 ^ k + 1 := by
      rintro ⟨k, _, hk⟩; exact hs ⟨k, hk⟩
    simp [residue_off n hn hs, hev, hod, hs, Int.dvd_iff_emod_eq_zero]

def hannaClaim : Prop := ∀ n : ℕ, 8 < n →
  ((a n % 16 = 12 ↔ ∃ k : ℕ, n = 2 * 4 ^ k + 1) ∧
    (¬ (∃ k : ℕ, n = 2 * 4 ^ k + 1) → 16 ∣ a n))

theorem hanna_conjecture_false : ¬ hannaClaim := by
  intro h
  have hr : a 17 % 16 = 4 := (mod_sixteen_classification 17 (by omega)).1.mpr
    ⟨4, ⟨2, rfl⟩, by norm_num⟩
  have hc := h 17 (by omega)
  have hoff : ¬ ∃ k : ℕ, 17 = 2 * 4 ^ k + 1 := by
    rintro ⟨k, hk⟩
    have hp : (4 : ℕ) ^ k = 8 := by omega
    cases k with
    | zero => simp at hp
    | succ k =>
      rw [pow_succ] at hp
      have hq : (4 : ℕ) ^ k = 2 := by omega
      cases k with
      | zero => simp at hq
      | succ k => rw [pow_succ] at hq; omega
  have hz := Int.dvd_iff_emod_eq_zero.mp (hc.2 hoff)
  omega

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_four_identity
#print axioms mod_sixteen_classification
#print axioms hanna_conjecture_false

end D5.S1.Recurrence.Parity.ScaledQuadraticReversionModSixteen
