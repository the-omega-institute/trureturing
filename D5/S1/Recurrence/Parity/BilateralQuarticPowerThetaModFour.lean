/- GID: D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bilateral quartic contraction and paired square powers give Hanna A379204. -/

import D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Int.Interval

open PowerSeries

namespace D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour

variable {R : Type*} [CommRing R]

private noncomputable def term (A : PowerSeries R) (n : ℤ) : PowerSeries R :=
  if 0 ≤ n then A ^ n.toNat * (A ^ n.toNat + 4) ^ (n.toNat + 1)
  else if n = -1 then 0
  else A ^ ((n.natAbs - 1) ^ 2 - 1) *
    invOfUnit (1 + 4 * A ^ n.natAbs) 1 ^ (n.natAbs - 1)

/-- The index -1 contributes A⁻¹ in the Laurent equation. Its contribution is
absorbed into the isolated X after multiplication by X*A, so this term is zero.
All other terms are ordinary formal power series. -/
noncomputable def bilateralTerm (A : PowerSeries ℤ) (n : ℤ) : PowerSeries ℤ := term A n

private def window (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ) - 2) N

private def Agree (d : ℕ) (F G : PowerSeries R) : Prop :=
  ∀ n < d, coeff n F = coeff n G

private theorem agree_iff (d : ℕ) (F G : PowerSeries R) :
    Agree d F G ↔ (X : PowerSeries R) ^ d ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_refl (d : ℕ) (F : PowerSeries R) : Agree d F F := by
  intro n hn; rfl

private theorem agree_add {d : ℕ} {F G H K : PowerSeries R}
    (h : Agree d F G) (h' : Agree d H K) : Agree d (F + H) (G + K) := by
  intro n hn
  simp only [map_add, h n hn, h' n hn]

private theorem agree_mul {d : ℕ} {F G H K : PowerSeries R}
    (h : Agree d F G) (h' : Agree d H K) : Agree d (F * H) (G * K) := by
  apply (agree_iff _ _ _).mpr
  have h1 := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) H
  have h2 := dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h') G
  convert dvd_add h1 h2 using 1
  ring

private theorem agree_pow {d : ℕ} {F G : PowerSeries R}
    (h : Agree d F G) (k : ℕ) : Agree d (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans
    (sub_dvd_pow_sub_pow F G k))

private theorem agree_inv {d : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    (h : Agree d F G) : Agree d (invOfUnit F 1) (invOfUnit G 1) := by
  have hFi := invOfUnit_mul F 1 hF
  have hGi := mul_invOfUnit G 1 hG
  have he : invOfUnit F 1 - invOfUnit G 1 =
      -(invOfUnit F 1 * (F - G) * invOfUnit G 1) := by
    linear_combination invOfUnit G 1 * hFi - invOfUnit F 1 * hGi
  apply (agree_iff _ _ _).mpr
  rw [he]
  exact dvd_neg.mpr (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h) _) _)

private theorem denominator_zero (F : PowerSeries R) (hF : constantCoeff F = 0)
    (r : ℕ) (hr : r ≠ 0) : constantCoeff (1 + 4 * F ^ r) = 1 := by
  simp [hF, zero_pow hr]

private theorem term_agree {d : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0)
    (h : Agree d F G) (n : ℤ) : Agree d (term F n) (term G n) := by
  unfold term
  split_ifs with hn h1
  · exact agree_mul (agree_pow h _) (agree_pow (agree_add (agree_pow h _)
      (agree_refl _ _)) _)
  · exact agree_refl _ _
  · have hr : n.natAbs ≠ 0 := by omega
    exact agree_mul (agree_pow h _) (agree_pow (agree_inv
      (denominator_zero F hF _ hr) (denominator_zero G hG _ hr)
      (agree_add (agree_refl _ _) (agree_mul (agree_refl _ _) (agree_pow h _)))) _)

private noncomputable def step (F : PowerSeries R) : PowerSeries R :=
  mk fun N => coeff N (X + X * F * ∑ n ∈ window N, term F n)

private theorem step_zero (F : PowerSeries R) : constantCoeff (step F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [step]

private theorem step_agree {d : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0)
    (h : Agree d F G) : Agree (d + 1) (step F) (step G) := by
  intro N hN
  simp only [step, coeff_mk, map_add]
  congr 1
  rw [mul_assoc, mul_assoc]
  cases N with
  | zero => simp
  | succ N =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul]
    apply agree_mul h ?_ N (by omega)
    intro i hi
    simp only [map_sum]
    exact Finset.sum_congr rfl fun n _ => term_agree hF hG h n i hi

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 0
  | d + 1 => step (approximation d)

private theorem approximation_zero (d : ℕ) :
    constantCoeff (approximation (R := R) d) = 0 := by
  cases d with
  | zero => simp [approximation]
  | succ d => exact step_zero _

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation (R := R) d) (approximation e) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e => exact step_agree (approximation_zero d) (approximation_zero e) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) : Agree d generatingSeries (approximation d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_zero : constantCoeff generatingSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
    coeff_zero_eq_constantCoeff, approximation_zero]

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext n
  exact (generating_agree (n + 2) n (by omega)).trans
    (step_agree generating_zero (approximation_zero (n + 1))
      (generating_agree (n + 1)) n (by omega)).symm

/-- Coefficientwise reading of the Laurent identity after multiplication by X*A.
The displayed finite window contains every term that can contribute at degree N. -/
theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧ ∀ N, coeff N generatingSeries =
      coeff N (X + X * generatingSeries *
        ∑ n ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm generatingSeries n) := by
  refine ⟨generating_zero, ?_, ?_⟩
  · have h := congrArg (coeff 1) generating_fixed
    simpa [step, mul_assoc, generating_zero] using h
  · intro N
    simpa only [step, coeff_mk, window, bilateralTerm] using
      congrArg (coeff N) generating_fixed

private theorem fixed_unique {F G : PowerSeries R}
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0)
    (eF : F = step F) (eG : G = step G) : F = G := by
  have h : ∀ d, Agree d F G := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← eF, ← eG] using step_agree hF hG ih
  ext n
  exact h (n + 1) n (by omega)

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (hB : ∀ N, coeff N B = coeff N (X + X * B *
      ∑ n ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm B n)) :
    B = generatingSeries := by
  apply fixed_unique h0 generating_zero ?_ generating_fixed
  ext N
  simpa only [step, coeff_mk, window, bilateralTerm] using hB N

private theorem term_order (F : PowerSeries R) (h0 : constantCoeff F = 0) (n : ℤ) :
    X ^ (if 0 ≤ n then n.toNat else (n.natAbs - 1) ^ 2 - 1) ∣ term F n := by
  unfold term
  split_ifs with hn h1
  · exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h0) _) _
  · exact dvd_zero _
  · exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h0) _) _

private theorem outside_order (N : ℕ) (n : ℤ) (hn : n ∉ window N) :
    N < if 0 ≤ n then n.toNat else (n.natAbs - 1) ^ 2 - 1 := by
  simp only [window, Finset.mem_Icc] at hn
  split_ifs with h0
  · omega
  · have ha : N + 2 < n.natAbs := by omega
    have hs : n.natAbs - 1 ≤ (n.natAbs - 1) ^ 2 := by
      simpa only [pow_two] using Nat.le_mul_self (n.natAbs - 1)
    omega

theorem bilateralTerm_coeff_eq_zero (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (N : ℕ) (n : ℤ)
    (hN : (N < if 0 ≤ n then n.toNat else (n.natAbs - 1) ^ 2 - 1) ∨
      n ∉ Finset.Icc (-(N : ℤ) - 2) N) :
    coeff N (bilateralTerm A n) = 0 :=
  X_pow_dvd_iff.mp (term_order A h0 n) N (hN.elim id (outside_order N n))

private theorem map_inv {S : Type*} [CommRing S] (f : R →+* S)
    (F : PowerSeries R) (hF : constantCoeff F = 1) :
    (invOfUnit F 1).map f = invOfUnit (F.map f) 1 := by
  have h1 := congrArg (PowerSeries.map f) (invOfUnit_mul F 1 hF)
  simp only [map_mul, map_one] at h1
  have h2 := mul_invOfUnit (F.map f) 1 (by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hF, map_one]
    rfl)
  calc
    (invOfUnit F 1).map f =
        (invOfUnit F 1).map f * (F.map f * invOfUnit (F.map f) 1) := by rw [h2, mul_one]
    _ = invOfUnit (F.map f) 1 := by rw [← mul_assoc, h1, one_mul]

private theorem map_term {S : Type*} [CommRing S] (f : R →+* S)
    (F : PowerSeries R) (hF : constantCoeff F = 0) (n : ℤ) :
    (term F n).map f = term (F.map f) n := by
  unfold term
  split_ifs with hn h1
  · simp only [map_mul, map_pow, map_add, map_ofNat]
  · exact map_zero _
  · rw [map_mul, map_pow, map_pow,
      map_inv f _ (denominator_zero F hF _ (by omega))]
    simp only [map_add, map_one, map_mul, map_ofNat, map_pow]

private theorem map_step {S : Type*} [CommRing S] (f : R →+* S)
    (F : PowerSeries R) (hF : constantCoeff F = 0) :
    (step F).map f = step (F.map f) := by
  ext N
  simp only [coeff_map, step, coeff_mk]
  rw [← coeff_map]
  simp only [map_add, map_mul, map_X, map_sum, map_term f F hF]

private theorem sum_window {S : Type*} [AddCommMonoid S] (f : ℤ → S)
    (h : f (-1) = 0) (N : ℕ) :
    ∑ n ∈ window N, f n = ∑ m ∈ Finset.range (N + 1), (f m + f (-(m : ℤ) - 2)) := by
  induction N with
  | zero =>
    have hw : window 0 = {-2, -1, 0} := by
      ext n
      simp only [window, Nat.cast_zero, neg_zero, zero_sub, Finset.mem_Icc,
        Finset.mem_insert, Finset.mem_singleton]
      omega
    simp [hw, h, add_comm]
  | succ N ih =>
    have hw : window (N + 1) = insert (-(N : ℤ) - 3) (insert ((N : ℤ) + 1) (window N)) := by
      ext n
      simp only [window, Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have hl : -(N : ℤ) - 3 ∉ insert ((N : ℤ) + 1) (window N) := by
      simp only [Finset.mem_insert, window, Finset.mem_Icc]
      omega
    have hr : (N : ℤ) + 1 ∉ window N := by simp [window]
    rw [hw, Finset.sum_insert hl, Finset.sum_insert hr, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, show -((N : ℤ) + 1) - 2 = -(N : ℤ) - 3 by ring]
    ac_rfl

private theorem four_zero : (4 : PowerSeries (ZMod 4)) = 0 := by
  rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]

private theorem inv_one : invOfUnit (1 : PowerSeries R) 1 = 1 := by
  simpa using invOfUnit_mul (1 : PowerSeries R) 1 (by simp)

private theorem positive_collapse (F : PowerSeries (ZMod 4)) (m : ℕ) :
    F * term F m = F ^ ((m + 1) ^ 2) := by
  simp only [term, Int.natCast_nonneg, if_true, Int.toNat_natCast, four_zero, add_zero]
  calc
    F * (F ^ m * (F ^ m) ^ (m + 1)) = F ^ (1 + m + m * (m + 1)) := by
      simp only [pow_add, pow_one, pow_mul]
      ring
    _ = F ^ ((m + 1) ^ 2) := by congr 1; ring

private theorem negative_collapse (F : PowerSeries (ZMod 4)) (m : ℕ) :
    F * term F (-(m : ℤ) - 2) = F ^ ((m + 1) ^ 2) := by
  have hn : ¬ 0 ≤ -(m : ℤ) - 2 := by omega
  have h1 : -(m : ℤ) - 2 ≠ -1 := by omega
  have ha : (-(m : ℤ) - 2).natAbs = m + 2 := by omega
  have hp : 1 ≤ (m + 1) ^ 2 := by nlinarith
  simp only [term, if_neg hn, if_neg h1, ha, four_zero, zero_mul, add_zero,
    inv_one, one_pow, mul_one, ← pow_succ']
  congr 1

private theorem paired_collapse (F : PowerSeries (ZMod 4)) (N : ℕ) :
    F * ∑ n ∈ window N, term F n =
      2 * ∑ m ∈ Finset.range (N + 1), F ^ ((m + 1) ^ 2) := by
  rw [Finset.mul_sum, sum_window (fun n => F * term F n) (by simp [term])]
  simp only [positive_collapse, negative_collapse, ← two_mul, ← Finset.mul_sum]

private theorem reduced_step (F : PowerSeries (ZMod 4)) (N : ℕ) :
    coeff N (step F) = coeff N (X + X *
      (2 * ∑ m ∈ Finset.range (N + 1), F ^ ((m + 1) ^ 2))) := by
  simp only [step, coeff_mk, mul_assoc, paired_collapse]

private theorem mapped_fixed (S : Type*) [CommRing S] :
    generatingSeries.map (Int.castRingHom S) = step (generatingSeries.map (Int.castRingHom S)) :=
  (congrArg (PowerSeries.map (Int.castRingHom S)) generating_fixed).trans
    (map_step _ _ generating_zero)

private theorem map_four_two (F : PowerSeries ℤ) :
    (F.map (Int.castRingHom (ZMod 4))).map
      (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) = F.map (Int.castRingHom (ZMod 2)) := by
  ext n
  simp only [coeff_map, Int.coe_castRingHom, map_intCast]

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) = X := by
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 by decide, map_zero]
  ext N
  have he := (congrArg (coeff N) (mapped_fixed (ZMod 4))).trans
    (reduced_step _ N)
  have hh := congrArg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) he
  simp only [← coeff_map] at hh
  rw [map_four_two] at hh
  simpa only [map_add, map_mul, map_X, map_ofNat, htwo, zero_mul, mul_zero, add_zero] using hh

private theorem double_map_eq (F G : PowerSeries ℤ)
    (h : F.map (Int.castRingHom (ZMod 2)) = G.map (Int.castRingHom (ZMod 2))) :
    2 * F.map (Int.castRingHom (ZMod 4)) = 2 * G.map (Int.castRingHom (ZMod 4)) := by
  ext n
  have he := congrArg (coeff n) h
  simp only [coeff_map, Int.coe_castRingHom] at he
  have hi := (ZMod.intCast_eq_intCast_iff' (coeff n F) (coeff n G) 2).mp he
  have hm : (2 * coeff n F) % 4 = (2 * coeff n G) % 4 := by omega
  have hc := (ZMod.intCast_eq_intCast_iff' (2 * coeff n F) (2 * coeff n G) 4).mpr hm
  simpa only [← map_ofNat C 2, coeff_C_mul, coeff_map, Int.coe_castRingHom,
    Int.cast_mul, Int.cast_ofNat] using hc

private theorem weighted_square_sum (N : ℕ) :
    2 * ∑ m ∈ Finset.range (N + 1),
        (generatingSeries.map (Int.castRingHom (ZMod 4))) ^ ((m + 1) ^ 2) =
      2 * ∑ m ∈ Finset.range (N + 1), (X : PowerSeries (ZMod 4)) ^ ((m + 1) ^ 2) := by
  have hd := double_map_eq
    (∑ m ∈ Finset.range (N + 1), generatingSeries ^ ((m + 1) ^ 2))
    (∑ m ∈ Finset.range (N + 1), (X : PowerSeries ℤ) ^ ((m + 1) ^ 2))
    (by simp only [map_sum, map_pow, mod_two_identity, map_X])
  simpa only [map_sum, map_pow, map_X] using hd

private theorem square_sum_coeff (N n : ℕ) (hn : n ≤ N) :
    coeff n (∑ m ∈ Finset.range (N + 1), (X : PowerSeries (ZMod 4)) ^ ((m + 1) ^ 2)) =
      if n = 0 then 0 else if IsSquare n then 1 else 0 := by
  classical
  rw [map_sum]
  by_cases h0 : n = 0
  · subst n
    simp only [if_true]
    apply Finset.sum_eq_zero
    intro m hm
    rw [coeff_X_pow, if_neg (Ne.symm (Nat.ne_of_gt (pow_pos (Nat.succ_pos m) 2)))]
  · rw [if_neg h0]
    by_cases hs : IsSquare n
    · rw [if_pos hs]
      obtain ⟨j, hj⟩ := hs
      have hj0 : 1 ≤ j := by
        by_contra h
        have : j = 0 := by omega
        simp [this] at hj
        exact h0 hj
      have hjn : j - 1 ∈ Finset.range (N + 1) := by
        simp only [Finset.mem_range]
        have hjn : j ≤ n := by rw [hj]; exact Nat.le_mul_self j
        omega
      rw [Finset.sum_eq_single (j - 1)]
      · rw [coeff_X_pow, if_pos (by rw [Nat.sub_add_cancel hj0]; nlinarith)]
      · intro m hm hmj
        rw [coeff_X_pow, if_neg]
        intro he
        have : m + 1 = j := by nlinarith
        omega
      · exact fun h => (h hjn).elim
    · rw [if_neg hs]
      apply Finset.sum_eq_zero
      intro m hm
      rw [coeff_X_pow, if_neg]
      intro he
      exact hs ⟨m + 1, by nlinarith⟩

private theorem theta_truncation (N n : ℕ) (hn : n ≤ N) :
    coeff n (1 + 2 * ∑ m ∈ Finset.range (N + 1),
      (X : PowerSeries (ZMod 4)) ^ ((m + 1) ^ 2)) =
        coeff n (ThetaSelfCompositionModFour.thetaSeries.map (Int.castRingHom (ZMod 4))) := by
  classical
  rw [map_add, show (2 : PowerSeries (ZMod 4)) = C 2 from (map_ofNat C 2).symm,
    coeff_C_mul, square_sum_coeff N n hn, coeff_map, ThetaSelfCompositionModFour.coeff_thetaSeries]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases hs : IsSquare n <;> simp [h0, hs, coeff_one]

theorem mod_four_identity : generatingSeries.map (Int.castRingHom (ZMod 4)) =
    X * ThetaSelfCompositionModFour.thetaSeries.map (Int.castRingHom (ZMod 4)) := by
  ext n
  have he := (congrArg (coeff n) (mapped_fixed (ZMod 4))).trans (reduced_step _ n)
  rw [weighted_square_sum] at he
  rw [show X + X * (2 * ∑ m ∈ Finset.range (n + 1),
      (X : PowerSeries (ZMod 4)) ^ ((m + 1) ^ 2)) =
      X * (1 + 2 * ∑ m ∈ Finset.range (n + 1),
        (X : PowerSeries (ZMod 4)) ^ ((m + 1) ^ 2)) by ring] at he
  rw [he]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul]
    exact theta_truncation (n + 1) n (by omega)

private theorem shifted_square (m : ℕ) :
    (m ≠ 0 ∧ IsSquare m) ↔ ∃ k : ℕ, 1 < k ∧ m + 1 = (k - 1) ^ 2 + 1 := by
  constructor
  · rintro ⟨hm, j, hj⟩
    have hj0 : 0 < j := by
      by_contra h
      have : j = 0 := by omega
      simp [this] at hj
      exact hm hj
    refine ⟨j + 1, by omega, ?_⟩
    rw [Nat.add_sub_cancel]
    nlinarith
  · rintro ⟨k, hk, he⟩
    have hp : 0 < (k - 1) ^ 2 := pow_pos (by omega : 0 < k - 1) _
    refine ⟨by omega, ⟨k - 1, ?_⟩⟩
    nlinarith

/-- The remainder-two characterization holds from index one. The remainder-zero
characterization excludes index one, whose coefficient is one. -/
theorem hanna_conjecture_mod_four (n : ℕ) (hn : 1 ≤ n) :
    (a n % 4 = 2 ↔ ∃ k : ℕ, 1 < k ∧ n = (k - 1) ^ 2 + 1) ∧
    (a n % 4 = 0 ↔ 1 < n ∧ ¬ ∃ k : ℕ, 1 < k ∧ n = (k - 1) ^ 2 + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [← shifted_square]
  have hc := congrArg (coeff (m + 1)) mod_four_identity
  simp only [coeff_succ_X_mul, coeff_map, generatingSeries, coeff_mk,
    ThetaSelfCompositionModFour.coeff_thetaSeries, Int.coe_castRingHom] at hc
  by_cases h0 : m = 0
  · rw [if_pos h0] at hc
    have ha : a (m + 1) % 4 = 1 := (ZMod.intCast_eq_intCast_iff' _ 1 4).mp hc
    simp only [h0, zero_add] at ha
    simp [h0, ha]
  · rw [if_neg h0] at hc
    have hm : 1 < m + 1 := by omega
    by_cases hs : IsSquare m
    · rw [if_pos hs] at hc
      have ha : a (m + 1) % 4 = 2 := (ZMod.intCast_eq_intCast_iff' _ 2 4).mp hc
      simp [h0, hs, hm, ha]
    · rw [if_neg hs] at hc
      have ha : a (m + 1) % 4 = 0 := (ZMod.intCast_eq_intCast_iff' _ 0 4).mp hc
      simp [h0, hs, hm, ha]

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) : Even (a n) := by
  have hc := hanna_conjecture_mod_four n (by omega)
  by_cases hs : ∃ k : ℕ, 1 < k ∧ n = (k - 1) ^ 2 + 1
  · have ha := hc.1.mpr hs
    rw [even_iff_two_dvd, Int.dvd_iff_emod_eq_zero]
    omega
  · have ha := hc.2.mpr ⟨hn, hs⟩
    rw [even_iff_two_dvd, Int.dvd_iff_emod_eq_zero]
    omega

#print axioms generating_equation
#print axioms generating_unique
#print axioms bilateralTerm_coeff_eq_zero
#print axioms mod_two_identity
#print axioms mod_four_identity
#print axioms hanna_conjecture_mod_four
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour
