/- GID: D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/BilateralThetaReversionModSixteen
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bilateral theta contraction gives support and Hanna's coefficient congruences. -/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Int.Interval

open PowerSeries
namespace D5.S1.Recurrence.Parity.BilateralThetaReversionModSixteen

variable {R : Type*} [CommRing R]

private noncomputable def term (F : PowerSeries R) (j : ℤ) : PowerSeries R :=
  (-X) ^ (j.natAbs ^ 2) * F ^ ((j - 1).natAbs ^ 2)

noncomputable def bilateralTerm (F : PowerSeries ℤ) (j : ℤ) : PowerSeries ℤ :=
  (-X) ^ (j.natAbs ^ 2) * F ^ ((j - 1).natAbs ^ 2)

private def window (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

private noncomputable def tail (F : PowerSeries R) : PowerSeries R :=
  mk fun N => ∑ j ∈ ((window N).erase 0).erase 1, coeff N (term F j)

private noncomputable def step (F : PowerSeries R) : PowerSeries R := 2 * X - tail F

private def Agree (d : ℕ) (F G : PowerSeries R) : Prop :=
  ∀ m < d, coeff m F = coeff m G

private theorem agree_iff (d : ℕ) (F G : PowerSeries R) :
    Agree d F G ↔ (X : PowerSeries R) ^ d ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem term_agree {d : ℕ} {F G : PowerSeries R}
    (h : Agree d F G) {j : ℤ} (hj : j ≠ 0) :
    Agree (d + 1) (term F j) (term G j) := by
  have hp : j.natAbs ^ 2 ≠ 0 := pow_ne_zero _ (Int.natAbs_ne_zero.mpr hj)
  have hx : (X : PowerSeries R) ∣ (-X : PowerSeries R) ^ (j.natAbs ^ 2) := by
    apply X_dvd_iff.mpr
    simp only [map_pow, map_neg, constantCoeff_X, neg_zero]
    exact zero_pow hp
  have hq := ((agree_iff _ _ _).mp h).trans
    (sub_dvd_pow_sub_pow F G ((j - 1).natAbs ^ 2))
  apply (agree_iff _ _ _).mpr
  simpa only [pow_succ', term, mul_sub] using mul_dvd_mul hx hq

private theorem step_agree {d : ℕ} {F G : PowerSeries R} (h : Agree d F G) :
    Agree (d + 1) (step F) (step G) := by
  intro m hm
  simp only [step, map_sub, tail, coeff_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact term_agree h (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 m hm

private theorem step_zero (F : PowerSeries R) : constantCoeff (step F) = 0 := by
  simp [step, tail, window]

private theorem fixed_unique {F G : PowerSeries R} (hF : F = step F) (hG : G = step G) :
    F = G := by
  have ha : ∀ d, Agree d F G := by
    intro d
    induction d with
    | zero => intro m hm; omega
    | succ d ih => simpa only [← hF, ← hG] using step_agree ih
  ext m
  exact ha (m + 1) m (by omega)

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 0
  | d + 1 => step (approximation d)

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation (R := R) d) (approximation e) := by
  induction d generalizing e with
  | zero => intro m hm; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e => exact step_agree (ih (by omega))

noncomputable def c (m : ℕ) : ℤ := coeff m (approximation (m + 1))

noncomputable def a (n : ℕ) : ℤ := c (4 * n - 3)

noncomputable def generatingSeries : PowerSeries ℤ := mk c

private theorem generating_agree (d : ℕ) : Agree d generatingSeries (approximation d) := by
  intro m hm
  simpa only [generatingSeries, coeff_mk, c] using
    approximation_stable (R := ℤ) (by omega : m + 1 ≤ d) m (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext m
  exact (generating_agree (m + 2) m (by omega)).trans
    (step_agree (generating_agree (m + 1)) m (by omega)).symm

private theorem term_zero (F : PowerSeries R) : term F 0 = F := by simp [term]
private theorem term_one (F : PowerSeries R) : term F 1 = -X := by simp [term]
private theorem term_two (F : PowerSeries R) : term F 2 = X ^ 4 * F := by
  norm_num [term]
  ring

private theorem window_isolation (F : PowerSeries R) (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ window N, coeff N (term F j)) =
      coeff N F - coeff N X + coeff N (tail F) := by
  have h0 : (0 : ℤ) ∈ window N := by simp [window]
  have h1 : (1 : ℤ) ∈ (window N).erase 0 := by simp [window]; omega
  have e0 := Finset.sum_erase_add (window N) (fun j => coeff N (term F j)) h0
  have e1 := Finset.sum_erase_add ((window N).erase 0)
    (fun j => coeff N (term F j)) h1
  simp only [term_zero, term_one, map_neg] at e0 e1
  simp only [tail, coeff_mk]
  rw [← e0, ← e1]
  ring

private theorem equation_iff (F : PowerSeries R) :
    (constantCoeff F = 0 ∧ ∀ N, coeff N (X : PowerSeries R) =
      ∑ j ∈ window N, coeff N (term F j)) ↔ F = step F := by
  constructor
  · rintro ⟨h0, hF⟩
    ext N
    by_cases hN : N = 0
    · subst N
      simpa only [coeff_zero_eq_constantCoeff, step_zero] using h0
    · have he := hF N
      rw [window_isolation F N (by omega)] at he
      simp only [step, map_sub, show (2 : PowerSeries R) = C 2 from (map_ofNat C 2).symm,
        coeff_C_mul]
      linear_combination -he
  · intro hF
    have h0 : constantCoeff F = 0 := by rw [hF, step_zero]
    refine ⟨h0, fun N => ?_⟩
    by_cases hN : N = 0
    · subst N
      simp [window, term_zero, h0]
    · rw [window_isolation F N (by omega)]
      have he := congrArg (coeff N) hF
      simp only [step, map_sub, show (2 : PowerSeries R) = C 2 from (map_ofNat C 2).symm,
        coeff_C_mul] at he
      linear_combination -he

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    ∀ N, coeff N (X : PowerSeries ℤ) =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, coeff N (bilateralTerm generatingSeries j) :=
  (equation_iff generatingSeries).mpr generating_fixed

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (hB : ∀ N, coeff N (X : PowerSeries ℤ) =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, coeff N (bilateralTerm B j)) :
    B = generatingSeries :=
  fixed_unique ((equation_iff B).mp ⟨h0, hB⟩) generating_fixed

private theorem term_order (F : PowerSeries R) (h0 : constantCoeff F = 0) (j : ℤ) :
    (X : PowerSeries R) ^ (j.natAbs ^ 2 + (j - 1).natAbs ^ 2) ∣ term F j := by
  have hX : (X : PowerSeries R) ∣ -X := dvd_neg.mpr dvd_rfl
  simpa only [pow_add, term] using mul_dvd_mul
    (pow_dvd_pow_of_dvd hX (j.natAbs ^ 2))
    (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h0) ((j - 1).natAbs ^ 2))

theorem bilateralTerm_coeff_eq_zero (F : PowerSeries ℤ) (h0 : constantCoeff F = 0)
    (N : ℕ) (j : ℤ) (hN : N < j.natAbs ^ 2 + (j - 1).natAbs ^ 2) :
    coeff N (bilateralTerm F j) = 0 :=
  X_pow_dvd_iff.mp (term_order F h0 j) N hN

private def Supported (r : ℕ) (F : PowerSeries R) : Prop :=
  ∀ m, m % 4 ≠ r % 4 → coeff m F = 0

private theorem supported_mul {r s : ℕ} {F G : PowerSeries R}
    (hF : Supported r F) (hG : Supported s G) : Supported (r + s) (F * G) := by
  intro m hm
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have he := Finset.mem_antidiagonal.mp hij
  by_cases hi : i % 4 = r % 4
  · have hj : j % 4 ≠ s % 4 := by
      intro hj
      apply hm
      rw [← he, Nat.add_mod, hi, hj, ← Nat.add_mod]
    rw [hG j hj, mul_zero]
  · rw [hF i hi, zero_mul]

private theorem supported_pow {r : ℕ} {F : PowerSeries R} (hF : Supported r F) (k : ℕ) :
    Supported (r * k) (F ^ k) := by
  induction k with
  | zero =>
    intro m hm
    simp only [pow_zero, coeff_one]
    split_ifs with h
    · subst m; simp at hm
    · rfl
  | succ k ih => simpa only [pow_succ, Nat.mul_succ] using supported_mul ih hF

private theorem square_residues (j : ℤ) :
    (j.natAbs ^ 2 + (j - 1).natAbs ^ 2) % 4 = 1 := by
  apply Int.ofNat_inj.mp
  push_cast
  rw [sq_abs, sq_abs]
  have hr : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases hr with h | h | h | h <;>
    norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h]

private theorem supported_term {F : PowerSeries R} (hF : Supported 1 F) (j : ℤ) :
    Supported 1 (term F j) := by
  have hx : Supported 1 (-X : PowerSeries R) := by
    intro m hm
    have h : m ≠ 1 := by intro h; subst m; simp at hm
    simp only [map_neg, coeff_X, if_neg h, neg_zero]
  have ht := supported_mul (supported_pow hx (j.natAbs ^ 2))
    (supported_pow hF ((j - 1).natAbs ^ 2))
  simpa only [Nat.one_mul, Supported, square_residues, Nat.one_mod, term] using ht

private theorem supported_step {F : PowerSeries R} (hF : Supported 1 F) :
    Supported 1 (step F) := by
  intro m hm
  have h : m ≠ 1 := by intro h; subst m; simp at hm
  simp only [step, map_sub, show (2 : PowerSeries R) = C 2 from (map_ofNat C 2).symm,
    coeff_C_mul, coeff_X, if_neg h, mul_zero, tail, coeff_mk]
  have ht : (∑ j ∈ ((window m).erase 0).erase 1, coeff m (term F j)) = 0 :=
    Finset.sum_eq_zero fun j _ => supported_term hF j m hm
  rw [ht, sub_self]

theorem support_one_mod_four (m : ℕ) (hm : m % 4 ≠ 1) : c m = 0 := by
  have ha : ∀ d, Supported 1 (approximation (R := ℤ) d) := by
    intro d
    induction d with
    | zero => intro m hm; simp [approximation]
    | succ d ih => exact supported_step ih
  exact ha (m + 1) m hm

private theorem outside_window_order (N : ℕ) (j : ℤ) (h : j ∉ window N) :
    N < j.natAbs ^ 2 := by
  have ha : N < j.natAbs := by
    simp only [window, Finset.mem_Icc] at h
    omega
  nlinarith

private theorem higher_exponent (j : ℤ) (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2) :
    4 ≤ (j - 1).natAbs ^ 2 := by
  have h : 2 ≤ (j - 1).natAbs := by omega
  nlinarith

private theorem tail_of_fourth_zero (F : PowerSeries R) (hF : F ^ 4 = 0) :
    tail F = X ^ 4 * F := by
  ext N
  simp only [tail, coeff_mk]
  rw [Finset.sum_eq_single 2, term_two]
  · intro j hj h2
    have h1 := (Finset.mem_erase.mp hj).1
    have h0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    rw [term, pow_eq_zero_of_le (higher_exponent j h0 h1 h2) hF, mul_zero, map_zero]
  · intro h2
    have h : (2 : ℤ) ∉ window N := by simpa using h2
    have hN : N < 4 := by simpa using outside_window_order N 2 h
    rw [term_two, coeff_X_pow_mul', if_neg (by omega)]

private theorem map_step {S : Type*} [CommRing S] (f : R →+* S) (F : PowerSeries R) :
    (step F).map f = step (F.map f) := by
  simp only [step, map_sub, map_mul, map_ofNat, map_X]
  congr 1
  ext N
  simp only [coeff_map, tail, coeff_mk, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← coeff_map]
  simp only [term, map_mul, map_pow, map_neg, map_X]

private noncomputable def linearCandidate : PowerSeries R :=
  2 * X * invOfUnit (1 + X ^ 4) 1

private theorem linear_equation :
    linearCandidate (R := R) + X ^ 4 * linearCandidate = 2 * X := by
  have hi := invOfUnit_mul (1 + (X : PowerSeries R) ^ 4) 1 (by simp)
  dsimp only [linearCandidate]
  linear_combination 2 * X * hi

private theorem candidate_fourth_zero : linearCandidate (R := ZMod 16) ^ 4 = 0 := by
  have h16 : (16 : PowerSeries (ZMod 16)) = 0 := by
    rw [← map_ofNat C 16, show (16 : ZMod 16) = 0 by decide, map_zero]
  calc
    linearCandidate (R := ZMod 16) ^ 4 =
        16 * (X * invOfUnit (1 + X ^ 4) 1) ^ 4 := by dsimp [linearCandidate]; ring
    _ = 0 := by rw [h16, zero_mul]

theorem mod_sixteen_identity :
    generatingSeries.map (Int.castRingHom (ZMod 16)) =
      2 * X * invOfUnit (1 + X ^ 4) 1 := by
  apply fixed_unique
  · rw [← map_step, ← generating_fixed]
  · change linearCandidate = step linearCandidate
    rw [step, tail_of_fourth_zero _ candidate_fourth_zero]
    linear_combination linear_equation (R := ZMod 16)

private theorem candidate_coeff (k : ℕ) :
    coeff (4 * k + 1) (linearCandidate (R := R)) = 2 * (-1) ^ k := by
  induction k with
  | zero =>
    have he := congrArg (coeff 1) (linear_equation (R := R))
    simpa [coeff_X_pow_mul', show (2 : PowerSeries R) = C 2 from (map_ofNat C 2).symm,
      coeff_C_mul, coeff_X] using he
  | succ k ih =>
    have he := congrArg (coeff (4 * (k + 1) + 1)) (linear_equation (R := R))
    have h4 : 4 ≤ 4 * (k + 1) + 1 := by omega
    have hd : 4 * (k + 1) + 1 - 4 = 4 * k + 1 := by omega
    have h1 : 4 * (k + 1) + 1 ≠ 1 := by omega
    simp only [map_add, coeff_X_pow_mul', if_pos h4, hd, ih,
      show (2 : PowerSeries R) = C 2 from (map_ofNat C 2).symm,
      coeff_C_mul, coeff_X, if_neg h1, mul_zero] at he
    rw [pow_succ]
    linear_combination he

private theorem coefficient_mod_sixteen (k : ℕ) :
    c (4 * k + 1) % 16 = (2 * (-1 : ℤ) ^ k) % 16 := by
  have he := congrArg (coeff (4 * k + 1)) mod_sixteen_identity
  change (coeff (4 * k + 1)) (generatingSeries.map (Int.castRingHom (ZMod 16))) =
    coeff (4 * k + 1) linearCandidate at he
  rw [candidate_coeff] at he
  simp only [coeff_map, generatingSeries, coeff_mk, Int.coe_castRingHom] at he
  apply (ZMod.intCast_eq_intCast_iff' _ _ 16).mp
  simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_neg, Int.cast_one] using he

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) : a n % 4 = 2 := by
  have hi : 4 * n - 3 = 4 * (n - 1) + 1 := by omega
  have he := coefficient_mod_sixteen (n - 1)
  change c (4 * n - 3) % 4 = 2
  rw [hi]
  rcases neg_one_pow_eq_or ℤ (n - 1) with h | h <;> rw [h] at he <;>
    norm_num at he <;> omega

theorem hanna_conjecture_mod_eight (n : ℕ) (hn : 1 ≤ n) :
    a (2 * n - 1) % 8 = 2 ∧ a (2 * n) % 8 = 6 := by
  have ho := coefficient_mod_sixteen (2 * (n - 1))
  have he := coefficient_mod_sixteen (2 * (n - 1) + 1)
  norm_num [pow_add, pow_mul] at ho he
  have hio : 4 * (2 * n - 1) - 3 = 4 * (2 * (n - 1)) + 1 := by omega
  have hie : 4 * (2 * n) - 3 = 4 * (2 * (n - 1) + 1) + 1 := by omega
  simp only [a, hio, hie]
  constructor <;> omega

#print axioms generating_equation
#print axioms generating_unique
#print axioms bilateralTerm_coeff_eq_zero
#print axioms support_one_mod_four
#print axioms mod_sixteen_identity
#print axioms hanna_conjecture
#print axioms hanna_conjecture_mod_eight

end D5.S1.Recurrence.Parity.BilateralThetaReversionModSixteen
