/- GID: D5/S1/Recurrence/Bilateral/HannaThetaFourModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Bilateral/HannaThetaFourModFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's A379764 theta-four generating function and mod-four conjectures are proved. -/

/-
Public declarations:
- theta4: source definition, proof_shape: bind-only; escape_witness: none.
- term: source definition, proof_shape: bind-only; escape_witness: none.
- IsGF: source definition, proof_shape: bind-only; escape_witness: none.
- claim: source conjecture, proof_shape: bind-only; escape_witness: none.
- result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18830; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19879
Direct frozen dependencies (declaration statement_id):
- D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.Agree (sha256:9f713507954544b157be5038ad405bd766f1eb9c6cb01d3292e162c2bfc27373).
- D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.map_inv (sha256:84254a37d7611374957fadbf596aab8f80ead28f1020c63db9c0f1261844a9e7).
- D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed (sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981).
- D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree (sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34).
- D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.agree_refl (sha256:a831bea32455484cd07e2e672ce1ed01616d79ba3122ef8bd420905e044c9439).
- D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.agree_mul (sha256:1d28a4b714c56dd8363e940666ff1ed72f6ce84dcfe1eac85ee9335658470932).
- D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.agree_add (sha256:6bf8ffefb42d0204fa72a8734aeba068be3b4a7977cb4d49ab54252f68b7d037).
- D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.agree_pow (sha256:74fa68ac755721aec072ceb443a8e891cac7522e2467f5bfb431a1c1f8a5c6a8).
- D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.agree_sub (sha256:7243862d9431dc23891ba2f12a25fcb418a219e248a5ba540c1534caba8c6ce7).
- D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.agree_inv (sha256:f603d720fc7dfefacc2d1b19ddf94cfe69428922103b55cd63afa3e83cb3bcce).
- D5/S1/Recurrence/Bilateral/BilateralProductModFour.ofSeries_inverse (sha256:6c9f94677b0c4cdb1baddca0a042a6a268121bc80d543b562f3b0b0d63f3a0de).
- D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_X (sha256:cb4bbeb74f9bb4de6a237dc609532d94ac61147a4a3cd321ca192132b9b26215).
Claims retain the issue's literal conventions; proofs reuse existing owners through private consumed adapters.
-/

import D5.S1.Recurrence.Parity.ScaledQuadraticReversionModSixteen
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Bilateral.BilateralProductModFour
import D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour

set_option autoImplicit false

namespace D5.S1.Recurrence.Bilateral.HannaThetaFourModFour

open PowerSeries

/-- `theta_4(x) = Sum_{n=-oo..+oo} (-x)^(n^2)`, coefficientwise. -/
noncomputable def theta4 : PowerSeries ℚ :=
  mk fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, if n ^ 2 = (N : ℤ) then (-1 : ℚ) ^ N else 0

/-- The summand `(4^n*A(x)^n - 4*A(x))^(n+1)` as a Laurent series (integer exponents). -/
noncomputable def term (A : PowerSeries ℚ) (n : ℤ) : LaurentSeries ℚ :=
  let B : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ A
  ((4 : LaurentSeries ℚ) ^ n * B ^ n - 4 * B) ^ (n + 1)

/-- OEIS A379764: "G.f. A(x) satisfies Sum_{n=-oo..+oo} (4^n*A(x)^n - 4*A(x))^(n+1) = 2*theta_4(x) =
2*Sum_{n=-oo..+oo} (-x)^(n^2)", offset 1, a(1) = 1. The bilateral sum is read coefficientwise through the
symmetric windows [-K, K], K > N. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    ∀ N K : ℕ, N + 1 ≤ K →
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (term A j).coeff (N : ℤ)) = 2 * coeff N theta4

/-- OEIS A379764 (P. D. Hanna), conjectures: "for n > 0, a(n) is odd iff n is a square" and "for n > 0,
a(n) == (-1)^(n-1) (mod 4) iff n is a square, otherwise a(n) is divisible by 4 if n is nonsquare." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 0 < n → ∃ m : ℤ, coeff n A = m ∧
      (Odd m ↔ IsSquare n) ∧
      (m ≡ (-1) ^ (n - 1) [ZMOD 4] ↔ IsSquare n) ∧ (¬ IsSquare n → (4 : ℤ) ∣ m)

end D5.S1.Recurrence.Bilateral.HannaThetaFourModFour

open PowerSeries
open private Agree agree_refl agree_add agree_mul agree_pow agree_inv from
  D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour
open D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour (map_inv)
open private agree_sub from D5.S1.Recurrence.Parity.ScaledQuadraticReversionModSixteen
open D5.S1.Recurrence.Bilateral.BilateralProductModFour

namespace D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
variable {R S : Type*} [CommRing R] [CommRing S]

private noncomputable def source : PowerSeries R :=
  mk fun n => if IsSquare (n + 1) then (-1 : R) ^ n else 0

private noncomputable def den (F : PowerSeries R) (k : ℕ) : PowerSeries R :=
  1 - (4 * (X * F)) ^ (k + 3)

private noncomputable def rec (F : PowerSeries R) (k : ℕ) : PowerSeries R :=
  invOfUnit (den F k) 1

private noncomputable def pos (F : PowerSeries R) (k : ℕ) : PowerSeries R :=
  X ^ (k + 2) * ((-1) ^ (k + 3) * 4 ^ (k + 1) * F ^ (k + 3) *
    (1 - (4 * (X * F)) ^ (k + 1)) ^ (k + 3))

private noncomputable def neg (F : PowerSeries R) (k : ℕ) : PowerSeries R :=
  X ^ (k ^ 2 + 3 * k + 1) * (4 ^ (k ^ 2 + 3 * k) *
    F ^ ((k + 2) * (k + 1)) * rec F k ^ (k + 1))

private noncomputable def pair (F : PowerSeries R) (k : ℕ) := pos F k + neg F k

private noncomputable def tail (F : PowerSeries R) : PowerSeries R :=
  mk fun N => ∑ k ∈ Finset.range (N + 1), coeff N (pair F k)

private noncomputable def step (F : PowerSeries R) : PowerSeries R := source + 4 * tail F

private theorem den_const (F : PowerSeries R) (k : ℕ) : constantCoeff (den F k) = 1 := by
  simp [den]

private theorem agree_shift {d k : ℕ} {F G : PowerSeries R}
    (hk : 0 < k) (h : Agree d F G) : Agree (d + 1) (X ^ k * F) (X ^ k * G) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simpa only [Agree, D5.S1.Recurrence.Invariants.UnitReversionSquareParity.Agree,
    pow_succ', mul_assoc] using
    D5.S1.Recurrence.Invariants.UnitReversionSquareParity.agree_X
      (agree_mul (agree_refl d (X ^ l)) h)

private theorem pair_agree {d : ℕ} {F G : PowerSeries R} (h : Agree d F G) (k : ℕ) :
    Agree (d + 1) (pair F k) (pair G k) := by
  have hr := agree_refl (R := R) d
  have ht : Agree d (4 * (X * F)) (4 * (X * G)) :=
    agree_mul (hr 4) (agree_mul (hr X) h)
  apply agree_add
  · apply agree_shift (by omega : 0 < k + 2)
    exact agree_mul (agree_mul (hr _) (agree_pow h _))
      (agree_pow (agree_sub (hr 1) (agree_pow ht _)) _)
  · apply agree_shift (by omega : 0 < k ^ 2 + 3 * k + 1)
    apply agree_mul (agree_mul (hr _) (agree_pow h _))
    exact agree_pow (agree_inv (den_const F k) (den_const G k)
      (agree_sub (hr 1) (agree_pow ht _))) _

private theorem step_agree {d : ℕ} {F G : PowerSeries R} (h : Agree d F G) :
    Agree (d + 1) (step F) (step G) := by
  intro N hN
  have ht : coeff N (tail F) = coeff N (tail G) := by
    simp only [tail, coeff_mk]
    exact Finset.sum_congr rfl fun k _ => pair_agree h k N hN
  simp only [step, map_add,
    show (4 : PowerSeries R) = C 4 from (map_ofNat C 4).symm, coeff_C_mul, ht]

private theorem pair_order (F : PowerSeries R) (k : ℕ) :
    (X : PowerSeries R) ^ (k + 1) ∣ pair F k := by
  apply dvd_add
  · exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega : k + 1 ≤ k + 2)) _
  · exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by nlinarith : k + 1 ≤ k ^ 2 + 3 * k + 1)) _

private theorem step_const (F : PowerSeries R) : constantCoeff (step F) = 1 := by
  have ht : coeff 0 (tail F) = 0 := by
    simp only [tail, coeff_mk]
    exact Finset.sum_eq_zero fun k _ => X_pow_dvd_iff.mp (pair_order F k) 0 (by omega)
  simpa [step, source, ← coeff_zero_eq_constantCoeff, ht]

private theorem fixed_unique {F G : PowerSeries R} (hF : F = step F) (hG : G = step G) : F = G := by
  obtain ⟨f, hf0, hff, hu⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      (R := R) step (fun F _ => step_const F) (fun {_} {_ _} _ _ _ h => step_agree h)
  have f0 : constantCoeff F = 1 := by rw [hF, step_const]
  have g0 : constantCoeff G = 1 := by rw [hG, step_const]
  exact (hu F f0 hF).trans (hu G g0 hG).symm

private theorem approx_stable {d e : ℕ} (h : d ≤ e) :
    Agree d ((step^[d]) (1 : PowerSeries R)) ((step^[e]) (1 : PowerSeries R)) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      simpa only [Function.iterate_succ_apply'] using step_agree (ih (by omega))

private noncomputable def solution : PowerSeries ℤ := mk fun n => coeff n ((step^[n + 1]) (1 : PowerSeries ℤ))

private theorem solution_agree (d : ℕ) : Agree d solution ((step^[d]) (1 : PowerSeries ℤ)) := by
  intro n hn
  simpa only [solution, coeff_mk] using approx_stable (R := ℤ) (by omega : n + 1 ≤ d) n (by omega)

private theorem solution_fixed : solution = step solution := by
  ext n
  calc
    coeff n solution = coeff n ((step^[n + 2]) (1 : PowerSeries ℤ)) :=
      solution_agree (n + 2) n (by omega)
    _ = coeff n (step ((step^[n + 1]) (1 : PowerSeries ℤ))) := by
      rw [Function.iterate_succ_apply']
    _ = coeff n (step solution) :=
      (step_agree (solution_agree (n + 1)) n (by omega)).symm

private theorem solution_const : constantCoeff solution = 1 := by
  rw [solution_fixed, step_const]

private theorem map_rec (f : R →+* S) (F : PowerSeries R) (k : ℕ) :
    (rec F k).map f = rec (F.map f) k := by
  rw [rec, map_inv f _ (den_const F k)]
  simp only [den, map_sub, map_one, map_pow, map_mul, map_ofNat, map_X, rec]

private theorem map_step (f : R →+* S) (F : PowerSeries R) :
    (step F).map f = step (F.map f) := by
  classical
  have hs : (source : PowerSeries R).map f = source := by
    ext n
    simp only [source, coeff_mk, coeff_map]
    split_ifs <;> simp
  have ht : (tail F).map f = tail (F.map f) := by
    ext n
    simp only [tail, coeff_mk, coeff_map, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← coeff_map]
    simp only [pair, pos, neg, map_add, map_mul, map_pow, map_ofNat, map_neg, map_one,
      map_X, map_sub, map_rec]
  simp only [step, map_add, map_mul, map_ofNat, hs, ht]

private theorem solution_mod_four (n : ℕ) :
    coeff n solution ≡ (if IsSquare (n + 1) then (-1 : ℤ) ^ n else 0) [ZMOD 4] := by
  have he := congrArg (coeff n) solution_fixed
  simp only [step, map_add, source, coeff_mk,
    show (4 : PowerSeries ℤ) = C 4 from (map_ofNat C 4).symm, coeff_C_mul] at he
  rw [Int.modEq_iff_dvd]
  rw [he]
  exact ⟨-coeff n (tail solution), by ring⟩

end D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
namespace D5.S1.Recurrence.Bilateral.HannaThetaFourModFour

private theorem theta_coeff (N : ℕ) : coeff N theta4 =
    if N = 0 then 1 else if IsSquare N then 2 * (-1 : ℚ) ^ N else 0 := by
  classical
  simp only [theta4, coeff_mk]
  by_cases h0 : N = 0
  · subst N
    norm_num
  rw [ite_eq_right h0]
  by_cases hs : IsSquare N
  · obtain ⟨m, hm⟩ := hs
    have hm0 : 0 < m := by
      have hN : 0 < N := Nat.pos_of_ne_zero h0
      nlinarith
    have hmn : m ≤ N := by rw [hm]; exact Nat.le_mul_self m
    have hms : (m : ℤ) ^ 2 = (N : ℤ) := by exact_mod_cast (show m ^ 2 = N by nlinarith)
    have hmem : ({(m : ℤ), -(m : ℤ)} : Finset ℤ) ⊆ Finset.Icc (-(N : ℤ)) N := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp only [Finset.mem_Icc] <;> constructor <;> omega
    have he : (∑ j ∈ ({(m : ℤ), -(m : ℤ)} : Finset ℤ),
        if j ^ 2 = (N : ℤ) then (-1 : ℚ) ^ N else 0) =
        ∑ j ∈ Finset.Icc (-(N : ℤ)) N, if j ^ 2 = (N : ℤ) then (-1 : ℚ) ^ N else 0 := by
      apply Finset.sum_subset hmem
      intro j hj hnot
      rw [ite_eq_right]
      intro hjn
      have hjm : j = (m : ℤ) ∨ j = -(m : ℤ) := by
        exact (sq_eq_sq_iff_eq_or_eq_neg).mp (hjn.trans hms.symm)
      exact hnot (by simpa using hjm)
    rw [← he, ite_eq_left ⟨m, hm⟩]
    simp [hms, show (m : ℤ) ≠ -(m : ℤ) by omega, two_mul]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right]
    intro he
    apply hs
    refine ⟨j.natAbs, ?_⟩
    have ha : (j.natAbs : ℤ) ^ 2 = N := by simpa only [Int.natCast_natAbs, sq_abs] using he
    have hh : N = j.natAbs ^ 2 := by exact_mod_cast ha.symm
    simpa only [pow_two] using hh

end D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
namespace D5.S1.Recurrence.Bilateral.HannaThetaFourModFour

private theorem inc_coeff (F : PowerSeries ℚ) (N : ℕ) :
    ((HahnSeries.ofPowerSeries ℤ ℚ) F).coeff (N : ℤ) = coeff N F := by
  exact LaurentSeries.coeff_coe_powerSeries _ _

private theorem inc_rec (F : PowerSeries ℚ) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ ℚ) (rec F k) = (1 - (4 * (HahnSeries.ofPowerSeries ℤ ℚ) (X * F)) ^ (k + 3))⁻¹ := by
  change (HahnSeries.ofPowerSeries ℤ ℚ) (invOfUnit (den F k) 1) = _
  rw [PowerSeries.invOfUnit_eq' _ 1 (den_const F k)]
  simpa only [den, map_sub, map_one, map_pow, map_mul, map_ofNat] using
    ofSeries_inverse (den F k) (by rw [den_const]; exact one_ne_zero)

private theorem base_rewrite (A : PowerSeries ℚ) (j : ℤ) :
    term A j = ((4 * (HahnSeries.ofPowerSeries ℤ ℚ) A) ^ j - 4 * (HahnSeries.ofPowerSeries ℤ ℚ) A) ^ (j + 1) := by
  simp only [term, mul_zpow]

private theorem positive_factor {F : Type*} [Field F] (t : F) (k : ℕ) :
    (t ^ ((k + 2 : ℕ) : ℤ) - t) ^ (((k + 2 : ℕ) : ℤ) + 1) =
      (-1 : F) ^ (k + 3) * t ^ (k + 3) * (1 - t ^ (k + 1)) ^ (k + 3) := by
  have he : t ^ (k + 2) - t = ((-1 : F) * t) * (1 - t ^ (k + 1)) := by
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ]
    ring
  rw [show ((k + 2 : ℕ) : ℤ) + 1 = ((k + 3 : ℕ) : ℤ) by omega]
  simp only [zpow_natCast, he, mul_pow]

private theorem negative_factor {F : Type*} [Field F] (t : F) (ht : t ≠ 0) (k : ℕ) :
    (t ^ (-((k + 2 : ℕ) : ℤ)) - t) ^ (-((k + 2 : ℕ) : ℤ) + 1) =
      t ^ ((k + 2) * (k + 1)) * (1 - t ^ (k + 3))⁻¹ ^ (k + 1) := by
  have he : t ^ (-((k + 2 : ℕ) : ℤ)) - t =
      t ^ (-((k + 2 : ℕ) : ℤ)) * (1 - t ^ (k + 3)) := by
    rw [mul_sub, mul_one]
    congr 1
    rw [← zpow_natCast, ← zpow_add₀ ht]
    rw [show -((k + 2 : ℕ) : ℤ) + ((k + 3 : ℕ) : ℤ) = 1 by omega, zpow_one]
  rw [he, mul_zpow, ← zpow_mul]
  have ha : (-((k + 2 : ℕ) : ℤ)) * (-((k + 2 : ℕ) : ℤ) + 1) =
      (((k + 2) * (k + 1) : ℕ) : ℤ) := by push_cast; ring
  have hb : -((k + 2 : ℕ) : ℤ) + 1 = -((k + 1 : ℕ) : ℤ) := by omega
  rw [ha, hb, zpow_natCast, zpow_neg, zpow_natCast, inv_pow]

private theorem term_pos (F : PowerSeries ℚ) (k : ℕ) :
    term (X * F) ((k + 2 : ℕ) : ℤ) = (HahnSeries.ofPowerSeries ℤ ℚ) (16 * X * pos F k) := by
  rw [base_rewrite, positive_factor]
  simp only [pos, map_mul, map_pow, map_sub, map_one, map_neg, map_ofNat]
  rw [show k + 3 = k + 1 + 2 by omega, pow_add (4 : LaurentSeries ℚ),
    show k + 1 + 2 = k + 2 + 1 by omega]
  simp only [mul_pow, pow_succ ((HahnSeries.ofPowerSeries ℤ ℚ) X) (k + 2)]
  norm_num only
  ring

private theorem term_neg (F : PowerSeries ℚ) (hF : constantCoeff F = 1) (k : ℕ) :
    term (X * F) (-((k + 2 : ℕ) : ℤ)) = (HahnSeries.ofPowerSeries ℤ ℚ) (16 * X * neg F k) := by
  have hf : (HahnSeries.ofPowerSeries ℤ ℚ) (X * F) ≠ 0 := by
    intro he
    have hz : X * F = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
      (show (HahnSeries.ofPowerSeries ℤ ℚ) (X * F) = (HahnSeries.ofPowerSeries ℤ ℚ) 0 by simpa only [map_zero] using he)
    have hh := congrArg (coeff 1) hz
    simpa [hF] using hh
  have h4 : (4 : LaurentSeries ℚ) ≠ 0 := by
    intro hz
    have hps : (4 : PowerSeries ℚ) = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
        (show (HahnSeries.ofPowerSeries ℤ ℚ) 4 = (HahnSeries.ofPowerSeries ℤ ℚ) 0 by simpa only [map_ofNat, map_zero] using hz)
    have hc := congrArg constantCoeff hps
    norm_num only [map_ofNat, map_zero] at hc
  rw [base_rewrite, negative_factor _ (mul_ne_zero h4 hf)]
  simp only [neg, map_mul, map_pow, map_ofNat, inc_rec]

  have he : (k + 2) * (k + 1) = k ^ 2 + 3 * k + 2 := by ring
  simp only [mul_pow]
  rw [he,
    show k ^ 2 + 3 * k + 2 = (k ^ 2 + 3 * k) + 2 by omega,
    pow_add (4 : LaurentSeries ℚ),
    show (k ^ 2 + 3 * k) + 2 = (k ^ 2 + 3 * k + 1) + 1 by omega,
    pow_succ ((HahnSeries.ofPowerSeries ℤ ℚ) X) (k ^ 2 + 3 * k + 1)]
  norm_num only
  ring

private theorem term_zero (A : PowerSeries ℚ) : term A 0 = (HahnSeries.ofPowerSeries ℤ ℚ) (1 - 4 * A) := by
  simp only [term, zpow_zero, one_mul, zero_add, zpow_one, map_sub, map_one, map_mul, map_ofNat]

private theorem term_one (A : PowerSeries ℚ) : term A 1 = 0 := by simp [term]

private theorem term_minus_one (A : PowerSeries ℚ) : term A (-1) = 1 := by simp [term]

end D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
namespace D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
variable {R : Type*} [CommRing R]

private theorem symmetric_pair {T : Type*} [AddCommMonoid T] (f : ℤ → T) (K : ℕ) :
    (∑ j ∈ Finset.Icc (-(K : ℤ)) K, f j) =
      f 0 + ∑ k ∈ Finset.range K, (f (k + 1) + f (-(k : ℤ) - 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hs : Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) =
        insert (-(K : ℤ) - 1) (insert ((K : ℤ) + 1) (Finset.Icc (-(K : ℤ)) K)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    rw [hs, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih]
    rw [Finset.sum_range_succ]
    ac_rfl

private theorem window_split {T : Type*} [AddCommMonoid T] (f : ℤ → T) (K : ℕ) (hK : 1 ≤ K) :
    (∑ j ∈ Finset.Icc (-(K : ℤ)) K, f j) =
      f 0 + (f 1 + f (-1)) +
        ∑ k ∈ Finset.range (K - 1), (f (k + 2) + f (-(k : ℤ) - 2)) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  rw [symmetric_pair, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, zero_add, Nat.cast_zero, neg_zero,
    zero_sub,
    show ∀ k : ℕ, (k : ℤ) + 1 + 1 = k + 2 by intro k; omega,
    show ∀ k : ℕ, -((k : ℤ) + 1) - 1 = -k - 2 by intro k; omega]
  ac_rfl

private theorem tail_window (F : PowerSeries R) (N L : ℕ) (hNL : N + 1 ≤ L) :
    coeff N (tail F) = coeff N (∑ k ∈ Finset.range L, pair F k) := by
  simp only [tail, coeff_mk, map_sum]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    apply X_pow_dvd_iff.mp (pair_order F k) N
    simp only [Finset.mem_range] at hnot
    omega

private theorem window_eq (F : PowerSeries ℚ) (hF : constantCoeff F = 1)
    (N K : ℕ) (hNK : N + 1 ≤ K) :
    (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (term (X * F) j).coeff (N : ℤ)) =
      coeff N (2 - 4 * (X * F) + 16 * X * tail F) := by
  rw [window_split _ K (by omega), term_zero, term_one, term_minus_one,
    inc_coeff, HahnSeries.coeff_zero, zero_add]
  have hp : ∀ k : ℕ, (term (X * F) ((k : ℤ) + 2)).coeff (N : ℤ) +
      (term (X * F) (-(k : ℤ) - 2)).coeff (N : ℤ) =
      coeff N (16 * X * pair F k) := by
    intro k
    rw [show (k : ℤ) + 2 = ((k + 2 : ℕ) : ℤ) by omega,
      show -(k : ℤ) - 2 = -((k + 2 : ℕ) : ℤ) by omega,
      term_pos, term_neg F hF, inc_coeff, inc_coeff, ← map_add]
    congr 1
    dsimp [pair]
    ring
  simp_rw [hp]
  rw [← map_sum, ← Finset.mul_sum]
  have hc : (1 : LaurentSeries ℚ).coeff (N : ℤ) = coeff N (1 : PowerSeries ℚ) := by
    simpa only [map_one] using inc_coeff (1 : PowerSeries ℚ) N
  rw [hc]
  cases N with
  | zero => norm_num [map_ofNat]
  | succ N =>
    have ht := tail_window F N (K - 1) (by omega)
    simp only [map_sub, map_add, show (4 : PowerSeries ℚ) = C 4 from (map_ofNat C 4).symm,
      show (16 : PowerSeries ℚ) = C 16 from (map_ofNat C 16).symm,
      mul_assoc, coeff_C_mul, coeff_succ_X_mul]
    rw [← ht]
    simp only [coeff_one, show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm,
      coeff_C, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    ring

end D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
namespace D5.S1.Recurrence.Bilateral.HannaThetaFourModFour

private theorem theta_identity : 2 * theta4 = 2 - 4 * (X * (source : PowerSeries ℚ)) := by
  classical
  ext N
  cases N with
  | zero => norm_num [theta_coeff, coeff_zero_eq_constantCoeff, map_ofNat]
  | succ N =>
    simp only [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm,
      show (4 : PowerSeries ℚ) = C 4 from (map_ofNat C 4).symm,
      coeff_C_mul, map_sub, coeff_C, coeff_succ_X_mul, source, coeff_mk,
      theta_coeff, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      pow_succ]
    split_ifs <;> ring

private theorem gf_iff (F : PowerSeries ℚ) (hF : constantCoeff F = 1) :
    IsGF (X * F) ↔ F = step F := by
  have e (N K : ℕ) (hNK : N + 1 ≤ K) := window_eq F hF N K hNK
  constructor
  · rintro ⟨h0, h1, he⟩
    ext n
    have hh := he (n + 1) (n + 2) (by omega)
    rw [e _ _ (by omega)] at hh
    have ht := congrArg (coeff (n + 1)) theta_identity
    simp only [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm,
      show (4 : PowerSeries ℚ) = C 4 from (map_ofNat C 4).symm,
      show (16 : PowerSeries ℚ) = C 16 from (map_ofNat C 16).symm,
      map_add, map_sub, coeff_C_mul, mul_assoc, coeff_succ_X_mul, coeff_C,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, zero_sub] at hh ht
    simp only [step, map_add,
      show (4 : PowerSeries ℚ) = C 4 from (map_ofNat C 4).symm, coeff_C_mul]
    linear_combination -1 / 4 * hh - 1 / 4 * ht
  · intro he
    refine ⟨by simp, by simpa using hF, fun N K hNK => ?_⟩
    rw [e N K hNK]
    have ht : 2 - 4 * (X * F) + 16 * X * tail F = 2 * theta4 := by
      rw [theta_identity]
      dsimp only [step] at he
      linear_combination -4 * X * he
    rw [ht, show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, coeff_C_mul]

private theorem integral_gf : IsGF ((X * solution).map (Int.castRingHom ℚ)) := by
  rw [map_mul, map_X]
  apply (gf_iff _ (by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      solution_const, map_one])).mpr
  exact (congrArg (PowerSeries.map (Int.castRingHom ℚ)) solution_fixed).trans
    (map_step _ _)

private theorem gf_unique (A : PowerSeries ℚ) (hA : IsGF A) :
    A = (X * solution).map (Int.castRingHom ℚ) := by
  obtain ⟨h0, h1, hw⟩ := hA
  obtain ⟨F, hf⟩ := X_dvd_iff.mpr h0
  subst A
  have hF : constantCoeff F = 1 := by simpa using h1
  have he := (gf_iff F hF).mp ⟨by simp, h1, hw⟩
  rw [map_mul, map_X]
  congr 1
  apply fixed_unique he
  exact (congrArg (PowerSeries.map (Int.castRingHom ℚ)) solution_fixed).trans
    (map_step _ _)

private theorem arithmetic (m : ℤ) (n : ℕ)
    (h : m ≡ (if IsSquare n then (-1 : ℤ) ^ (n - 1) else 0) [ZMOD 4]) :
    (Odd m ↔ IsSquare n) ∧
    (m ≡ (-1) ^ (n - 1) [ZMOD 4] ↔ IsSquare n) ∧
    (¬ IsSquare n → (4 : ℤ) ∣ m) := by
  classical
  by_cases hs : IsSquare n
  · rw [ite_eq_left hs] at h
    have ho : Odd m := by
      rw [Int.odd_iff]
      change m % 4 = ((-1 : ℤ) ^ (n - 1)) % 4 at h
      rcases neg_one_pow_eq_or ℤ (n - 1) with hp | hp <;> rw [hp] at h <;>
        norm_num at h <;> omega
    exact ⟨iff_of_true ho hs, iff_of_true h hs, by simp [hs]⟩
  · rw [ite_eq_right hs] at h
    have hm : m % 4 = 0 := by exact h
    have ho : ¬ Odd m := by rw [Int.odd_iff]; omega
    have hn : ¬ m ≡ (-1) ^ (n - 1) [ZMOD 4] := by
      intro he
      change m % 4 = ((-1 : ℤ) ^ (n - 1)) % 4 at he
      rcases neg_one_pow_eq_or ℤ (n - 1) with hp | hp <;> rw [hp] at he <;>
        norm_num at he <;> omega
    exact ⟨iff_of_false ho hs, iff_of_false hn hs,
      fun _ => Int.dvd_iff_emod_eq_zero.mpr hm⟩

theorem result : D5.S1.Recurrence.Bilateral.HannaThetaFourModFour.claim := by
  refine ⟨⟨_, integral_gf⟩, fun A hA n hn => ?_⟩
  rw [gf_unique A hA]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine ⟨coeff k solution, ?_, ?_⟩
  · simp only [coeff_map, coeff_succ_X_mul, Int.coe_castRingHom]
  · simpa only [Nat.add_sub_cancel, Nat.succ_sub_succ_eq_sub, Nat.sub_zero] using
      arithmetic (coeff k solution) (k + 1) (by simpa only [Nat.add_sub_cancel] using solution_mod_four k)

end D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
