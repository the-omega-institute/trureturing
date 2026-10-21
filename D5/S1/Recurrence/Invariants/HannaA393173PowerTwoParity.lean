/- GID: D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA393173PowerTwoParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A normalized inverse diagonal has odd coefficients exactly at powers of two. -/

/-
admission_basis: open-problem-resolution (#18824; Proved)
escape_witness: none
proof_shape: IsGF: bind-only; consumers: claim, isGF_iff_fixed, result; escape_witness: none.
proof_shape: claim: bind-only; consumers: result; escape_witness: none.
proof_shape: inverse_top: bind-only; consumers: step_contract; escape_witness: none.
proof_shape: binary_quadratic: bind-only; consumers: binary_inverse, candidate_fixed; escape_witness: none.
proof_shape: binary_parity: bind-only; consumers: result; escape_witness: none.
proof_shape: step: bind-only; consumers: step_zero, step_contract, fixed_iff, fixed_map, normalized_solution; escape_witness: none.
proof_shape: denominator_zero: bind-only; consumers: step_contract, fixed_map, isGF_iff_fixed; escape_witness: none.
proof_shape: step_zero: bind-only; consumers: normalized_solution; escape_witness: none.
proof_shape: step_contract: bind-only; consumers: normalized_solution; escape_witness: none.
proof_shape: fixed_iff: bind-only; consumers: fixed_map, isGF_iff_fixed, candidate_fixed; escape_witness: none.
proof_shape: fixed_map: bind-only; consumers: integral_mod_two, result; escape_witness: none.
proof_shape: isGF_iff_fixed: bind-only; consumers: result; escape_witness: none.
proof_shape: binary_inverse: bind-only; consumers: candidate_fixed; escape_witness: none.
proof_shape: candidate_fixed: bind-only; consumers: integral_mod_two; escape_witness: none.
proof_shape: normalized_solution: bind-only; consumers: fixed_unique, result; escape_witness: none.
proof_shape: fixed_unique: bind-only; consumers: integral_mod_two, result; escape_witness: none.
proof_shape: integral_mod_two: bind-only; consumers: result; escape_witness: none.
proof_shape: result: bind-only; consumers: settling conclusion; escape_witness: none.
Direct frozen dependencies (declaration statement_id):
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.powerTwoSeries: sha256:b8d06ca726de7b75ba200f87da476e9506036c6dab9e63f4421f4681357c960a
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.power_two_zero: sha256:1294c542989f805f468158e6cbdaf12b7c07cbe1a88d0868854d1717c72163c4
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.prime_power_subst: sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.thue_series_equation: sha256:fc3ac63dd05e27bfd84403674dfaa5f427c0b485f4d8a16e79f6e39110349fe2
  D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed: sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree: sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff: sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6
  D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.inverse_agreement: sha256:d1379c38e0f8cbcd0bdb5f7cf15b769e6f62621f650163840608c4c7690dcd03
  D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.map_inverse: sha256:eec2ac5aeb5ff2c68ae3f71d23957e78007dd42cce9fc105e609e2ef21d334ee
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19804.
The public definitions retain the source expressions. The proof uses the existing
coefficient-agreement predicate and normalized-contraction theorem directly.
All helpers are consumed applications, coefficient extraction, or normalization.
The utility is none: no finite-instance certificate or bounded enumeration is used.
-/

import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour

set_option autoImplicit false
open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaA393173PowerTwoParity
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
  (powerTwoSeries power_two_zero prime_power_subst)
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (Agree)
open D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour (inverse_agreement)

/-- OEIS A393173: "G.f. A(x) satisfies [x^n] 1/(A(x) - n^2*x) = 0 for n >= 1", offset 0, a(0) = 1. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧ ∀ n : ℕ, 1 ≤ n → coeff n (A - C ((n : ℚ) ^ 2) * X)⁻¹ = 0

/-- OEIS A393173 (P. D. Hanna), conjecture: "for n > 0, a(n) is odd iff n is a power of 2." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 0 < n → ∃ m : ℤ, coeff n A = m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k)


variable {R : Type*} [CommRing R]

private theorem inverse_top {d : ℕ} {f g : PowerSeries R} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (h : ∀ n < d, coeff n f = coeff n g) :
    coeff d (invOfUnit f 1) - coeff d (invOfUnit g 1) = -(coeff d f - coeff d g) := by
  have hd : (X : PowerSeries R) ^ d ∣ f - g :=
    (D5.S1.Recurrence.Invariants.UnitReversionSquareParity.agree_iff d f g).mp h
  obtain ⟨w, hw⟩ := hd
  let : Invertible f := ⟨invOfUnit f 1, invOfUnit_mul f 1 hf, mul_invOfUnit f 1 hf⟩
  let : Invertible g := ⟨invOfUnit g 1, invOfUnit_mul g 1 hg, mul_invOfUnit g 1 hg⟩
  have he : invOfUnit f 1 - invOfUnit g 1 = -(f - g) * (invOfUnit f 1 * invOfUnit g 1) := by
    calc
      _ = invOfUnit f 1 * (g - f) * invOfUnit g 1 := invOf_sub_invOf f g
      _ = _ := by ring
  rw [hw] at he
  have he' : invOfUnit f 1 - invOfUnit g 1 =
      X ^ d * (-(w * (invOfUnit f 1 * invOfUnit g 1))) := by rw [he]; ring
  have hc := congrArg (coeff d) he'
  have hc' := congrArg (coeff d) hw
  simp only [map_sub, coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self,
    coeff_zero_eq_constantCoeff, map_neg, map_mul, constantCoeff_invOfUnit,
    Units.val_one, inv_one, mul_one] at hc hc'
  rw [hc']
  exact hc


private theorem binary_quadratic : powerTwoSeries + powerTwoSeries ^ 2 = (X : PowerSeries (ZMod 2)) := by
  have he := D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.thue_series_equation.1
  have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_ofNat C 2, CharTwo.two_eq_zero (R := ZMod 2), map_zero]
  linear_combination he + powerTwoSeries ^ 2 * hz

private theorem binary_parity (f : PowerSeries ℤ) (he : f.map (Int.castRingHom (ZMod 2)) = 1 + powerTwoSeries)
    (n : ℕ) (hn : 0 < n) : Odd (coeff n f) ↔ ∃ k : ℕ, n = 2 ^ k := by
  classical
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hc := congrArg (coeff n) he
  simp only [coeff_map, Int.coe_castRingHom, map_add, coeff_one, ite_eq_right (by omega : n ≠ 0), zero_add,
    powerTwoSeries, coeff_mk] at hc
  rw [hc]
  split_ifs <;> simp_all


private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  mk fun n => if n = 0 then 1 else coeff n f + coeff n (invOfUnit (f - C ((n : R)^2) * X) 1)

private theorem denominator_zero (f : PowerSeries R) (hf : constantCoeff f = 1) (n : ℕ) :
    constantCoeff (f - C ((n : R)^2) * X) = 1 := by simp [hf]

private theorem step_zero (f : PowerSeries R) : constantCoeff (step f) = 1 :=
  MonoidHom.mem_mker.mp rfl

private theorem step_contract (d : ℕ) (f g : PowerSeries R) (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (h : Agree d f g) : Agree (d+1) (step f) (step g) := by
  intro n hn
  simp only [step, coeff_mk]
  split_ifs with hn0
  · rfl
  have hd : Agree d (f - C ((n : R)^2) * X) (g - C ((n : R)^2) * X) := by
    intro k hk
    simp only [map_sub, h k hk]
  by_cases hnd : n < d
  · rw [h n hnd, inverse_agreement (denominator_zero f hf n) (denominator_zero g hg n) hd n hnd]
  · have hnd : n = d := Nat.eq_of_lt_succ_of_not_lt hn hnd
    subst n
    have ht := inverse_top (denominator_zero f hf d) (denominator_zero g hg d) hd
    simp only [map_sub] at ht
    linear_combination ht

private theorem fixed_iff (f : PowerSeries R) (hf : constantCoeff f = 1) :
    f = step f ↔ ∀ n : ℕ, 0 < n → coeff n (invOfUnit (f - C ((n : R)^2) * X) 1) = 0 := by
  constructor
  · intro he n hn
    have hc := congrArg (coeff n) he
    simp only [step, coeff_mk, ite_eq_right (by omega : n ≠ 0)] at hc
    linear_combination -hc
  · intro h
    ext n
    by_cases hn : n = 0
    · subst n
      simpa [step, coeff_zero_eq_constantCoeff] using hf
    · simp only [step, coeff_mk, ite_eq_right hn, h n (by omega), add_zero]

private theorem fixed_map {T : Type*} [CommRing T] (hom : R →+* T) (f : PowerSeries R)
    (hf : constantCoeff f = 1) (he : f = step f) : f.map hom = step (f.map hom) := by
  have hz : constantCoeff (f.map hom) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf, map_one]
  apply (fixed_iff _ hz).mpr
  intro n hn
  have h := congrArg hom ((fixed_iff f hf).mp he n hn)
  rw [map_zero, ← coeff_map, D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour.map_inverse hom _ (denominator_zero f hf n)] at h
  simpa only [map_sub, map_mul, map_X, map_C, map_pow, map_natCast] using h

private theorem isGF_iff_fixed (A : PowerSeries ℚ) :
    IsGF A ↔ constantCoeff A = 1 ∧ A = step A := by
  constructor
  · rintro ⟨hz, he⟩
    refine ⟨hz, (fixed_iff A hz).mpr ?_⟩
    intro n hn
    rw [invOfUnit_eq' _ 1 (denominator_zero A hz n)]
    exact he n (by omega)
  · rintro ⟨hz, he⟩
    refine ⟨hz, fun n hn => ?_⟩
    have h := (fixed_iff A hz).mp he n (by omega)
    rw [invOfUnit_eq' _ 1 (denominator_zero A hz n)] at h
    exact h

private theorem binary_inverse : invOfUnit (1 + powerTwoSeries) 1 = (mk fun n => coeff (n+1) powerTwoSeries) := by
  have hs : powerTwoSeries = X * (mk fun n => coeff (n+1) powerTwoSeries) := by
    simpa only [power_two_zero, map_zero, add_zero] using eq_X_mul_shift_add_const powerTwoSeries
  have h : (1 + powerTwoSeries) * powerTwoSeries = (X : PowerSeries (ZMod 2)) := by
    linear_combination binary_quadratic
  have hh : (1 + powerTwoSeries) * (mk fun n => coeff (n+1) powerTwoSeries) = 1 := by
    apply mul_left_cancel₀ (X_ne_zero (R := ZMod 2))
    calc
      X * ((1 + powerTwoSeries) * (mk fun n => coeff (n+1) powerTwoSeries)) =
          (1 + powerTwoSeries) * (X * (mk fun n => coeff (n+1) powerTwoSeries)) := by ring
      _ = (1 + powerTwoSeries) * powerTwoSeries := congrArg ((1 + powerTwoSeries) * ·) hs.symm
      _ = X * 1 := by simpa using h
  rw [invOfUnit_eq' _ 1 (by simp [power_two_zero])]
  exact (eq_inv_iff_mul_eq_one (by simp [power_two_zero] : constantCoeff (1 + powerTwoSeries) ≠ 0)).mpr
    (by simpa only [mul_comm] using hh) |>.symm

private theorem candidate_fixed : (1 + powerTwoSeries : PowerSeries (ZMod 2)) = step (1 + powerTwoSeries) := by
  classical
  apply (fixed_iff _ (by simp [power_two_zero])).mpr
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · have hc : (n : ZMod 2) = 0 := he.natCast_zmod_two
    have hd : ((1 + powerTwoSeries) - C ((n : ZMod 2)^2) * X) = 1 + powerTwoSeries := by simp [hc]
    rw [hd, binary_inverse]
    have hnp : ¬ ∃ k : ℕ, n+1 = 2^k := by
      rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        have hd : 2 ∣ n+1 := Dvd.intro_left (2 ^ k) hk.symm
        have he' := even_iff_two_dvd.mp he
        omega
    simp only [coeff_mk, powerTwoSeries,
      coeff_mk, ite_eq_right hnp]
  · have hc : (n : ZMod 2) = 1 := ho.natCast_zmod_two
    have hd : ((1 + powerTwoSeries) - C ((n : ZMod 2)^2) * X) = (1 + powerTwoSeries)^2 := by
      simp only [hc, one_pow, map_one, one_mul]
      have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
        rw [← map_ofNat C 2, CharTwo.two_eq_zero (R := ZMod 2), map_zero]
      linear_combination -binary_quadratic - X * hz
    rw [hd, invOfUnit_eq' _ 1 (by simp [power_two_zero]), ← PowerSeries.inv_pow]
    rw [prime_power_subst 2, coeff_subst_X_pow (by decide)]
    have hd' : ¬ 2 ∣ n := ho.not_two_dvd_nat
    simp [hd']

private theorem normalized_solution : ∃ f : PowerSeries R, constantCoeff f = 1 ∧ f = step f ∧
    ∀ g, constantCoeff g = 1 → g = step g → g = f :=
  D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
    step (fun f _ => step_zero f) (fun _ hf hg h => step_contract _ _ _ hf hg h)

private theorem fixed_unique (f g : PowerSeries R) (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (hff : f = step f) (hgg : g = step g) : f = g := by
  obtain ⟨u, _, _, hu⟩ := normalized_solution (R := R)
  exact (hu f hf hff).trans (hu g hg hgg).symm

private theorem integral_mod_two (f : PowerSeries ℤ) (hf : constantCoeff f = 1) (he : f = step f) :
    f.map (Int.castRingHom (ZMod 2)) = 1 + powerTwoSeries := by
  apply fixed_unique _ _ _ (by simp [power_two_zero])
    (fixed_map _ f hf he) candidate_fixed
  rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf]
  rfl

theorem result : claim := by
  obtain ⟨f, hf, he, _⟩ := normalized_solution (R := ℤ)
  have hq : IsGF (f.map (Int.castRingHom ℚ)) :=
    (isGF_iff_fixed _).mpr ⟨by
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf]; rfl,
      fixed_map _ f hf he⟩
  refine ⟨⟨_, hq⟩, ?_⟩
  intro A hA n hn
  obtain ⟨hA0, hAf⟩ := (isGF_iff_fixed A).mp hA
  have hEq : A = f.map (Int.castRingHom ℚ) :=
    fixed_unique _ _ hA0 ((isGF_iff_fixed _).mp hq).1 hAf
      ((isGF_iff_fixed _).mp hq).2
  refine ⟨coeff n f, ?_, binary_parity f (integral_mod_two f hf he) n hn⟩
  rw [hEq, coeff_map]
  rfl


end D5.S1.Recurrence.Invariants.HannaA393173PowerTwoParity
