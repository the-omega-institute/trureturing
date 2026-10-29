/- GID: D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent
   generality: G
   mirror-B: D5/B/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Unit-exponent extension settles Hanna's A380066 congruence for c >= 1. -/

/-
The public definitions quote the OEIS convention literally; the frozen owner is used only inside
private correspondence and proof steps.  All proof helpers are private and consumed by the
settling result. The frozen suppliers are BilateralProductModFour and
PowerSeriesNormalizedContraction.exists_unique_fixed.
proof_shape: result = bind-only
escape_witness: result = none
The stabilization induction proves facts about the specified approximations and diagonal
series for every c >= 1. It is not an escape witness for the existential result: the
frozen contraction theorem supplies a normalized fixed point without that construction.
The generic uniqueness application uses R = Z and step c; step_zero supplies normalized
preservation and step_agree supplies strict contraction. The two Agree predicates are
definitionally equal. polynomial_unique identifies both normalized fixed points with
the generic witness. Its conclusion still names the specified diagonal generatingSeries,
whose fixed-point property is supplied by the stabilization construction.

| declaration | proof_shape | escape_witness | direct consumers |
| --- | --- | --- | --- |
| UnitExponent.term_order | bind-only | none | UnitExponent.outside_zero |
| UnitExponent.outside_zero | bind-only | none | UnitExponent.finite_window |
| UnitExponent.finite_window | bind-only | none | UnitExponent.laurent_window, UnitExponent.sum_zero |
| UnitExponent.sum_zero | bind-only | none | UnitExponent.step_agree, UnitExponent.step_zero |
| UnitExponent.term_agree | bind-only | none | UnitExponent.sum_agree |
| UnitExponent.sum_agree | bind-only | none | UnitExponent.step_agree |
| UnitExponent.step_zero | bind-only | none | UnitExponent.polynomial_form, UnitExponent.polynomial_unique |
| UnitExponent.step_agree | bind-only | none | UnitExponent.approximation_stable, UnitExponent.generating_fixed, UnitExponent.polynomial_unique |
| UnitExponent.approximation_stable | content | UnitExponent.approximation_stable | UnitExponent.generating_agree |
| UnitExponent.generating_agree | content | UnitExponent.approximation_stable | UnitExponent.generating_fixed |
| UnitExponent.generating_fixed | content | UnitExponent.approximation_stable | UnitExponent.coefficient_four_dvd, UnitExponent.polynomial_form, UnitExponent.polynomial_unique |
| UnitExponent.polynomial_form | content | UnitExponent.approximation_stable | UnitExponent.generating_equation, UnitExponent.laurent_identity |
| UnitExponent.polynomial_unique | content | UnitExponent.approximation_stable | UnitExponent.generating_unique |
| UnitExponent.laurent_normalization | bind-only | none | UnitExponent.laurent_window |
| UnitExponent.laurent_window | bind-only | none | UnitExponent.equation_of_laurent, UnitExponent.generating_equation |
| UnitExponent.laurent_identity | content | UnitExponent.approximation_stable | UnitExponent.generating_equation |
| UnitExponent.generating_equation | content | UnitExponent.approximation_stable | result |
| UnitExponent.equation_of_laurent | bind-only | none | UnitExponent.generating_unique |
| UnitExponent.generating_unique | content | UnitExponent.approximation_stable | result |
| UnitExponent.coefficient_four_dvd | content | UnitExponent.approximation_stable | UnitExponent.hanna_conjecture_general |
| UnitExponent.hanna_conjecture_general | content | UnitExponent.approximation_stable | result |
| result | bind-only | none | none |
admission_basis: pending external open-problem-resolution (#18805; Proved).
The preregistration specifies the literal claim and tier before the original delivery.
Its literature screen remains incomplete (ASSUMED-UNVERIFIED), so the bind-only terminal
result has no verified admission exception. The module remains mathematical WIP for
admission; its candidate pin and the linked audit issue supply no exception.
Escape audit: result — https://github.com/the-omega-institute/trureturing/issues/20261.
Direct frozen dependencies: PowerSeriesNormalizedContraction.exists_unique_fixed (protected-baseline module statement_id sha256:6fde09331cce748985c92e44cd8bb294c09eb2f01eeea1d646183f03ab04baf4); BilateralProductModFour.laurentTerm (sha256:376c1a862fdd901131b6ce6b839a230a385199b6d8908eaa9acad48868601e0e), bilateralTerm (sha256:93ca9c7b68470ac5db5c4e197fdaacc6a38e37e6bade38df4244ecb4ea20e3fc), nonzeroSum (sha256:5b27d604826938f9c12ad4ca71d8aff5c710b2525327b2788e3ac851619ec203), generatingSeries (sha256:84e4cc046d08d9d34c19ab24cfec587a6c179c2d641c9330f6ec9a7e7aa04728), a (sha256:d1fd34c260df28d6a8ffbb60cb1faaeefb4bdb43c652c75cb58f984c2ed8270b); published owners Agree (sha256:81371ab5f236f52665c836befe987abe2c238c2ad1a09929b2d932b14b557be7), approximation (sha256:21e66904f2406378d82aa3d96245aaa1fa1c25f26cdd0b90556a2af7e370beea), step (sha256:e594efea638591ca1b1fbf09182ee696f5716f038d13b0ec28cfb3ca9fcbb3d3), geometric (sha256:081a25f95093c6453bbdc2a20f9a009701ce2c16e67d86a2b9079c74b0f24c57), embed (sha256:0bd1c43f5ed3ac3be778ebc90be3618a8ef3cb5984dd6a924907e8d8f5c06f1d), positiveTerm (sha256:606cb881803cd3edf13172330b742224520692d1e67eafd8cb73578af5fe8871), negativeTerm (sha256:81daea39837d82b596ea5e7718e28850912c0edac89daae681d548e5025d1dc5), and their consumed lemmas are public at the original owner and applied directly.
-/

import D5.S1.Recurrence.Bilateral.BilateralProductModFour
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

set_option autoImplicit false

/-! The unit-exponent bilateral product has a normalized integral fixed series. -/


namespace D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent

namespace HannaA380066

open PowerSeries
open D5.S1.Recurrence.Bilateral.BilateralProductModFour (laurentTerm)

/-- OEIS A380066: "G.f. A(x) satisfies 1/2 = Sum_{n=-oo..+oo} x^n*A(x)^n *
(A(x)^n + x)^(n-1) * (A(x) + x^n)^(n-1)", a(0) = 1.
`laurentTerm 1 A j` is the j-th summand (the frozen family with c = 1),
and the bilateral series is read coefficientwise through the symmetric windows [-K, K], K ≥ N, as in the
frozen `BilateralProductModFour.generating_equation`. -/
def IsGF (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 1 ∧
    ∀ N K : ℕ, N ≤ K →
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (laurentTerm 1 A j).coeff (N : ℤ)) =
        if N = 0 then (1 / 2 : ℚ) else 0

/-- OEIS A380066 (P. D. Hanna), conjecture: "for n > 0, a(n) == 2 (mod 4)." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧ ∀ A, IsGF A → ∀ n : ℕ, 0 < n → coeff n A % 4 = 2

end HannaA380066

open PowerSeries
open D5.S1.Recurrence.Bilateral.BilateralProductModFour
namespace UnitExponent
private theorem term_order (c : ℕ) (hc : 1 ≤ c) (A : PowerSeries ℤ) (j : ℤ) :
    (X : PowerSeries ℤ) ^ j.natAbs ∣ bilateralTerm c A j := by
  unfold bilateralTerm
  split_ifs with h0 hp
  · exact dvd_zero _
  · exact dvd_mul_right _ _
  · apply dvd_trans (pow_dvd_pow X (show j.natAbs ≤ c * j.natAbs ^ 2 by
      calc
        j.natAbs ≤ j.natAbs ^ 2 := by
          simpa only [pow_two] using Nat.le_mul_self j.natAbs
        _ ≤ c * j.natAbs ^ 2 := by
          simpa only [one_mul] using Nat.mul_le_mul_right (j.natAbs ^ 2) hc))
    exact dvd_mul_right _ _

private theorem outside_zero (c : ℕ) (hc : 1 ≤ c) (A : PowerSeries ℤ)
    (N : ℕ) (j : ℤ) (hj : j < -(N : ℤ) ∨ (N : ℤ) < j) :
    coeff N (bilateralTerm c A j) = 0 := by
  exact X_pow_dvd_iff.mp (term_order c hc A j) N (by omega)

private theorem finite_window (c : ℕ) (hc : 1 ≤ c) (A : PowerSeries ℤ)
    (N K : ℕ) (hNK : N ≤ K) :
    (∀ j : ℤ, j < -(N : ℤ) ∨ (N : ℤ) < j → coeff N (bilateralTerm c A j) = 0) ∧
    coeff N (nonzeroSum c A) =
      ∑ j ∈ Finset.Icc (-(K : ℤ)) K, coeff N (bilateralTerm c A j) := by
  refine ⟨outside_zero c hc A N, ?_⟩
  simp only [nonzeroSum, coeff_mk]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj hnot
    apply outside_zero c hc A N j
    simp only [Finset.mem_Icc] at hnot
    omega

private theorem sum_zero (c : ℕ) (hc : 1 ≤ c) (A : PowerSeries ℤ) :
    constantCoeff (nonzeroSum c A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, (finite_window c hc A 0 0 le_rfl).2]
  simp [bilateralTerm]

private theorem term_agree (c : ℕ) (hc : 1 ≤ c) {d : ℕ} {A B : PowerSeries ℤ}
    (h : Agree d A B) (j : ℤ) : Agree (d + 1) (bilateralTerm c A j) (bilateralTerm c B j) := by
  have hr := agree_refl d
  unfold bilateralTerm
  split_ifs with h0 hp
  · exact agree_refl _ _
  · apply agree_shift (Int.natAbs_pos.mpr h0)
    exact agree_mul (agree_mul (agree_pow h _)
      (agree_pow (agree_add (agree_pow h _) (hr X)) _))
      (agree_pow (agree_add (hr _) h) _)
  · have hk : 0 < j.natAbs := Int.natAbs_pos.mpr h0
    have he : 0 < c * j.natAbs ^ 2 := Nat.mul_pos hc (pow_pos hk _)
    apply agree_shift he
    apply agree_mul
    · apply agree_mul (agree_pow h _)
      apply agree_pow
      apply agree_inverse (by simp) (by simp)
      exact agree_add (hr 1) (agree_mul (hr X) (agree_pow h _))
    · apply agree_pow
      apply agree_inverse (by simp [ne_of_gt hk]) (by simp [ne_of_gt hk])
      exact agree_add (hr 1) (agree_mul (hr _) h)

private theorem sum_agree (c : ℕ) (hc : 1 ≤ c) {d : ℕ} {A B : PowerSeries ℤ}
    (h : Agree d A B) : Agree (d + 1) (nonzeroSum c A) (nonzeroSum c B) := by
  intro n hn
  simp only [nonzeroSum, coeff_mk]
  exact Finset.sum_congr rfl fun j _ => term_agree c hc h j n hn

private theorem step_zero (c : ℕ) (hc : 1 ≤ c) (A : PowerSeries ℤ) :
    constantCoeff (step c A) = 1 := by
  norm_num [step, sum_zero c hc, geometric, constantCoeff_invOfUnit, map_ofNat]

private theorem step_agree (c : ℕ) (hc : 1 ≤ c) {d : ℕ} {A B : PowerSeries ℤ}
    (h : Agree d A B) : Agree (d + 1) (step c A) (step c B) := by
  have hs := (agree_iff _ _ _).mp (sum_agree c hc h)
  have ha := (agree_iff _ _ _).mp h
  have hx := X_dvd_iff.mpr (sum_zero c hc B)
  have ht : (X : PowerSeries ℤ) ^ (d + 1) ∣
      (1 + A) * nonzeroSum c A - (1 + B) * nonzeroSum c B := by
    have h1 := dvd_mul_of_dvd_right hs (1 + A)
    have h2 := mul_dvd_mul ha hx
    rw [← pow_succ] at h2
    convert dvd_add h1 h2 using 1
    ring
  apply (agree_iff _ _ _).mpr
  convert dvd_mul_of_dvd_right ht 2 using 1
  unfold step
  ring

private theorem approximation_stable (c : ℕ) (hc : 1 ≤ c) {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation c d) (approximation c e) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e => exact step_agree c hc (ih (by omega))

private theorem generating_agree (c : ℕ) (hc : 1 ≤ c) (d : ℕ) :
    Agree d (generatingSeries c) (approximation c d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable c hc (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed (c : ℕ) (hc : 1 ≤ c) :
    generatingSeries c = step c (generatingSeries c) := by
  ext n
  exact (generating_agree c hc (n + 2) n (by omega)).trans
    (step_agree c hc (generating_agree c hc (n + 1)) n (by omega)).symm

private theorem polynomial_form (c : ℕ) (hc : 1 ≤ c) :
    constantCoeff (generatingSeries c) = 1 ∧
    (1 + X) * (1 + generatingSeries c) * (1 - 2 * nonzeroSum c (generatingSeries c)) = 2 := by
  refine ⟨?_, (equation_iff c _).mpr (generating_fixed c hc)⟩
  rw [generating_fixed c hc, step_zero c hc]

private theorem polynomial_unique (c : ℕ) (hc : 1 ≤ c) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 1)
    (hB : (1 + X) * (1 + B) * (1 - 2 * nonzeroSum c B) = 2) :
    B = generatingSeries c := by
  obtain ⟨F, _, _, unique⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      (step c) (fun A _ => step_zero c hc A)
      (fun _ _ _ h => step_agree c hc h)
  exact (unique B h0 ((equation_iff c B).mp hB)).trans
    (unique (generatingSeries c) (polynomial_form c hc).1
      (generating_fixed c hc)).symm

private theorem laurent_normalization (c : ℕ) (hc : 1 ≤ c)
    (A : PowerSeries ℤ) (hA : constantCoeff A = 1) (j : ℤ) (hj : j ≠ 0) :
    laurentTerm c A j = embed (bilateralTerm c A j) := by
  have hx : embed X ≠ 0 := by
    intro he
    exact X_ne_zero (embed_injective (by simpa using he))
  have ha : embed A ≠ 0 := by
    intro he
    have hz : A = 0 := embed_injective (by simpa using he)
    simp [hz] at hA
  have hk : 0 < j.natAbs := Int.natAbs_pos.mpr hj
  unfold bilateralTerm
  rw [if_neg hj]
  split_ifs with hp
  · have hjk : j = (j.natAbs : ℤ) := Int.eq_natAbs_of_nonneg (le_of_lt hp)
    have he : (c : ℤ) * j - 1 = ((c * j.natAbs - 1 : ℕ) : ℤ) := by
      conv_lhs => rw [hjk]
      rw [Nat.cast_sub (Nat.mul_pos hc hk)]
      push_cast
      rfl
    simp only [laurentTerm, he]
    conv_lhs => rw [hjk]
    simp only [Int.natAbs_natCast, zpow_natCast, positiveTerm, map_mul, map_pow, map_add]
    ring
  · have hjk : j = -(j.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos (le_of_not_gt hp)
    have he : (c : ℤ) * j - 1 = -((c * j.natAbs + 1 : ℕ) : ℤ) := by
      conv_lhs => rw [hjk]
      push_cast
      ring
    simp only [laurentTerm, he]
    conv_lhs => rw [hjk]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [negative_factorization _ _ hx ha]
    simp only [negativeTerm, map_mul, map_pow, embed_inverse (1 + X * A ^ j.natAbs) (by simp),
      embed_inverse (1 + X ^ j.natAbs * A) (by simp [ne_of_gt hk]), map_add, map_one]

private theorem laurent_window (c : ℕ) (hc : 1 ≤ c)
    (A : PowerSeries ℤ) (hA : constantCoeff A = 1) (N K : ℕ) (hNK : N ≤ K) :
    (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (laurentTerm c A j).coeff (N : ℤ)) =
    (laurentTerm c A 0).coeff (N : ℤ) + ((coeff N (nonzeroSum c A) : ℤ) : ℚ) := by
  rw [(finite_window c hc A N K hNK).2, Int.cast_sum]
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(K : ℤ)) K := by simp
  rw [← Finset.sum_erase_add _ _ h0]
  conv_rhs => rw [← Finset.sum_erase_add _ _ h0]
  have hz : bilateralTerm c A 0 = 0 := by simp [bilateralTerm]
  simp only [hz, map_zero, Int.cast_zero, add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 := (Finset.mem_erase.mp hj).1
  rw [laurent_normalization c hc A hA j hj0, embed_coeff]

private theorem laurent_identity (c : ℕ) (hc : 1 ≤ c) :
    laurentTerm c (generatingSeries c) 0 + embed (nonzeroSum c (generatingSeries c)) =
      (1 / 2 : LaurentSeries ℚ) := by
  let A := generatingSeries c
  let H := nonzeroSum c A
  have he := congrArg embed (polynomial_form c hc).2
  simp only [map_mul, map_add, map_sub, map_one, map_ofNat] at he
  have hx : 1 + embed X ≠ 0 := by
    intro hz
    have hh : (1 : ℚ) = 0 := by
      have hcoeff := congrArg (fun F : LaurentSeries ℚ => F.coeff 0) hz
      have hmap : 1 + embed X = embed (1 + X) := by simp
      rw [hmap, ← show ((0 : ℕ) : ℤ) = 0 from rfl, embed_coeff] at hcoeff
      simp at hcoeff
    norm_num at hh
  have ha : 1 + embed A ≠ 0 := by
    intro hz
    have hmap : 1 + embed A = embed (1 + A) := by simp
    have hcoeff := congrArg (fun F : LaurentSeries ℚ => F.coeff 0) hz
    rw [hmap, ← show ((0 : ℕ) : ℤ) = 0 from rfl, embed_coeff] at hcoeff
    have hA := (polynomial_form c hc).1
    change constantCoeff A = 1 at hA
    norm_num [coeff_zero_eq_constantCoeff, hA] at hcoeff
  rw [laurent_zero]
  change (1 + embed X)⁻¹ * (1 + embed A)⁻¹ + embed H = 1 / 2
  change (1 + embed X) * (1 + embed A) * (1 - 2 * embed H) = 2 at he
  have htwo : (2 : LaurentSeries ℚ) ≠ 0 := by
    intro h
    have h2 : (2 : PowerSeries ℤ) = 0 :=
      embed_injective (by simpa only [map_ofNat, map_zero] using h)
    have hh := congrArg constantCoeff h2
    norm_num only [map_ofNat, map_zero] at hh
  apply (eq_div_iff htwo).mpr
  field_simp [hx, ha]
  linear_combination -he

private theorem generating_equation (c : ℕ) (hc : 1 ≤ c) :
    constantCoeff (generatingSeries c) = 1 ∧
    ∀ N K : ℕ, N ≤ K →
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K,
        (laurentTerm c (generatingSeries c) j).coeff (N : ℤ)) =
      if N = 0 then (1 / 2 : ℚ) else 0 := by
  refine ⟨(polynomial_form c hc).1, fun N K hNK => ?_⟩
  rw [laurent_window c hc _ (polynomial_form c hc).1 N K hNK]
  have he := congrArg (fun F : LaurentSeries ℚ => F.coeff (N : ℤ)) (laurent_identity c hc)
  rw [HahnSeries.coeff_add, embed_coeff] at he
  convert he using 1
  have hh : (1 / 2 : LaurentSeries ℚ) =
      HahnSeries.ofPowerSeries ℤ ℚ (C (1 / 2)) := by simp
  rw [hh]
  change (if N = 0 then (1 / 2 : ℚ) else 0) =
    ((C (1 / 2) : PowerSeries ℚ) : LaurentSeries ℚ).coeff (N : ℤ)
  rw [LaurentSeries.coeff_coe_powerSeries, coeff_C]

private theorem equation_of_laurent (c : ℕ) (hc : 1 ≤ c) (A : PowerSeries ℤ)
    (hA : constantCoeff A = 1)
    (hB : ∀ N K : ℕ, N ≤ K →
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (laurentTerm c A j).coeff (N : ℤ)) =
        if N = 0 then (1 / 2 : ℚ) else 0) :
    (1 + X) * (1 + A) * (1 - 2 * nonzeroSum c A) = 2 := by
  let B := A.map (Int.castRingHom ℚ)
  let H := (nonzeroSum c A).map (Int.castRingHom ℚ)
  let Q : PowerSeries ℚ := (1 + X)⁻¹ * (1 + B)⁻¹
  have hs : Q + H = C (1 / 2) := by
    ext N
    have he := hB N N le_rfl
    rw [laurent_window c hc A hA N N le_rfl, zeroTerm_series c A hA,
      HahnSeries.ofPowerSeries_apply_coeff] at he
    simpa only [map_add, coeff_C, H, coeff_map, Int.coe_castRingHom] using he
  have hB0 : constantCoeff B = 1 := by
    dsimp only [B]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hA, map_one]
  have hu := PowerSeries.inv_mul_cancel (1 + (X : PowerSeries ℚ)) (by simp)
  have hv := PowerSeries.inv_mul_cancel (1 + B) (by rw [map_add, constantCoeff_one, hB0]; norm_num)
  have hi : Q * ((1 + X) * (1 + B)) = 1 := by
    calc
      _ = ((1 + X)⁻¹ * (1 + X)) * ((1 + B)⁻¹ * (1 + B)) := by dsimp [Q]; ring
      _ = 1 := by rw [hu, hv, mul_one]
  have htwo : (2 : PowerSeries ℚ) * C (1 / 2) = 1 := by
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_mul, map_add, map_one, map_X, map_sub, map_ofNat]
  change (1 + X) * (1 + B) * (1 - 2 * H) = 2
  linear_combination -2 * (1 + X) * (1 + B) * hs + 2 * hi -
    (1 + X) * (1 + B) * htwo

private theorem generating_unique (c : ℕ) (hc : 1 ≤ c) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 1)
    (hB : ∀ N K : ℕ, N ≤ K →
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (laurentTerm c B j).coeff (N : ℤ)) =
        if N = 0 then (1 / 2 : ℚ) else 0) :
    B = generatingSeries c := by
  exact polynomial_unique c hc B h0 (equation_of_laurent c hc B h0 hB)

private theorem coefficient_four_dvd (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    4 ∣ a c n - coeff n (2 * geometric - 1) := by
  let A := generatingSeries c
  let H := nonzeroSum c A
  let B := geometric + (1 + A) * H
  have he : A = 2 * geometric - 1 + 2 * ((1 + A) * H) := generating_fixed c hc
  have hb : 1 + A = 2 * B := by dsimp only [B]; linear_combination he
  have hfour : A - (2 * geometric - 1) = 4 * (B * H) := by
    linear_combination he + 2 * H * hb
  refine ⟨coeff n (B * H), ?_⟩
  have hn := congrArg (coeff n) hfour
  simpa only [A, generatingSeries, coeff_mk, map_sub,
    show (4 : PowerSeries ℤ) = C 4 from (map_ofNat C 4).symm, coeff_C_mul] using hn

private theorem hanna_conjecture_general (c : ℕ) (hc : 1 ≤ c) (n : ℕ) (hn : 0 < n) :
    a c n % 4 = 2 := by
  have hd := coefficient_four_dvd c hc n
  rw [map_sub, show (2 : PowerSeries ℤ) = C 2 from (map_ofNat C 2).symm,
    coeff_C_mul, geometric_coeff, coeff_one, if_neg (ne_of_gt hn), sub_zero] at hd
  obtain ⟨k, hk⟩ := hd
  rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] at hk <;> omega

end UnitExponent

theorem result : HannaA380066.claim := by
  refine ⟨⟨generatingSeries 1, UnitExponent.generating_equation 1 le_rfl⟩, ?_⟩
  intro A hA n hn
  have hu := UnitExponent.generating_unique 1 le_rfl A hA.1 hA.2
  rw [hu]
  simpa only [generatingSeries, coeff_mk] using UnitExponent.hanna_conjecture_general 1 le_rfl n hn


end D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent
