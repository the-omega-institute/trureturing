/- GID: D5/S1/Recurrence/Bilateral/BilateralProductModFour
   generality: G
   mirror-B: D5/B/S1/Recurrence/Bilateral/BilateralProductModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite bilateral windows and integral contraction prove Hanna's product family. -/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.WellKnown

open PowerSeries
namespace D5.S1.Recurrence.Bilateral.BilateralProductModFour

private noncomputable def positiveTerm (c : ℕ) (A : PowerSeries ℤ) (k : ℕ) :=
  X ^ k * (A ^ k * (A ^ k + X) ^ (c * k - 1) * (X ^ k + A) ^ (c * k - 1))

private noncomputable def negativeTerm (c : ℕ) (A : PowerSeries ℤ) (k : ℕ) :=
  X ^ (c * k ^ 2) * (A ^ (c * k ^ 2) *
    invOfUnit (1 + X * A ^ k) 1 ^ (c * k + 1) *
    invOfUnit (1 + X ^ k * A) 1 ^ (c * k + 1))

-- The zero-index term is isolated as (1+X)⁻¹(1+A)⁻¹ over the rationals.
noncomputable def bilateralTerm (c : ℕ) (A : PowerSeries ℤ) (j : ℤ) : PowerSeries ℤ :=
  if j = 0 then 0 else if 0 < j then positiveTerm c A j.natAbs
    else negativeTerm c A j.natAbs

noncomputable def nonzeroSum (c : ℕ) (A : PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun N => ∑ j ∈ Finset.Icc (-(N : ℤ)) N, coeff N (bilateralTerm c A j)

private theorem term_order (c : ℕ) (hc : 2 ≤ c) (A : PowerSeries ℤ) (j : ℤ) :
    (X : PowerSeries ℤ) ^ j.natAbs ∣ bilateralTerm c A j := by
  unfold bilateralTerm
  split_ifs with h0 hp
  · exact dvd_zero _
  · exact dvd_mul_right _ _
  · apply dvd_trans (pow_dvd_pow X (show j.natAbs ≤ c * j.natAbs ^ 2 by
      have hj : 1 ≤ j.natAbs := by omega
      nlinarith [Nat.mul_le_mul_right (j.natAbs ^ 2) hc]))
    exact dvd_mul_right _ _

private theorem outside_zero (c : ℕ) (hc : 2 ≤ c) (A : PowerSeries ℤ)
    (N : ℕ) (j : ℤ) (hj : j < -(N : ℤ) ∨ (N : ℤ) < j) :
    coeff N (bilateralTerm c A j) = 0 :=
  X_pow_dvd_iff.mp (term_order c hc A j) N (by omega)

theorem finite_window (c : ℕ) (hc : 2 ≤ c) (A : PowerSeries ℤ)
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

private theorem sum_zero (c : ℕ) (hc : 2 ≤ c) (A : PowerSeries ℤ) :
    constantCoeff (nonzeroSum c A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, (finite_window c hc A 0 0 le_rfl).2]
  simp [bilateralTerm]

private def Agree (d : ℕ) (A B : PowerSeries ℤ) : Prop :=
  ∀ n < d, coeff n A = coeff n B

private theorem agree_iff (d : ℕ) (A B : PowerSeries ℤ) :
    Agree d A B ↔ (X : PowerSeries ℤ) ^ d ∣ A - B := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_refl (d : ℕ) (A : PowerSeries ℤ) : Agree d A A :=
  fun _ _ => rfl

private theorem agree_add {d : ℕ} {A B F G : PowerSeries ℤ}
    (h : Agree d A B) (h' : Agree d F G) : Agree d (A + F) (B + G) := by
  intro n hn
  simp only [map_add, h n hn, h' n hn]

private theorem agree_mul {d : ℕ} {A B F G : PowerSeries ℤ}
    (h : Agree d A B) (h' : Agree d F G) : Agree d (A * F) (B * G) := by
  apply (agree_iff _ _ _).mpr
  have ha := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) F
  have hb := dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h') B
  convert dvd_add ha hb using 1
  ring

private theorem agree_pow {d : ℕ} {A B : PowerSeries ℤ}
    (h : Agree d A B) (k : ℕ) : Agree d (A ^ k) (B ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow A B k))

private theorem agree_inverse {d : ℕ} {A B : PowerSeries ℤ}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree d A B) : Agree d (invOfUnit A 1) (invOfUnit B 1) := by
  have he : invOfUnit A 1 - invOfUnit B 1 =
      -(invOfUnit A 1 * invOfUnit B 1) * (A - B) := by
    linear_combination invOfUnit B 1 * invOfUnit_mul A 1 hA -
      invOfUnit A 1 * invOfUnit_mul B 1 hB
  apply (agree_iff _ _ _).mpr
  rw [he]
  exact dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h) _

private theorem agree_shift {d k : ℕ} {A B : PowerSeries ℤ}
    (hk : 0 < k) (h : Agree d A B) : Agree (d + 1) (X ^ k * A) (X ^ k * B) := by
  apply (agree_iff _ _ _).mpr
  have hx : (X : PowerSeries ℤ) ∣ X ^ k := by
    simpa only [pow_one] using pow_dvd_pow (X : PowerSeries ℤ) hk
  simpa only [pow_succ', mul_sub] using mul_dvd_mul hx ((agree_iff _ _ _).mp h)

private theorem term_agree (c : ℕ) (hc : 2 ≤ c) {d : ℕ} {A B : PowerSeries ℤ}
    (h : Agree d A B) (j : ℤ) : Agree (d + 1) (bilateralTerm c A j) (bilateralTerm c B j) := by
  have hr := agree_refl d
  unfold bilateralTerm
  split_ifs with h0 hp
  · exact agree_refl _ _
  · apply agree_shift (by omega : 0 < j.natAbs)
    exact agree_mul (agree_mul (agree_pow h _)
      (agree_pow (agree_add (agree_pow h _) (hr X)) _))
      (agree_pow (agree_add (hr _) h) _)
  · have hk : 0 < j.natAbs := by omega
    have he : 0 < c * j.natAbs ^ 2 := Nat.mul_pos (by omega) (pow_pos hk _)
    apply agree_shift he
    apply agree_mul
    · apply agree_mul (agree_pow h _)
      apply agree_pow
      apply agree_inverse (by simp) (by simp)
      exact agree_add (hr 1) (agree_mul (hr X) (agree_pow h _))
    · apply agree_pow
      apply agree_inverse (by simp [ne_of_gt hk]) (by simp [ne_of_gt hk])
      exact agree_add (hr 1) (agree_mul (hr _) h)

private theorem sum_agree (c : ℕ) (hc : 2 ≤ c) {d : ℕ} {A B : PowerSeries ℤ}
    (h : Agree d A B) : Agree (d + 1) (nonzeroSum c A) (nonzeroSum c B) := by
  intro n hn
  simp only [nonzeroSum, coeff_mk]
  exact Finset.sum_congr rfl fun j _ => term_agree c hc h j n hn

private noncomputable def geometric : PowerSeries ℤ := invOfUnit (1 + X) 1

private theorem geometric_spec : geometric * (1 + X) = 1 :=
  invOfUnit_mul _ 1 (by simp)

private noncomputable def step (c : ℕ) (A : PowerSeries ℤ) : PowerSeries ℤ :=
  2 * geometric - 1 + 2 * ((1 + A) * nonzeroSum c A)

private theorem step_zero (c : ℕ) (hc : 2 ≤ c) (A : PowerSeries ℤ) :
    constantCoeff (step c A) = 1 := by
  norm_num [step, sum_zero c hc, geometric, constantCoeff_invOfUnit, map_ofNat]

private theorem step_agree (c : ℕ) (hc : 2 ≤ c) {d : ℕ} {A B : PowerSeries ℤ}
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

private noncomputable def approximation (c : ℕ) : ℕ → PowerSeries ℤ
  | 0 => 1
  | d + 1 => step c (approximation c d)

private theorem approximation_stable (c : ℕ) (hc : 2 ≤ c) {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation c d) (approximation c e) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e => exact step_agree c hc (ih (by omega))

noncomputable def a (c n : ℕ) : ℤ := coeff n (approximation c (n + 1))

noncomputable def generatingSeries (c : ℕ) : PowerSeries ℤ := mk (a c)

private theorem generating_agree (c : ℕ) (hc : 2 ≤ c) (d : ℕ) :
    Agree d (generatingSeries c) (approximation c d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable c hc (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed (c : ℕ) (hc : 2 ≤ c) :
    generatingSeries c = step c (generatingSeries c) := by
  ext n
  exact (generating_agree c hc (n + 2) n (by omega)).trans
    (step_agree c hc (generating_agree c hc (n + 1)) n (by omega)).symm

private theorem equation_iff (c : ℕ) (A : PowerSeries ℤ) :
    (1 + X) * (1 + A) * (1 - 2 * nonzeroSum c A) = 2 ↔ A = step c A := by
  constructor
  · intro he
    have hg := geometric_spec
    unfold step
    linear_combination geometric * he - (1 + A) * (1 - 2 * nonzeroSum c A) * hg
  · intro he
    unfold step at he
    linear_combination (1 + X) * he + 2 * geometric_spec

theorem polynomial_form (c : ℕ) (hc : 2 ≤ c) :
    constantCoeff (generatingSeries c) = 1 ∧
    (1 + X) * (1 + generatingSeries c) * (1 - 2 * nonzeroSum c (generatingSeries c)) = 2 := by
  refine ⟨?_, (equation_iff c _).mpr (generating_fixed c hc)⟩
  rw [generating_fixed c hc, step_zero c hc]

private theorem polynomial_unique (c : ℕ) (hc : 2 ≤ c) (B : PowerSeries ℤ)
    (_h0 : constantCoeff B = 1)
    (hB : (1 + X) * (1 + B) * (1 - 2 * nonzeroSum c B) = 2) :
    B = generatingSeries c := by
  have hb := (equation_iff c B).mp hB
  have ha : ∀ d, Agree d B (generatingSeries c) := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← hb, ← generating_fixed c hc] using step_agree c hc ih
  ext n
  exact ha (n + 1) n (by omega)

private noncomputable def embed : PowerSeries ℤ →+* LaurentSeries ℚ :=
  (HahnSeries.ofPowerSeries ℤ ℚ).comp (PowerSeries.map (Int.castRingHom ℚ))

private theorem embed_coeff (A : PowerSeries ℤ) (N : ℕ) :
    (embed A).coeff (N : ℤ) = ((coeff N A : ℤ) : ℚ) := by
  change ((A.map (Int.castRingHom ℚ) : PowerSeries ℚ) : LaurentSeries ℚ).coeff (N : ℤ) = _
  simp only [LaurentSeries.coeff_coe_powerSeries, coeff_map, Int.coe_castRingHom]

private theorem embed_injective : Function.Injective embed := by
  intro A B h
  have hm : A.map (Int.castRingHom ℚ) = B.map (Int.castRingHom ℚ) :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ) h
  exact PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective hm

private theorem embed_inverse (A : PowerSeries ℤ) (hA : constantCoeff A = 1) :
    embed (invOfUnit A 1) = (embed A)⁻¹ := by
  apply Eq.symm
  apply inv_eq_of_mul_eq_one_left
  simpa only [map_mul, map_one] using congrArg embed (invOfUnit_mul A 1 hA)

noncomputable def laurentTerm (c : ℕ) (A : PowerSeries ℤ) (j : ℤ) : LaurentSeries ℚ :=
  let x := embed X
  let B := embed A
  x ^ j * B ^ j * (B ^ j + x) ^ ((c : ℤ) * j - 1) *
    (x ^ j + B) ^ ((c : ℤ) * j - 1)

private theorem negative_factorization {F : Type*} [Field F]
    (x u : F) (hx : x ≠ 0) (hu : u ≠ 0) (c k : ℕ) :
    x ^ (-(k : ℤ)) * u ^ (-(k : ℤ)) *
      (u ^ (-(k : ℤ)) + x) ^ (-((c * k + 1 : ℕ) : ℤ)) *
      (x ^ (-(k : ℤ)) + u) ^ (-((c * k + 1 : ℕ) : ℤ)) =
    x ^ (c * k ^ 2) * (u ^ (c * k ^ 2) *
      (1 + x * u ^ k)⁻¹ ^ (c * k + 1) * (1 + x ^ k * u)⁻¹ ^ (c * k + 1)) := by
  have hU : u ^ (-(k : ℤ)) + x = u ^ (-(k : ℤ)) * (1 + x * u ^ k) := by
    rw [zpow_neg, zpow_natCast]
    field_simp
  have hX : x ^ (-(k : ℤ)) + u = x ^ (-(k : ℤ)) * (1 + x ^ k * u) := by
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [hU, hX, mul_zpow, mul_zpow]
  have he : -(k : ℤ) + -(k : ℤ) * -((c * k + 1 : ℕ) : ℤ) = (c * k ^ 2 : ℕ) := by
    push_cast
    ring
  calc
    _ = (x ^ (-(k : ℤ)) * (x ^ (-(k : ℤ))) ^ (-((c * k + 1 : ℕ) : ℤ))) *
        (u ^ (-(k : ℤ)) * (u ^ (-(k : ℤ))) ^ (-((c * k + 1 : ℕ) : ℤ))) *
        (1 + x * u ^ k) ^ (-((c * k + 1 : ℕ) : ℤ)) *
        (1 + x ^ k * u) ^ (-((c * k + 1 : ℕ) : ℤ)) := by ring
    _ = _ := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← zpow_add₀ hu, he]
      simp only [zpow_natCast, zpow_neg, inv_pow]
      ring

private theorem laurent_normalization (c : ℕ) (hc : 2 ≤ c)
    (A : PowerSeries ℤ) (hA : constantCoeff A = 1) (j : ℤ) (hj : j ≠ 0) :
    laurentTerm c A j = embed (bilateralTerm c A j) := by
  have hx : embed X ≠ 0 := by
    intro he
    exact X_ne_zero (embed_injective (by simpa using he))
  have ha : embed A ≠ 0 := by
    intro he
    have hz : A = 0 := embed_injective (by simpa using he)
    simp [hz] at hA
  have hk : 0 < j.natAbs := by omega
  unfold bilateralTerm
  rw [if_neg hj]
  split_ifs with hp
  · have hjk : j = (j.natAbs : ℤ) := by omega
    have he : (c : ℤ) * j - 1 = ((c * j.natAbs - 1 : ℕ) : ℤ) := by
      conv_lhs => rw [hjk]
      rw [Nat.cast_sub (by nlinarith : 1 ≤ c * j.natAbs)]
      push_cast
      rfl
    simp only [laurentTerm, he]
    conv_lhs => rw [hjk]
    simp only [Int.natAbs_natCast, zpow_natCast, positiveTerm, map_mul, map_pow, map_add]
    ring
  · have hjk : j = -(j.natAbs : ℤ) := by omega
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

private theorem laurent_zero (c : ℕ) (A : PowerSeries ℤ) :
    laurentTerm c A 0 = (1 + embed X)⁻¹ * (1 + embed A)⁻¹ := by
  simp [laurentTerm]

private theorem laurent_window (c : ℕ) (hc : 2 ≤ c)
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

private theorem laurent_identity (c : ℕ) (hc : 2 ≤ c) :
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

theorem generating_equation (c : ℕ) (hc : 2 ≤ c) :
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

private theorem ofSeries_inverse (B : PowerSeries ℚ) (hB : constantCoeff B ≠ 0) :
    HahnSeries.ofPowerSeries ℤ ℚ (B⁻¹) = (HahnSeries.ofPowerSeries ℤ ℚ B)⁻¹ := by
  apply Eq.symm
  apply inv_eq_of_mul_eq_one_left
  simpa only [map_mul, map_one] using congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
    (PowerSeries.inv_mul_cancel B hB)

private theorem zeroTerm_series (c : ℕ) (A : PowerSeries ℤ) (hA : constantCoeff A = 1) :
    laurentTerm c A 0 = HahnSeries.ofPowerSeries ℤ ℚ
      ((1 + X)⁻¹ * (1 + A.map (Int.castRingHom ℚ))⁻¹) := by
  have ha : constantCoeff (1 + A.map (Int.castRingHom ℚ)) ≠ 0 := by
    rw [map_add, constantCoeff_one, ← coeff_zero_eq_constantCoeff, coeff_map,
      coeff_zero_eq_constantCoeff, hA]
    norm_num
  rw [map_mul, ofSeries_inverse _ (by simp), ofSeries_inverse _ ha, laurent_zero]
  simp only [embed, RingHom.comp_apply, map_add, map_one, map_X]

private theorem equation_of_laurent (c : ℕ) (hc : 2 ≤ c) (A : PowerSeries ℤ)
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

theorem generating_unique (c : ℕ) (hc : 2 ≤ c) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 1)
    (hB : ∀ N K : ℕ, N ≤ K →
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (laurentTerm c B j).coeff (N : ℤ)) =
        if N = 0 then (1 / 2 : ℚ) else 0) :
    B = generatingSeries c :=
  polynomial_unique c hc B h0 (equation_of_laurent c hc B h0 hB)

private theorem geometric_coeff (n : ℕ) : coeff n geometric = (-1 : ℤ) ^ n := by
  have hg : rescale (-1 : ℤ) (mk 1) * (1 + X) = 1 := by
    simpa using congrArg (rescale (-1 : ℤ)) (mk_one_mul_one_sub_eq_one ℤ)
  have he : geometric = rescale (-1 : ℤ) (mk 1) := by
    linear_combination rescale (-1 : ℤ) (mk 1) * geometric_spec - geometric * hg
  rw [he, coeff_rescale, coeff_mk]
  simp

private theorem coefficient_four_dvd (c : ℕ) (hc : 2 ≤ c) (n : ℕ) :
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

theorem hanna_conjecture_general (c : ℕ) (hc : 2 ≤ c) (n : ℕ) (hn : 0 < n) :
    a c n % 4 = 2 := by
  have hd := coefficient_four_dvd c hc n
  rw [map_sub, show (2 : PowerSeries ℤ) = C 2 from (map_ofNat C 2).symm,
    coeff_C_mul, geometric_coeff, coeff_one, if_neg (by omega : n ≠ 0), sub_zero] at hd
  obtain ⟨k, hk⟩ := hd
  rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] at hk <;> omega

theorem hanna_conjecture_a381362 (n : ℕ) (hn : 0 < n) : a 2 n % 4 = 2 :=
  hanna_conjecture_general 2 le_rfl n hn

theorem hanna_conjecture_a381363 (n : ℕ) (hn : 0 < n) : a 3 n % 4 = 2 :=
  hanna_conjecture_general 3 (by omega) n hn

#print axioms laurentTerm
#print axioms generating_equation
#print axioms hanna_conjecture_general
#print axioms hanna_conjecture_a381362
#print axioms hanna_conjecture_a381363
#print axioms bilateralTerm
#print axioms nonzeroSum
#print axioms finite_window
#print axioms a
#print axioms generatingSeries
#print axioms polynomial_form
#print axioms generating_unique

end D5.S1.Recurrence.Bilateral.BilateralProductModFour
