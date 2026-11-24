/- GID: D5/S3/Arith/ModularForms/IncompleteKloostermanFourier
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform interval bound for the centered inverse-residue phase. -/

import D5.S3.Arith.ModularForms.RademacherKloostermanCoefficient
import D5.S3.CharacterSums.KloostermanSummability
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod

namespace D5.S3.Arith.ModularForms.IncompleteKloostermanFourier

open RademacherKloostermanCoefficient (sum_vacuumPhase_mul_residuePhase_eq_kloosterman)
open RademacherLinearCutoff (reducedResidues)
open RademacherPhaseRamanujan
  (negatedInverseResidue residuePhase vacuumPhase_eq_residuePhase_negatedInverse)
open RademacherVacuum (inverseResidue inverseResidue_spec vacuumPhase)
open D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase (kloosterman phase)
open D5.S3.CharacterSums.KloostermanSummability (norm_kloosterman_div_sq_le)

variable {c : ℕ} [NeZero c]

/-- The standard negative inverse phase on units, extended by zero to the other residues. -/
def nativePhase (c : ℕ) [NeZero c] (r : ZMod c) : ℂ :=
  if r.val.Coprime c then phase 0 (-1) r else 0

/-- Coprimality of the residue representative detects precisely the unit support. -/
theorem nativePhase_eq_if_isUnit (r : ZMod c) [Decidable (IsUnit r)] :
    nativePhase c r = if IsUnit r then ZMod.stdAddChar (-r⁻¹) else 0 := by
  have h : IsUnit r ↔ r.val.Coprime c := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.isUnit_iff_coprime r.val c
  by_cases hr : IsUnit r
  · simp only [nativePhase, ite_eq_left hr, ite_eq_left (h.mp hr), phase, zero_mul, zero_add, neg_one_mul]
  · rw [nativePhase, ite_eq_right hr, ite_eq_right (mt h.mpr hr)]

/-- The average of the native phase over a full period. -/
def phaseMean (c : ℕ) [NeZero c] : ℂ :=
  (∑ r : ZMod c, nativePhase c r) / (c : ℂ)

/-- The periodic phase with its average removed. -/
def centeredPhase (c : ℕ) [NeZero c] (r : ZMod c) : ℂ :=
  nativePhase c r - phaseMean c

/-- On a primitive denominator the native phase agrees with the vacuum phase. -/
theorem nativePhase_intCast_of_gcd_eq_one {d : ℤ} (hd : d.gcd (c : ℤ) = 1) :
    nativePhase c (d : ZMod c) = vacuumPhase (c : ℤ) d := by
  have hc : 0 < (c : ℤ) := by exact_mod_cast (NeZero.pos c)
  have hcoprime : (d : ZMod c).val.Coprime c := by
    rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast, ZMod.val_intCast, Int.gcd_emod]
    exact hd
  have hinv : (d : ZMod c) * (inverseResidue (c : ℤ) d : ZMod c) = 1 := by
    have h := (ZMod.intCast_eq_intCast_iff (d * inverseResidue (c : ℤ) d) 1 c).2
      (inverseResidue_spec hc ((Int.gcd_comm _ _).trans hd)).2.2
    simpa only [Int.cast_mul, Int.cast_one] using h
  have hneg : (negatedInverseResidue (c : ℤ) d : ZMod c) = -((d : ZMod c)⁻¹) := by
    rw [negatedInverseResidue, ZMod.intCast_mod, Int.cast_neg,
      ZMod.inv_eq_of_mul_eq_one c _ _ hinv]
  have hchar (a : ℤ) : residuePhase (c : ℤ) a = ZMod.stdAddChar (a : ZMod c) := by
    simp only [ZMod.stdAddChar_coe, residuePhase, Int.cast_natCast, div_eq_mul_inv, mul_assoc]
  rw [nativePhase, ite_eq_left hcoprime, vacuumPhase_eq_residuePhase_negatedInverse hc.ne',
    hchar, hneg]
  simp only [phase, zero_mul, zero_add, neg_one_mul]

/-- The sign in mathlib's forward DFT gives first coefficient `-m`. -/
theorem dft_nativePhase (m : ZMod c) :
    𝓕 (nativePhase c) m = kloosterman (-m) (-1) := by
  rw [ZMod.dft_apply]
  calc
    _ = ∑ r ∈ (Finset.univ : Finset (ZMod c)).filter (fun r => r.val.Coprime c),
        phase (-m) (-1) r := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : r.val.Coprime c
      · simp only [smul_eq_mul, nativePhase, ite_eq_left hr, phase, zero_mul, zero_add,
          neg_one_mul, ← AddChar.map_add_eq_mul]
        rw [mul_comm r m, neg_mul]
      · simp [nativePhase, hr]
    _ = ∑ r : {r : ZMod c // r.val.Coprime c}, phase (-m) (-1) r.val :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      rw [kloosterman]
      symm
      refine Fintype.sum_equiv (ZMod.unitsEquivCoprime (n := c)) _ _ fun u => ?_
      change phase (-m) ((-1 : (ZMod c)ˣ) : ZMod c) (u : ZMod c) =
        phase (-m) (-1) (u : ZMod c)
      rw [Units.coe_neg_one]

/-- The native mean is the vacuum residue sum divided by the modulus. -/
theorem phaseMean_eq_sum_vacuumPhase :
    phaseMean c = (∑ d ∈ reducedResidues (c : ℤ), vacuumPhase (c : ℤ) d) / (c : ℂ) := by
  have h := sum_vacuumPhase_mul_residuePhase_eq_kloosterman c 0
  simp only [zero_mul, residuePhase, Int.cast_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at h
  rw [phaseMean, ← ZMod.dft_apply_zero (nativePhase c), dft_nativePhase, neg_zero, h]

/-- Centering cancels the zero-frequency coefficient. -/
theorem dft_centeredPhase_zero : 𝓕 (centeredPhase c) 0 = 0 := by
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  rw [ZMod.dft_apply_zero]
  simp only [centeredPhase, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, phaseMean]
  field_simp [hc]
  rw [sub_self, mul_zero]

/-- The nonzero Fourier coefficients survive centering. -/
theorem dft_centeredPhase_of_ne_zero {m : ZMod c} (hm : m ≠ 0) :
    𝓕 (centeredPhase c) m = kloosterman (-m) (-1) := by
  have hsum : (∑ r : ZMod c, ZMod.stdAddChar (-(r * m))) = 0 := by
    have h := AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar c (neg_ne_zero.mpr hm))
    have harg (r : ZMod c) : (-m) * r = -(r * m) := by rw [neg_mul, mul_comm m r]
    simpa only [AddChar.mulShift_apply, harg] using h
  calc
    _ = 𝓕 (nativePhase c) m -
        (∑ r : ZMod c, ZMod.stdAddChar (-(r * m))) * phaseMean c := by
      simp only [ZMod.dft_apply, smul_eq_mul, centeredPhase, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul]
    _ = _ := by rw [hsum, zero_mul, sub_zero, dft_nativePhase]

/-- Fourier inversion with the zero frequency removed. -/
theorem centeredPhase_eq_sum (r : ZMod c) :
    centeredPhase c r = (c : ℂ)⁻¹ * ∑ m ∈ Finset.univ.erase (0 : ZMod c),
      ZMod.stdAddChar (m * r) * kloosterman (-m) (-1) := by
  have htrim :
      (∑ m : ZMod c, ZMod.stdAddChar (m * r) * 𝓕 (centeredPhase c) m) =
        ∑ m ∈ Finset.univ.erase (0 : ZMod c),
          ZMod.stdAddChar (m * r) * 𝓕 (centeredPhase c) m := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod c))
      (fun m => ZMod.stdAddChar (m * r) * 𝓕 (centeredPhase c) m) (Finset.mem_univ 0)
    simpa only [dft_centeredPhase_zero, mul_zero, add_zero] using h.symm
  calc
    _ = 𝓕⁻ (𝓕 (centeredPhase c)) r :=
      (congrFun (LinearEquiv.symm_apply_apply ZMod.dft (centeredPhase c)) r).symm
    _ = (c : ℂ)⁻¹ * ∑ m : ZMod c, ZMod.stdAddChar (m * r) * 𝓕 (centeredPhase c) m := by
      simpa only [smul_eq_mul] using ZMod.invDFT_apply (𝓕 (centeredPhase c)) r
    _ = _ := by
      rw [htrim]
      apply congrArg ((c : ℂ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro m hm
      rw [dft_centeredPhase_of_ne_zero (Finset.mem_erase.mp hm).1]

/-- At modulus one there are no nonzero frequencies. -/
theorem centeredPhase_one (r : ZMod 1) : centeredPhase 1 r = 0 := by
  have hs : (Finset.univ.erase (0 : ZMod 1)) = ∅ := by
    ext m
    simp [show m = 0 from Subsingleton.elim _ _]
  rw [centeredPhase_eq_sum, hs, Finset.sum_empty, mul_zero]

/-- The geometric sum over an integer interval of length `L` and left endpoint `A`. -/
theorem sum_stdAddChar_range_eq {m : ZMod c} (hm : m ≠ 0) (A : ℤ) (L : ℕ) :
    (∑ j ∈ Finset.range L, ZMod.stdAddChar (m * ((A + (j : ℤ) : ℤ) : ZMod c))) =
      ZMod.stdAddChar (m * (A : ZMod c)) *
        ((ZMod.stdAddChar m ^ L - 1) / (ZMod.stdAddChar m - 1)) := by
  have hz : ZMod.stdAddChar m ≠ 1 := by
    intro h
    apply hm
    exact ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm)
  have hterm (j : ℕ) :
      ZMod.stdAddChar (m * ((A + (j : ℤ) : ℤ) : ZMod c)) =
        ZMod.stdAddChar (m * (A : ZMod c)) * ZMod.stdAddChar m ^ j := by
    simp only [Int.cast_add, Int.cast_natCast, mul_add, AddChar.map_add_eq_mul]
    rw [show m * (j : ZMod c) = j • m by rw [nsmul_eq_mul, mul_comm],
      AddChar.map_nsmul_eq_pow]
  simp_rw [hterm]
  rw [← Finset.mul_sum, geom_sum_eq hz]

/-- The chord length is at least four times the distance from the normalized
frequency to the nearest integer. -/
theorem stdAddChar_chord_lower (m : ZMod c) :
    4 * ((min m.val (c - m.val) : ℕ) : ℝ) / (c : ℝ) ≤ ‖ZMod.stdAddChar m - 1‖ := by
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  let u : ℝ := (m.val : ℝ) / (c : ℝ)
  let v : ℝ := ((c - m.val : ℕ) : ℝ) / (c : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have huv : u + v = 1 := by
    dsimp [u, v]
    rw [Nat.cast_sub m.val_lt.le, ← add_div]
    rw [show (m.val : ℝ) + ((c : ℝ) - m.val) = (c : ℝ) by ring, div_self hc.ne']
  have hhalf (t : ℝ) (h₀ : 0 ≤ t) (h₁ : 2 * t ≤ 1) :
      2 * t ≤ Real.sin (Real.pi * t) := by
    have h := Real.le_sin_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h₀) h₁
    rwa [show Real.pi / 2 * (2 * t) = Real.pi * t by ring] at h
  have hsin : 2 * min u v ≤ Real.sin (Real.pi * u) := by
    by_cases h : u ≤ v
    · rw [min_eq_left h]
      exact hhalf u hu (by linarith)
    · rw [min_eq_right (le_of_not_ge h),
        show Real.pi * u = Real.pi - Real.pi * v by
          calc
            _ = Real.pi * (1 - v) := by rw [show u = 1 - v by linarith]
            _ = _ := by ring,
        Real.sin_pi_sub]
      exact hhalf v hv (by linarith)
  have hchar : ZMod.stdAddChar m =
      Complex.exp (Complex.I * ((2 * (Real.pi * u) : ℝ) : ℂ)) := by
    calc
      _ = ZMod.stdAddChar ((m.val : ℤ) : ZMod c) := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      _ = _ := by
        rw [ZMod.stdAddChar_coe]
        congr 1
        dsimp [u]
        push_cast
        ring
  rw [hchar, Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * (Real.pi * u) / 2 = Real.pi * u by ring, Real.norm_eq_abs]
  calc
    _ = 2 * (2 * min u v) := by
      dsimp [u, v]
      rw [min_div_div_right hc.le, ← Nat.cast_min]
      ring
    _ ≤ 2 * Real.sin (Real.pi * u) := mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ ≤ _ := le_abs_self _

private theorem norm_stdAddChar (m : ZMod c) : ‖ZMod.stdAddChar m‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- At a nonzero frequency the interval length drops out of the geometric sum bound. -/
theorem norm_sum_stdAddChar_range_le {m : ZMod c} (hm : m ≠ 0) (A : ℤ) (L : ℕ) :
    ‖∑ j ∈ Finset.range L, ZMod.stdAddChar (m * ((A + (j : ℤ) : ℤ) : ZMod c))‖ ≤
      ((c : ℝ) / 2) * (((min m.val (c - m.val) : ℕ) : ℝ)⁻¹) := by
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  have hdist : 0 < ((min m.val (c - m.val) : ℕ) : ℝ) := by
    exact_mod_cast (lt_min (ZMod.val_pos.mpr hm) (Nat.sub_pos_of_lt m.val_lt))
  have hnum : ‖ZMod.stdAddChar m ^ L - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖ZMod.stdAddChar m ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by norm_num [norm_pow, norm_stdAddChar]
  rw [sum_stdAddChar_range_eq hm, norm_mul, norm_stdAddChar, one_mul, norm_div]
  calc
    _ ≤ 2 / ‖ZMod.stdAddChar m - 1‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 2 / (4 * ((min m.val (c - m.val) : ℕ) : ℝ) / (c : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (stdAddChar_chord_lower m)
    _ = _ := by
      field_simp [hc.ne', hdist.ne']
      ring

private theorem sum_inv_val_le_harmonic :
    (∑ m : ZMod c, (m.val : ℝ)⁻¹) ≤ (harmonic c : ℝ) := by
  let e : ZMod c ↪ ℕ := ⟨ZMod.val, ZMod.val_injective c⟩
  have hsub : ((Finset.univ.erase (0 : ZMod c)).map e) ⊆ Finset.Icc 1 c := by
    intro j hj
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_of_lt (ZMod.val_pos.mpr (Finset.mem_erase.mp hm).1), m.val_lt.le⟩
  calc
    _ = ∑ j ∈ (Finset.univ.erase (0 : ZMod c)).map e, (j : ℝ)⁻¹ := by
      simp [e, Finset.sum_map]
    _ ≤ ∑ j ∈ Finset.Icc 1 c, (j : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := by simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem sum_inv_frequencyDistance_le :
    (∑ m ∈ Finset.univ.erase (0 : ZMod c), ((min m.val (c - m.val) : ℕ) : ℝ)⁻¹) ≤
      34 * (c : ℝ) ^ (1 / 16 : ℝ) := by
  have hc : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (show 1 ≤ c from NeZero.pos c)
  have hpow : 1 ≤ (c : ℝ) ^ (1 / 16 : ℝ) := Real.one_le_rpow hc (by norm_num)
  have hlog : Real.log c ≤ 16 * (c : ℝ) ^ (1 / 16 : ℝ) := by
    calc
      _ ≤ (c : ℝ) ^ (1 / 16 : ℝ) / (1 / 16 : ℝ) :=
        Real.log_natCast_le_rpow_div c (by norm_num)
      _ = _ := by ring
  have hharm : (harmonic c : ℝ) ≤ 17 * (c : ℝ) ^ (1 / 16 : ℝ) := by
    have h := harmonic_le_one_add_log c
    linarith
  calc
    _ ≤ ∑ m ∈ Finset.univ.erase (0 : ZMod c), ((m.val : ℝ)⁻¹ + ((-m).val : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [ZMod.neg_val, ite_eq_right (Finset.mem_erase.mp hm).1]
      by_cases h : m.val ≤ c - m.val
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
      · rw [min_eq_right (le_of_not_ge h)]
        exact le_add_of_nonneg_left (by positivity)
    _ ≤ ∑ m : ZMod c, ((m.val : ℝ)⁻¹ + ((-m).val : ℝ)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun _ _ _ => by positivity)
    _ = 2 * ∑ m : ZMod c, (m.val : ℝ)⁻¹ := by
      have hneg : (∑ m : ZMod c, ((-m).val : ℝ)⁻¹) = ∑ m : ZMod c, (m.val : ℝ)⁻¹ :=
        Fintype.sum_equiv (Equiv.neg (ZMod c)) _ _ (fun _ => rfl)
      rw [Finset.sum_add_distrib, hneg]
      ring
    _ ≤ 2 * (harmonic c : ℝ) :=
      mul_le_mul_of_nonneg_left sum_inv_val_le_harmonic (by norm_num)
    _ ≤ _ := by linarith

private theorem norm_kloosterman_le_power (a : ZMod c) :
    ‖kloosterman a (-1)‖ ≤ (4 : ℝ) ^ (4 ^ 8 : ℕ) * (c : ℝ) ^ (7 / 8 : ℝ) := by
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  calc
    _ ≤ ((4 : ℝ) ^ (4 ^ 8 : ℕ) * (c : ℝ) ^ (-(9 / 8) : ℝ)) * (c : ℝ) ^ 2 :=
      (div_le_iff₀ (pow_pos hc 2)).mp (norm_kloosterman_div_sq_le a (-1))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast (c : ℝ) 2, ← Real.rpow_add hc,
        show (-(9 / 8) : ℝ) + ((2 : ℕ) : ℝ) = 7 / 8 by norm_num]

/-- The centered interval sum as the sum of the nonzero Kloosterman coefficients
times their finite geometric sums. -/
theorem sum_centeredPhase_range_eq (A : ℤ) (L : ℕ) :
    (∑ j ∈ Finset.range L, centeredPhase c ((A + (j : ℤ) : ℤ) : ZMod c)) =
      (c : ℂ)⁻¹ * ∑ m ∈ Finset.univ.erase (0 : ZMod c),
        (∑ j ∈ Finset.range L, ZMod.stdAddChar (m * ((A + (j : ℤ) : ℤ) : ZMod c))) *
          kloosterman (-m) (-1) := by
  simp_rw [centeredPhase_eq_sum]
  rw [← Finset.mul_sum]
  apply congrArg ((c : ℂ)⁻¹ * ·)
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- A bound uniform in the starting point and length of the integer interval. -/
theorem norm_sum_centeredPhase_range_le (A : ℤ) (L : ℕ) :
    ‖∑ j ∈ Finset.range L, centeredPhase c ((A + (j : ℤ) : ℤ) : ZMod c)‖ ≤
      (17 * (4 : ℝ) ^ (4 ^ 8 : ℕ)) * (c : ℝ) ^ (15 / 16 : ℝ) := by
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  let s := Finset.univ.erase (0 : ZMod c)
  let g (m : ZMod c) :=
    ∑ j ∈ Finset.range L, ZMod.stdAddChar (m * ((A + (j : ℤ) : ℤ) : ZMod c))
  let f (m : ZMod c) := ((min m.val (c - m.val) : ℕ) : ℝ)⁻¹
  let K : ℝ := (4 : ℝ) ^ (4 ^ 8 : ℕ)
  rw [sum_centeredPhase_range_eq, norm_mul, norm_inv, Complex.norm_natCast]
  change (c : ℝ)⁻¹ * ‖∑ m ∈ s, g m * kloosterman (-m) (-1)‖ ≤
    17 * K * (c : ℝ) ^ (15 / 16 : ℝ)
  calc
    _ ≤ (c : ℝ)⁻¹ * ∑ m ∈ s, ‖g m * kloosterman (-m) (-1)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (c : ℝ)⁻¹ * ∑ m ∈ s,
        (((c : ℝ) / 2) * (K * (c : ℝ) ^ (7 / 8 : ℝ))) * f m := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      calc
        _ ≤ (((c : ℝ) / 2) * f m) * (K * (c : ℝ) ^ (7 / 8 : ℝ)) :=
          mul_le_mul (norm_sum_stdAddChar_range_le (Finset.mem_erase.mp hm).1 A L)
            (norm_kloosterman_le_power (-m)) (norm_nonneg _) (by dsimp [f]; positivity)
        _ = _ := by ac_rfl
    _ = (K * (c : ℝ) ^ (7 / 8 : ℝ)) / 2 * ∑ m ∈ s, f m := by
      rw [← Finset.mul_sum]
      field_simp [hc.ne']
    _ ≤ (K * (c : ℝ) ^ (7 / 8 : ℝ)) / 2 * (34 * (c : ℝ) ^ (1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left sum_inv_frequencyDistance_le (by dsimp [K]; positivity)
    _ = 17 * K * ((c : ℝ) ^ (7 / 8 : ℝ) * (c : ℝ) ^ (1 / 16 : ℝ)) := by
      generalize K = C
      ring
    _ = _ := by
      rw [← Real.rpow_add hc, show (7 / 8 : ℝ) + 1 / 16 = 15 / 16 by norm_num]

/-- A premise-free uniform bound for every finite consecutive integer interval
at every positive modulus, including modulus one. -/
theorem norm_sum_centeredPhase_Ico_le (c : ℕ) [NeZero c] (A B : ℤ) :
    ‖∑ d ∈ Finset.Ico A B, (nativePhase c (d : ZMod c) - phaseMean c)‖ ≤
      (17 * (4 : ℝ) ^ (4 ^ 8 : ℕ)) * (c : ℝ) ^ (15 / 16 : ℝ) := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simpa only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply, centeredPhase] using
    (norm_sum_centeredPhase_range_le (c := c) A (B - A).toNat)

end D5.S3.Arith.ModularForms.IncompleteKloostermanFourier
