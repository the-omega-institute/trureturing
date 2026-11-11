/- GID: D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A positive coupled system proves all Hanna A382316 coefficients nonnegative. -/

/-
proof_shape: IsSourceSeries, claim, step, Equation: definitions, not proofs.
proof_shape: step_zero: bind-only; consumer: source_exists; escape_witness: none.
proof_shape: step_agree: bind-only; consumer: source_exists; escape_witness: none.
proof_shape: source_iff: bind-only; consumers: source_exists, result; escape_witness: none.
proof_shape: original_iff: bind-only; consumers: source_exists, result; escape_witness: none.
proof_shape: normalized_iff: bind-only; consumer: source_exists; escape_witness: none.
proof_shape: source_exists: bind-only; consumer: result; escape_witness: none.
proof_shape: coupled_of_normalized: bind-only; consumer: result; escape_witness: none.
proof_shape: coeff_mul_nonneg: bind-only; consumer: coupled_nonneg; escape_witness: none.
proof_shape: coupled_nonneg: content; consumer: result; escape_witness: none.
proof_shape: result: content, after expanding coupled_nonneg; escape_witness: none.
admission_basis: open-problem-resolution (#23937; Proved)
Direct frozen dependencies: step_agree uses UnitReversionSquareParity.Agree,
UnitReversionSquareParity.subst_outer_agree, UnitReversionSquareParity.agree_mul,
UnitReversionSquareParity.agree_pow, UnitReversionSquareParity.agree_X and
AbsoluteReciprocalGeometricParity.agree_inv; source_exists also uses
PowerSeriesNormalizedContraction.exists_unique_fixed; result uses these through source_exists.
The elaborated terms also mention AbsoluteReciprocalGeometricParity's private Agree predicate
through the type of agree_inv. Its declaration statement_id is
sha256:2ee8ed98da278ffd1ebd198b2092408351dcd0b50f49fa7c4d1de3e9724691b9.
All other declarations have no frozen D5 dependencies after helper expansion.
Declaration statement_id values from the existing Lean report; its three owner source hashes
match the current sources:
D5.S1.Recurrence.Invariants.UnitReversionSquareParity.subst_outer_agree:
sha256:c32c7154e0e2560fb0b2fb35f21abd75ea20fe528b93f1fa9e4d311e42eb984e.
D5.S1.Recurrence.Invariants.UnitReversionSquareParity.Agree:
sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34.
D5.S1.Recurrence.Invariants.UnitReversionSquareParity.agree_X:
sha256:cb4bbeb74f9bb4de6a237dc609532d94ac61147a4a3cd321ca192132b9b26215.
D5.S1.Recurrence.Invariants.UnitReversionSquareParity.agree_mul:
sha256:b4802ea85bb0964fd0f4727040613a738a00c26e68db4c758612d114939c9e3a.
D5.S1.Recurrence.Invariants.UnitReversionSquareParity.agree_pow:
sha256:0c9456bb3300b1f38308df2b3a2abc2d51d68b3b05356990e7bc5cfc4bfb0dbb.
D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_inv:
sha256:08ca54a1ff0f6dac6300f134bbfa5bd27fd9e2c7f64d37b46218787d9b012d97.
D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed:
sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26002.
The source predicate and claim retain the preregistered expressions; the positive coupled
system is used only inside the proof. Unbounded existence and coefficient induction require
no finite enumeration, checker, numeric reduction or certified finite instance.
-/

import Mathlib.RingTheory.LaurentSeries

import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaA382316CoefficientPositivity

open PowerSeries

/-- OEIS A382316 NAME and FORMULA (1), with the quotient in the Laurent-series field.
The normalization A(0) = 0 and A'(0) = 1 means coefficients 0 and 1 are 0 and 1. -/
def IsSourceSeries (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    (A : LaurentSeries ℚ) =
      (PowerSeries.subst (X ^ 2 : PowerSeries ℚ) A : LaurentSeries ℚ) +
        (PowerSeries.subst (X ^ 2 : PowerSeries ℚ) A : LaurentSeries ℚ) ^ 2 *
          (PowerSeries.subst (X ^ 3 : PowerSeries ℚ) A : LaurentSeries ℚ) /
            (PowerSeries.subst (X ^ 6 : PowerSeries ℚ) A : LaurentSeries ℚ)

/-- OEIS A382316 COMMENTS: “Conjecture: there are no negative terms.”
Existence is included because the generating series is specified implicitly. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsSourceSeries A) ∧
    ∀ A : PowerSeries ℚ, IsSourceSeries A →
      ∀ n : ℕ, 1 ≤ n → 0 ≤ coeff n A

end D5.S1.Recurrence.Invariants.HannaA382316CoefficientPositivity

namespace D5.S1.Recurrence.Invariants.HannaA382316CoefficientPositivity
open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

private noncomputable def step (f : PowerSeries ℚ) : PowerSeries ℚ :=
  X * f.subst (X ^ 2) + f.subst (X ^ 2) ^ 2 * f.subst (X ^ 3) *
    invOfUnit (f.subst (X ^ 6)) 1

private theorem step_zero (f : PowerSeries ℚ) (hf : constantCoeff f = 1) :
    constantCoeff (step f) = 1 := by
  simp [step, hf]

private theorem step_agree {d : ℕ} {f g : PowerSeries ℚ} (hd : 1 ≤ d)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (step f) (step g) := by
  have h2 := subst_outer_agree h (show (X : PowerSeries ℚ) ^ 2 ∣ X ^ 2 from dvd_rfl)
  have h3 := subst_outer_agree h (show (X : PowerSeries ℚ) ^ 2 ∣ X ^ 3 from pow_dvd_pow X (by omega))
  have h6 := subst_outer_agree h (show (X : PowerSeries ℚ) ^ 2 ∣ X ^ 6 from pow_dvd_pow X (by omega))
  have hf6 : constantCoeff (f.subst ((X : PowerSeries ℚ) ^ 6)) = 1 := by simpa using hf
  have hg6 : constantCoeff (g.subst ((X : PowerSeries ℚ) ^ 6)) = 1 := by simpa using hg
  have hi := D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_inv hf6 hg6 h6
  have hm := agree_mul (agree_mul (agree_pow h2 2) h3) hi
  have hx := agree_X h2
  intro n hn
  simp only [step, map_add, hx n (by omega), hm n (by omega)]

private def Equation (A : PowerSeries ℚ) : Prop :=
  A * A.subst (X ^ 6) = A.subst (X ^ 2) * A.subst (X ^ 6) +
    A.subst (X ^ 2) ^ 2 * A.subst (X ^ 3)

private theorem source_iff (A : PowerSeries ℚ) (h0 : constantCoeff A = 0)
    (h1 : coeff 1 A = 1) : IsSourceSeries A ↔ Equation A := by
  let b : PowerSeries ℚ := A.subst (X ^ 2)
  let c : PowerSeries ℚ := A.subst (X ^ 3)
  let e : PowerSeries ℚ := A.subst (X ^ 6)
  let ι : PowerSeries ℚ →+* LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ
  have he : e ≠ 0 := by
    intro hz
    have hh := congrArg (coeff 6) hz
    simp [e, coeff_subst_X_pow (by decide : 6 ≠ 0), h1] at hh
  have hie : ι e ≠ 0 := by
    intro hz
    exact he (HahnSeries.ofPowerSeries_injective (hz.trans (map_zero ι).symm))
  constructor
  · intro hA
    have hh : ι A = ι b + ι b ^ 2 * ι c / ι e := hA.2.2
    have hc : ι A * ι e = ι b * ι e + ι b ^ 2 * ι c := by
      rw [hh, add_mul, div_mul_cancel₀ _ hie]
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ))
    change ι (A * e) = ι (b * e + b ^ 2 * c)
    simpa only [map_mul, map_add, map_pow] using hc
  · intro hA
    have hc : ι A * ι e = ι b * ι e + ι b ^ 2 * ι c := by
      have hh := congrArg ι hA
      simpa only [map_mul, map_add, map_pow] using hh
    refine ⟨h0, h1, ?_⟩
    change ι A = ι b + ι b ^ 2 * ι c / ι e
    apply (sub_eq_iff_eq_add'.mp ?_)
    apply (eq_div_iff hie).mpr
    linear_combination hc

private theorem original_iff (f : PowerSeries ℚ) :
    Equation (X * f) ↔
    f * f.subst (X ^ 6) = X * f.subst (X ^ 2) * f.subst (X ^ 6) +
      f.subst (X ^ 2) ^ 2 * f.subst (X ^ 3) := by
  have s2 : HasSubst ((X : PowerSeries ℚ) ^ 2) := .X_pow (by decide)
  have s3 : HasSubst ((X : PowerSeries ℚ) ^ 3) := .X_pow (by decide)
  have s6 : HasSubst ((X : PowerSeries ℚ) ^ 6) := .X_pow (by decide)
  unfold Equation
  rw [subst_mul s2, subst_X s2, subst_mul s3, subst_X s3, subst_mul s6, subst_X s6]
  constructor
  · intro he
    apply X_pow_mul_injective (k := 7)
    linear_combination he
  · intro he
    linear_combination X ^ 7 * he

private theorem normalized_iff (f : PowerSeries ℚ) (hf : constantCoeff f = 1) :
    f = step f ↔
    f * f.subst (X ^ 6) = X * f.subst (X ^ 2) * f.subst (X ^ 6) +
      f.subst (X ^ 2) ^ 2 * f.subst (X ^ 3) := by
  have h6 : constantCoeff (f.subst ((X : PowerSeries ℚ) ^ 6)) = 1 := by simpa using hf
  have hi := invOfUnit_mul (f.subst (X ^ 6)) 1 h6
  have hu : IsUnit (f.subst ((X : PowerSeries ℚ) ^ 6)) :=
    isUnit_iff_constantCoeff.mpr (h6 ▸ isUnit_one)
  constructor
  · intro he
    calc
      f * f.subst (X ^ 6) = step f * f.subst (X ^ 6) := congrArg (fun t => t * f.subst (X ^ 6)) he
      _ = _ := by dsimp [step]; linear_combination f.subst (X ^ 2) ^ 2 * f.subst (X ^ 3) * hi
  · intro he
    apply hu.mul_right_cancel
    dsimp [step]
    linear_combination he - f.subst (X ^ 2) ^ 2 * f.subst (X ^ 3) * hi

private theorem source_exists : ∃ A : PowerSeries ℚ, IsSourceSeries A := by
  obtain ⟨f, hf, he, _⟩ := exists_unique_fixed step step_zero
    (fun hd hf hg h => step_agree hd hf hg h)
  refine ⟨X * f, (source_iff _ (by simp) (by simpa using hf)).mpr ?_⟩
  exact (original_iff f).mpr ((normalized_iff f hf).mp he)

private theorem coupled_of_normalized (f : PowerSeries ℚ) (hf : constantCoeff f = 1)
    (he : f * f.subst (X ^ 6) = X * f.subst (X ^ 2) * f.subst (X ^ 6) +
      f.subst (X ^ 2) ^ 2 * f.subst (X ^ 3)) :
    ∃ g : PowerSeries ℚ, constantCoeff g = 1 ∧
      f = f.subst (X ^ 2) * g ∧ g = X + f.subst (X ^ 2) * g.subst (X ^ 3) := by
  let g : PowerSeries ℚ := f * invOfUnit (f.subst (X ^ 2)) 1
  have hf2 : constantCoeff (f.subst ((X : PowerSeries ℚ) ^ 2)) = 1 := by simpa using hf
  have hf6 : constantCoeff (f.subst ((X : PowerSeries ℚ) ^ 6)) = 1 := by simpa using hf
  have hi := invOfUnit_mul (f.subst (X ^ 2)) 1 hf2
  have hfg : f = f.subst (X ^ 2) * g := by
    dsimp [g]
    linear_combination -f * hi
  have s2 : HasSubst ((X : PowerSeries ℚ) ^ 2) := .X_pow (by decide)
  have s3 : HasSubst ((X : PowerSeries ℚ) ^ 3) := .X_pow (by decide)
  have h23 : PowerSeries.subst ((X : PowerSeries ℚ) ^ 3)
      (PowerSeries.subst ((X : PowerSeries ℚ) ^ 2) f) =
      PowerSeries.subst ((X : PowerSeries ℚ) ^ 6) f := by
    rw [subst_comp_subst_apply s2 s3, subst_pow s3, subst_X s3]
    congr 1
    ring
  have hf3 : f.subst ((X : PowerSeries ℚ) ^ 3) = f.subst (X ^ 6) * g.subst (X ^ 3) := by
    have hh := congrArg (subst ((X : PowerSeries ℚ) ^ 3)) hfg
    simpa only [subst_mul s3, h23] using hh
  refine ⟨g, by simp [g, hf], hfg, ?_⟩
  have hu2 : IsUnit (f.subst ((X : PowerSeries ℚ) ^ 2)) :=
    isUnit_iff_constantCoeff.mpr (hf2 ▸ isUnit_one)
  have hu6 : IsUnit (f.subst ((X : PowerSeries ℚ) ^ 6)) :=
    isUnit_iff_constantCoeff.mpr (hf6 ▸ isUnit_one)
  apply hu2.mul_left_cancel
  apply hu6.mul_right_cancel
  linear_combination he - f.subst (X ^ 6) * hfg + f.subst (X ^ 2) ^ 2 * hf3

private theorem coeff_mul_nonneg (f g : PowerSeries ℚ) (n : ℕ)
    (hf : ∀ i ≤ n, 0 ≤ coeff i f) (hg : ∀ i ≤ n, 0 ≤ coeff i g) :
    0 ≤ coeff n (f * g) := by
  rw [coeff_mul]
  apply Finset.sum_nonneg
  intro p hp
  have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact mul_nonneg (hf p.1 (by omega)) (hg p.2 (by omega))

private theorem coupled_nonneg (f g : PowerSeries ℚ)
    (hf0 : constantCoeff f = 1) (hg0 : constantCoeff g = 1)
    (hf : f = f.subst (X ^ 2) * g)
    (hg : g = X + f.subst (X ^ 2) * g.subst (X ^ 3)) :
    ∀ n : ℕ, 0 ≤ coeff n f ∧ 0 ≤ coeff n g := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [coeff_zero_eq_constantCoeff, hf0, hg0]
    have hf2 (i : ℕ) (hi : i ≤ n) : 0 ≤ coeff i (f.subst ((X : PowerSeries ℚ) ^ 2)) := by
      rw [coeff_subst_X_pow (by decide : 2 ≠ 0)]
      split_ifs
      · simpa using (ih (i / 2) (by omega)).1
      · exact le_refl 0
    have hg3 (i : ℕ) (hi : i ≤ n) : 0 ≤ coeff i (g.subst ((X : PowerSeries ℚ) ^ 3)) := by
      rw [coeff_subst_X_pow (by decide : 3 ≠ 0)]
      split_ifs
      · simpa using (ih (i / 3) (by omega)).2
      · exact le_refl 0
    have hgn : 0 ≤ coeff n g := by
      have hh := congrArg (coeff n) hg
      rw [map_add] at hh
      rw [hh]
      apply add_nonneg
      · simp only [coeff_X]
        split_ifs <;> norm_num
      · exact coeff_mul_nonneg _ _ n hf2 hg3
    refine ⟨?_, hgn⟩
    have hfn := congrArg (coeff n) hf
    rw [hfn]
    apply coeff_mul_nonneg _ _ n hf2
    intro i hi
    by_cases hin : i = n
    · simpa [hin] using hgn
    · exact (ih i (by omega)).2

theorem result : D5.S1.Recurrence.Invariants.HannaA382316CoefficientPositivity.claim := by
  refine ⟨source_exists, ?_⟩
  intro A hA n hn
  obtain ⟨f, hAf⟩ := X_dvd_iff.mpr hA.1
  have hf0 : constantCoeff f = 1 := by
    have hh := hA.2.1
    rw [hAf] at hh
    simpa using hh
  have he := (original_iff f).mp (hAf ▸ (source_iff A hA.1 hA.2.1).mp hA)
  obtain ⟨g, hg0, hf, hg⟩ := coupled_of_normalized f hf0 he
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [hAf]
  simpa using (coupled_nonneg f g hf0 hg0 hf hg m).1


end D5.S1.Recurrence.Invariants.HannaA382316CoefficientPositivity
