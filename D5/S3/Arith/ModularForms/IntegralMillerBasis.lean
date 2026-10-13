/- GID: D5/S3/Arith/ModularForms/IntegralMillerBasis
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/IntegralMillerBasis
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Constructed normalized integral Miller basis and full integer coefficient lattice. -/

import D5.S3.Arith.ModularForms.IntegralDiscriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries
open scoped BigOperators

namespace D5.S3.Arith.ModularForms

def MillerResidualWeight (s : ℕ) : Prop :=
  s = 0 ∨ s = 4 ∨ s = 6 ∨ s = 8 ∨ s = 10 ∨ s = 14

private def residualFourExponent (s : ℕ) : ℕ :=
  if s = 4 ∨ s = 10 then 1 else if s = 8 ∨ s = 14 then 2 else 0

private def residualSixExponent (s : ℕ) : ℕ :=
  if s = 6 ∨ s = 10 ∨ s = 14 then 1 else 0

private lemma residual_weight {s : ℕ} (hs : MillerResidualWeight s) :
    4 * residualFourExponent s + 6 * residualSixExponent s = s := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def eisensteinFourCoefficient (n : ℕ) : ℤ :=
  (if n = 0 then 1 else 0) + 240 * divisorPowerSum 3 n

private def eisensteinSixCoefficient (n : ℕ) : ℤ :=
  (if n = 0 then 1 else 0) - 504 * divisorPowerSum 5 n

private def integerPowerCoefficient (c : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | e + 1, n => integerConvolution (integerPowerCoefficient c e) c n

def rawMillerCoefficient (m s j n : ℕ) : ℤ :=
  integerConvolution (integerPowerCoefficient discriminantCoefficient (j + 1))
    (integerConvolution
      (integerPowerCoefficient eisensteinFourCoefficient
        (3 * (m - 1 - j) + residualFourExponent s))
      (integerPowerCoefficient eisensteinSixCoefficient (residualSixExponent s))) n

/-- Descending integer elimination, indexed by depth from the highest leading order. -/
def millerCoefficientDepth (m s d n : ℕ) : ℤ :=
  if d < m then
    rawMillerCoefficient m s (m - 1 - d) n -
      ∑ ell : Fin d, rawMillerCoefficient m s (m - 1 - d) (m - ell.val) *
        millerCoefficientDepth m s ell.val n
  else 0
termination_by d
decreasing_by exact ell.isLt

/-- Executable coefficient of the normalized integral Miller form with leading index j+1. -/
def millerCoefficient (m s j n : ℕ) : ℤ :=
  millerCoefficientDepth m s (m - 1 - j) n

noncomputable section

private lemma coefficient_integerConvolution (f g : PowerSeries ℤ) (n : ℕ) :
    (f * g).coeff n = integerConvolution (fun i => f.coeff i) (fun i => g.coeff i) n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

private lemma integerPowerCoefficient_correct (f : PowerSeries ℤ) (c : ℕ → ℤ)
    (hc : ∀ n, f.coeff n = c n) (e n : ℕ) :
    (f ^ e).coeff n = integerPowerCoefficient c e n := by
  induction e generalizing n with
  | zero => simp [integerPowerCoefficient, PowerSeries.coeff_one]
  | succ e ih =>
    rw [pow_succ, coefficient_integerConvolution]
    simp_rw [ih, hc]
    rfl

private def rawMillerSeries (m s j : ℕ) : PowerSeries ℤ :=
  integralDiscriminant ^ (j + 1) *
    (integralEisensteinFour ^ (3 * (m - 1 - j) + residualFourExponent s) *
      integralEisensteinSix ^ residualSixExponent s)

private lemma integralDiscriminant_coefficient (n : ℕ) :
    integralDiscriminant.coeff n = discriminantCoefficient n := by
  have h := discriminantCoefficient_correct n
  rw [← integralDiscriminant_map, PowerSeries.coeff_map] at h
  change ((integralDiscriminant.coeff n : ℤ) : ℂ) = (discriminantCoefficient n : ℂ) at h
  exact_mod_cast h

private lemma rawMillerSeries_coefficient (m s j n : ℕ) :
    (rawMillerSeries m s j).coeff n = rawMillerCoefficient m s j n := by
  have h4 (i : ℕ) : integralEisensteinFour.coeff i = eisensteinFourCoefficient i := by
    simp only [integralEisensteinFour, eisensteinFourCoefficient, map_add,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_one, divisorSeries, PowerSeries.coeff_mk]
  have h6 (i : ℕ) : integralEisensteinSix.coeff i = eisensteinSixCoefficient i := by
    simp only [integralEisensteinSix, eisensteinSixCoefficient, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_one, divisorSeries, PowerSeries.coeff_mk]
  simp only [rawMillerSeries, coefficient_integerConvolution]
  simp_rw [integerPowerCoefficient_correct integralDiscriminant _
    integralDiscriminant_coefficient,
    integerPowerCoefficient_correct integralEisensteinFour _ h4,
    integerPowerCoefficient_correct integralEisensteinSix _ h6]
  rfl

private lemma rawMiller_weight (m s : ℕ) (hs : MillerResidualWeight s) (j : Fin m) :
    12 + ((j.val : ℤ) * 12 +
      (((3 * (m - 1 - j.val) + residualFourExponent s : ℕ) : ℤ) * 4 +
        (residualSixExponent s : ℤ) * 6)) = (12 * m + s : ℕ) := by
  have ht : (m - 1 - j.val) + j.val + 1 = m := by omega
  have htZ : ((m - 1 - j.val : ℕ) : ℤ) + j.val + 1 = m := by exact_mod_cast ht
  have heZ : 4 * (residualFourExponent s : ℤ) +
      6 * (residualSixExponent s : ℤ) = s := by exact_mod_cast residual_weight hs
  push_cast
  omega

private def rawMillerForm (m s : ℕ) (hs : MillerResidualWeight s) (j : Fin m) :
    CuspForm 𝒮ℒ (12 * m + s : ℕ) :=
  CuspForm.mcast (rawMiller_weight m s hs j)
    (CuspForm.discriminant.mulModularForm
      (((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow j.val).mul
        ((E₄.pow (3 * (m - 1 - j.val) + residualFourExponent s)).mul
          (E₆.pow (residualSixExponent s)))))

private lemma rawMillerForm_qExpansion (m s : ℕ) (hs : MillerResidualWeight s) (j : Fin m) :
    qExpansion 1 (rawMillerForm m s hs j) =
      PowerSeries.map (Int.castRingHom ℂ) (rawMillerSeries m s j.val) := by
  change qExpansion 1 ((⇑CuspForm.discriminant) *
    ⇑(((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow j.val).mul
      ((E₄.pow (3 * (m - 1 - j.val) + residualFourExponent s)).mul
        (E₆.pow (residualSixExponent s))))) = _
  rw [ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
  simp only [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    CuspForm.coe_discriminant, rawMillerSeries, map_mul, map_pow,
    integralDiscriminant_map, integralEisensteinFour_map, integralEisensteinSix_map]
  have hd : qExpansion 1 (CuspForm.discriminant : ModularForm 𝒮ℒ 12) =
      qExpansion 1 ModularForm.discriminant := rfl
  rw [hd]
  ring

private lemma rawMillerForm_coefficient (m s : ℕ) (hs : MillerResidualWeight s)
    (j : Fin m) (n : ℕ) :
    (qExpansion 1 (rawMillerForm m s hs j)).coeff n =
      (rawMillerCoefficient m s j.val n : ℂ) := by
  rw [rawMillerForm_qExpansion, PowerSeries.coeff_map, rawMillerSeries_coefficient]
  rfl

private def millerFormDepth (m s : ℕ) (hs : MillerResidualWeight s) (d : ℕ) :
    CuspForm 𝒮ℒ (12 * m + s : ℕ) :=
  if hd : d < m then
    rawMillerForm m s hs ⟨m - 1 - d, by omega⟩ -
      ∑ ell : Fin d, (rawMillerCoefficient m s (m - 1 - d) (m - ell.val) : ℂ) •
        millerFormDepth m s hs ell.val
  else 0
termination_by d
decreasing_by exact ell.isLt

private def cuspCoefficientMap (k : ℤ) (n : ℕ) : CuspForm 𝒮ℒ k →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 f).coeff n
  map_add' f g := by
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
    exact map_add _ _ _
  map_smul' c f := by
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    exact PowerSeries.coeff_smul n _ c

private lemma millerFormDepth_coefficient (m s : ℕ) (hs : MillerResidualWeight s) (d n : ℕ) :
    (qExpansion 1 (millerFormDepth m s hs d)).coeff n =
      (millerCoefficientDepth m s d n : ℂ) := by
  induction d using Nat.strong_induction_on generalizing n with
  | h d ih =>
    rw [millerFormDepth, millerCoefficientDepth]
    by_cases hd : d < m
    · rw [dif_pos hd, if_pos hd]
      change cuspCoefficientMap (12 * m + s : ℕ) n
        (rawMillerForm m s hs ⟨m - 1 - d, by omega⟩ - _) = _
      rw [map_sub, map_sum]
      simp only [map_smul]
      change (qExpansion 1 (rawMillerForm m s hs ⟨m - 1 - d, by omega⟩)).coeff n -
        ∑ ell : Fin d, (rawMillerCoefficient m s (m - 1 - d) (m - ell.val) : ℂ) *
          (qExpansion 1 (millerFormDepth m s hs ell.val)).coeff n = _
      rw [rawMillerForm_coefficient]
      simp_rw [ih _ (Fin.isLt _) n]
      push_cast
      rfl
    · simp [hd, qExpansion_zero]

private lemma rawMillerForm_triangular (m s : ℕ) (hs : MillerResidualWeight s) (j : Fin m)
    (n : ℕ) (hn : n ≤ j.val + 1) :
    (qExpansion 1 (rawMillerForm m s hs j)).coeff n =
      if n = j.val + 1 then 1 else 0 := by
  let delta := qExpansion 1 ModularForm.discriminant
  let tail := PowerSeries.divXPowOrder delta
  have hd : delta = PowerSeries.X * tail := by
    simpa [delta, tail, ModularForm.discriminant_qExpansion_order] using
      (PowerSeries.X_pow_order_mul_divXPowOrder (f := delta)).symm
  have ht : tail.constantCoeff = 1 := by
    simp only [tail, PowerSeries.constantCoeff_divXPowOrder, delta,
      ModularForm.discriminant_qExpansion_order, ENat.toNat_one]
    exact ModularForm.discriminant_qExpansion_coeff_one
  have h4 : (qExpansion 1 E₄).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [← integralEisensteinFour_map, PowerSeries.coeff_map]
    change ((integralEisensteinFour.coeff 0 : ℤ) : ℂ) = 1
    simp [integralEisensteinFour, divisorSeries, divisorPowerSum]
  have h6 : (qExpansion 1 E₆).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [← integralEisensteinSix_map, PowerSeries.coeff_map]
    change ((integralEisensteinSix.coeff 0 : ℤ) : ℂ) = 1
    simp [integralEisensteinSix, divisorSeries, divisorPowerSum]
  let u : PowerSeries ℂ := tail ^ (j.val + 1) *
    (qExpansion 1 E₄ ^ (3 * (m - 1 - j.val) + residualFourExponent s) *
      qExpansion 1 E₆ ^ residualSixExponent s)
  have hu : u.constantCoeff = 1 := by simp [u, ht, h4, h6]
  have hg : qExpansion 1 (rawMillerForm m s hs j) = PowerSeries.X ^ (j.val + 1) * u := by
    rw [rawMillerForm_qExpansion]
    simp only [rawMillerSeries, map_mul, map_pow, integralDiscriminant_map,
      integralEisensteinFour_map, integralEisensteinSix_map]
    change delta ^ (j.val + 1) * _ = _
    rw [hd, mul_pow]
    simp only [u]
    ring
  rw [hg, PowerSeries.coeff_X_pow_mul']
  by_cases he : n = j.val + 1
  · subst n
    simpa using hu
  · have hlt : n < j.val + 1 := by omega
    simp [not_le.mpr hlt, he]

private lemma rawMillerCoefficient_triangular (m s : ℕ) (hs : MillerResidualWeight s)
    (j : Fin m) (n : ℕ) (hn : n ≤ j.val + 1) :
    rawMillerCoefficient m s j.val n = if n = j.val + 1 then 1 else 0 := by
  have h := rawMillerForm_triangular m s hs j n hn
  rw [rawMillerForm_coefficient] at h
  split_ifs with he <;> simp only [he, if_true, if_false] at h ⊢ <;> exact_mod_cast h

lemma millerCoefficientDepth_normalized (m s : ℕ) (hs : MillerResidualWeight s)
    (d : ℕ) (hd : d < m) (n : ℕ) (hn : 1 ≤ n ∧ n ≤ m) :
    millerCoefficientDepth m s d n = if n = m - d then 1 else 0 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rw [millerCoefficientDepth, if_pos hd]
    have hi (ell : Fin d) : millerCoefficientDepth m s ell.val n =
        if n = m - ell.val then 1 else 0 := ih ell.val ell.isLt (by omega)
    simp_rw [hi]
    by_cases hnd : n ≤ m - d
    · have hz : ∑ ell : Fin d, rawMillerCoefficient m s (m - 1 - d) (m - ell.val) *
          (if n = m - ell.val then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ell _
        have he : n ≠ m - ell.val := by have := ell.isLt; omega
        simp [he]
      rw [hz, sub_zero]
      have ht : m - 1 - d + 1 = m - d := by omega
      have hraw := rawMillerCoefficient_triangular m s hs
        ⟨m - 1 - d, by omega⟩ n (by dsimp; omega)
      simpa only [Fin.val_mk, ht] using hraw
    · let e : Fin d := ⟨m - n, by omega⟩
      have hsumm : ∑ ell : Fin d, rawMillerCoefficient m s (m - 1 - d) (m - ell.val) *
          (if n = m - ell.val then 1 else 0) = rawMillerCoefficient m s (m - 1 - d) n := by
        rw [Finset.sum_eq_single e]
        · have he : m - e.val = n := by dsimp [e]; omega
          simp [he]
        · intro ell _ hne
          have he : n ≠ m - ell.val := by
            intro he
            apply hne
            apply Fin.ext
            dsimp [e]
            have := ell.isLt
            omega
          simp [he]
        · simp
      rw [hsumm, sub_self]
      have he : n ≠ m - d := by omega
      simp [he]

private instance cuspFiniteDimensional (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) :=
  FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

private lemma miller_cusp_finrank (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s) :
    Module.finrank ℂ (CuspForm 𝒮ℒ (12 * m + s : ℕ)) = m := by
  rw [CuspForm.discriminantEquiv.finrank_eq]
  have hc : ((12 * m + s : ℕ) : ℤ) - 12 = (12 * (m - 1) + s : ℕ) := by
    push_cast
    omega
  rw [hc]
  apply Module.finrank_eq_of_rank_eq
  have he : Even (12 * (m - 1) + s) := by
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨6 * (m - 1), by omega⟩
    · exact ⟨6 * (m - 1) + 2, by omega⟩
    · exact ⟨6 * (m - 1) + 3, by omega⟩
    · exact ⟨6 * (m - 1) + 4, by omega⟩
    · exact ⟨6 * (m - 1) + 5, by omega⟩
    · exact ⟨6 * (m - 1) + 7, by omega⟩
  rw [ModularForm.dimension_level_one _ he]
  have hn : (if (12 * (m - 1) + s) ≡ 2 [MOD 12]
      then (12 * (m - 1) + s) / 12 else (12 * (m - 1) + s) / 12 + 1) = m := by
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Nat.ModEq, Nat.add_mod, Nat.add_div] <;> omega
  exact_mod_cast hn

def millerForm (m s : ℕ) (hs : MillerResidualWeight s) (j : Fin m) :
    CuspForm 𝒮ℒ (12 * m + s : ℕ) := millerFormDepth m s hs (m - 1 - j.val)

private lemma millerForm_normalized (m s : ℕ) (hs : MillerResidualWeight s) (i j : Fin m) :
    (qExpansion 1 (millerForm m s hs j)).coeff (i.val + 1) = if i = j then 1 else 0 := by
  rw [millerForm, millerFormDepth_coefficient,
    millerCoefficientDepth_normalized m s hs _ (by omega) _ (by omega)]
  have he : i.val + 1 = m - (m - 1 - j.val) ↔ i = j := by
    rw [Fin.ext_iff]
    have := i.isLt
    have := j.isLt
    omega
  simp [he]

private lemma millerForm_linearIndependent (m s : ℕ) (hs : MillerResidualWeight s) :
    LinearIndependent ℂ (millerForm m s hs) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (cuspCoefficientMap (12 * m + s : ℕ) (j.val + 1)) hc
  rw [map_sum, map_zero] at h
  simp only [map_smul] at h
  change (∑ i : Fin m, c i * (qExpansion 1 (millerForm m s hs i)).coeff (j.val + 1)) = 0 at h
  simp_rw [millerForm_normalized] at h
  simpa using h

def integralMillerBasis (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s) :
    Module.Basis (Fin m) ℂ (CuspForm 𝒮ℒ (12 * m + s : ℕ)) :=
  basisOfLinearIndependentOfCardEqFinrank' (millerForm m s hs)
    (millerForm_linearIndependent m s hs) (by simpa using (miller_cusp_finrank m s hm hs).symm)

lemma integralMillerBasis_apply (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (j : Fin m) : integralMillerBasis m s hm hs j = millerForm m s hs j := by
  simp [integralMillerBasis]

/-- The actual cusp-space equivalence, with coordinates equal to the first m coefficients. -/
def millerCoefficientEquiv (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s) :
    CuspForm 𝒮ℒ (12 * m + s : ℕ) ≃ₗ[ℂ] (Fin m → ℂ) :=
  (integralMillerBasis m s hm hs).equivFun

theorem millerCoefficientEquiv_apply (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (f : CuspForm 𝒮ℒ (12 * m + s : ℕ)) (j : Fin m) :
    millerCoefficientEquiv m s hm hs f j = (qExpansion 1 f).coeff (j.val + 1) := by
  have h := congrArg (cuspCoefficientMap (12 * m + s : ℕ) (j.val + 1))
    ((integralMillerBasis m s hm hs).sum_equivFun f)
  rw [map_sum] at h
  simp only [map_smul, integralMillerBasis_apply] at h
  change (∑ i : Fin m, millerCoefficientEquiv m s hm hs f i *
    (qExpansion 1 (millerForm m s hs i)).coeff (j.val + 1)) = _ at h
  simp_rw [millerForm_normalized] at h
  simpa [cuspCoefficientMap] using h

private lemma miller_reconstruction (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (f : CuspForm 𝒮ℒ (12 * m + s : ℕ)) :
    ∑ j : Fin m, (qExpansion 1 f).coeff (j.val + 1) • millerForm m s hs j = f := by
  have h := (integralMillerBasis m s hm hs).sum_equivFun f
  change (∑ j : Fin m, millerCoefficientEquiv m s hm hs f j •
    integralMillerBasis m s hm hs j) = f at h
  simpa only [millerCoefficientEquiv_apply, integralMillerBasis_apply] using h

theorem millerForm_coefficient (m s : ℕ) (hs : MillerResidualWeight s) (j : Fin m) (n : ℕ) :
    (qExpansion 1 (millerForm m s hs j)).coeff n = (millerCoefficient m s j.val n : ℂ) := by
  exact millerFormDepth_coefficient m s hs (m - 1 - j.val) n

/-- The normalized Miller form is uniquely determined inside the actual cusp space. -/
theorem millerForm_unique (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (j : Fin m) (f : CuspForm 𝒮ℒ (12 * m + s : ℕ))
    (hf : ∀ i : Fin m, (qExpansion 1 f).coeff (i.val + 1) = if i = j then 1 else 0) :
    f = millerForm m s hs j := by
  apply (millerCoefficientEquiv m s hm hs).injective
  ext i
  rw [millerCoefficientEquiv_apply, millerCoefficientEquiv_apply, millerForm_normalized]
  exact hf i

/-- All coefficients are integral exactly when the first m coefficients are integral. -/
theorem miller_integrality_iff (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (f : CuspForm 𝒮ℒ (12 * m + s : ℕ)) :
    (∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 f).coeff n = (z : ℂ)) ↔
      ∀ j : Fin m, ∃ z : ℤ, (qExpansion 1 f).coeff (j.val + 1) = (z : ℂ) := by
  constructor
  · intro h j
    exact h (j.val + 1)
  · intro h n
    classical
    let z : Fin m → ℤ := fun j => Classical.choose (h j)
    have hz (j : Fin m) : (qExpansion 1 f).coeff (j.val + 1) = (z j : ℂ) :=
      Classical.choose_spec (h j)
    refine ⟨∑ j : Fin m, z j * millerCoefficient m s j.val n, ?_⟩
    have hr := congrArg (cuspCoefficientMap (12 * m + s : ℕ) n)
      (miller_reconstruction m s hm hs f)
    rw [map_sum] at hr
    simp only [map_smul] at hr
    change (∑ j : Fin m, (qExpansion 1 f).coeff (j.val + 1) *
      (qExpansion 1 (millerForm m s hs j)).coeff n) = (qExpansion 1 f).coeff n at hr
    rw [← hr]
    simp_rw [hz, millerForm_coefficient]
    push_cast
    rfl


/-- Fewer than m initial coefficients do not determine all-coefficient integrality. -/
theorem miller_integrality_bound_sharp (m s : ℕ)
    (hs : MillerResidualWeight s) (r : ℕ) (hr : r < m) :
    ∃ f : CuspForm 𝒮ℒ (12 * m + s : ℕ),
      (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : ℤ, (qExpansion 1 f).coeff n = (z : ℂ)) ∧
        ¬ (∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 f).coeff n = (z : ℂ)) := by
  let j : Fin m := ⟨r, hr⟩
  let f := (2 : ℂ)⁻¹ • millerForm m s hs j
  have hc (i : Fin m) : (qExpansion 1 f).coeff (i.val + 1) =
      (2 : ℂ)⁻¹ * (if i = j then 1 else 0) := by
    change cuspCoefficientMap (12 * m + s : ℕ) (i.val + 1)
      ((2 : ℂ)⁻¹ • millerForm m s hs j) = _
    rw [map_smul]
    change (2 : ℂ)⁻¹ * (qExpansion 1 (millerForm m s hs j)).coeff (i.val + 1) = _
    rw [millerForm_normalized]
  refine ⟨f, ?_, ?_⟩
  · intro n hn hnr
    let i : Fin m := ⟨n - 1, by omega⟩
    have hi : i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [i, j] at hv
      omega
    have he : i.val + 1 = n := by dsimp [i]; omega
    refine ⟨0, ?_⟩
    simpa only [he, if_neg hi, mul_zero, Int.cast_zero] using hc i
  · intro h
    obtain ⟨z, hz⟩ := h (r + 1)
    have hj : (qExpansion 1 f).coeff (r + 1) = (2 : ℂ)⁻¹ := by
      simpa only [j, Fin.val_mk, if_true, mul_one] using hc j
    have hz' : (2 : ℂ)⁻¹ = (z : ℂ) := hj.symm.trans hz
    have hmultip : (2 : ℂ) * (z : ℂ) = 1 := by
      rw [← hz']
      norm_num
    have hzint : (2 : ℤ) * z = 1 := by exact_mod_cast hmultip
    omega

/-- The full coefficient lattice of actual level-one cusp forms. -/
def integralCuspLattice (k : ℤ) : Submodule ℤ (CuspForm 𝒮ℒ k) where
  carrier := {f | ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 f).coeff n = (z : ℂ)}
  zero_mem' := by
    intro n
    refine ⟨0, ?_⟩
    change cuspCoefficientMap k n 0 = (0 : ℤ)
    simp
  add_mem' := by
    intro f g hf hg n
    obtain ⟨z, hz⟩ := hf n
    obtain ⟨w, hw⟩ := hg n
    refine ⟨z + w, ?_⟩
    change cuspCoefficientMap k n (f + g) = _
    rw [map_add]
    change (qExpansion 1 f).coeff n + (qExpansion 1 g).coeff n = _
    rw [hz, hw, Int.cast_add]
  smul_mem' := by
    intro a f hf n
    obtain ⟨z, hz⟩ := hf n
    refine ⟨a * z, ?_⟩
    change cuspCoefficientMap k n (a • f) = _
    rw [map_zsmul]
    change a • (qExpansion 1 f).coeff n = _
    rw [hz, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Int.cast_mul]

private def millerIntegerReconstructionMap (m s : ℕ) (hs : MillerResidualWeight s) :
    (Fin m → ℤ) →ₗ[ℤ] CuspForm 𝒮ℒ (12 * m + s : ℕ) where
  toFun z := ∑ j : Fin m, (z j : ℂ) • millerForm m s hs j
  map_add' z w := by
    simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_smul, Finset.smul_sum,
      Int.cast_smul_eq_zsmul, RingHom.id_apply]

private lemma millerIntegerReconstruction_coefficient (m s : ℕ)
    (hs : MillerResidualWeight s) (z : Fin m → ℤ) (n : ℕ) :
    (qExpansion 1 (millerIntegerReconstructionMap m s hs z)).coeff n =
      (∑ j : Fin m, z j * millerCoefficient m s j.val n : ℤ) := by
  change cuspCoefficientMap (12 * m + s : ℕ) n
    (∑ j : Fin m, (z j : ℂ) • millerForm m s hs j) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ j : Fin m, (z j : ℂ) * (qExpansion 1 (millerForm m s hs j)).coeff n) = _
  simp_rw [millerForm_coefficient]
  push_cast
  rfl

private lemma millerIntegerReconstruction_first (m s : ℕ) (hs : MillerResidualWeight s)
    (z : Fin m → ℤ) (j : Fin m) :
    (qExpansion 1 (millerIntegerReconstructionMap m s hs z)).coeff (j.val + 1) =
      (z j : ℂ) := by
  change cuspCoefficientMap (12 * m + s : ℕ) (j.val + 1)
    (∑ i : Fin m, (z i : ℂ) • millerForm m s hs i) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ i : Fin m, (z i : ℂ) *
    (qExpansion 1 (millerForm m s hs i)).coeff (j.val + 1)) = _
  simp_rw [millerForm_normalized]
  simp

private def millerIntegerLatticeMap (m s : ℕ) (hs : MillerResidualWeight s) :
    (Fin m → ℤ) →ₗ[ℤ] integralCuspLattice (12 * m + s : ℕ) :=
  (millerIntegerReconstructionMap m s hs).codRestrict _ (by
    intro z n
    exact ⟨∑ j : Fin m, z j * millerCoefficient m s j.val n,
      millerIntegerReconstruction_coefficient m s hs z n⟩)

private lemma millerIntegerLatticeMap_bijective (m s : ℕ) (hm : 1 ≤ m)
    (hs : MillerResidualWeight s) : Function.Bijective (millerIntegerLatticeMap m s hs) := by
  constructor
  · intro z w h
    funext j
    have hj := congrArg (fun f : integralCuspLattice (12 * m + s : ℕ) =>
      (qExpansion 1 f.val).coeff (j.val + 1)) h
    change (qExpansion 1 (millerIntegerReconstructionMap m s hs z)).coeff (j.val + 1) =
      (qExpansion 1 (millerIntegerReconstructionMap m s hs w)).coeff (j.val + 1) at hj
    rw [millerIntegerReconstruction_first, millerIntegerReconstruction_first] at hj
    exact_mod_cast hj
  · intro f
    classical
    let z : Fin m → ℤ := fun j => Classical.choose (f.property (j.val + 1))
    have hz (j : Fin m) : (qExpansion 1 f.val).coeff (j.val + 1) = (z j : ℂ) :=
      Classical.choose_spec (f.property (j.val + 1))
    refine ⟨z, Subtype.ext ?_⟩
    change (∑ j : Fin m, (z j : ℂ) • millerForm m s hs j) = f.val
    simpa only [← hz] using miller_reconstruction m s hm hs f.val

/-- Integer Miller coordinates give the entire integral coefficient lattice. -/
def millerIntegerLatticeEquiv (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s) :
    (Fin m → ℤ) ≃ₗ[ℤ] integralCuspLattice (12 * m + s : ℕ) :=
  LinearEquiv.ofBijective (millerIntegerLatticeMap m s hs)
    (millerIntegerLatticeMap_bijective m s hm hs)

/-- The inverse integer coordinates are precisely the first m actual coefficients. -/
theorem millerIntegerLatticeEquiv_symm_coefficient (m s : ℕ) (hm : 1 ≤ m)
    (hs : MillerResidualWeight s) (f : integralCuspLattice (12 * m + s : ℕ))
    (j : Fin m) :
    ((millerIntegerLatticeEquiv m s hm hs).symm f j : ℂ) =
      (qExpansion 1 f.val).coeff (j.val + 1) := by
  let e := millerIntegerLatticeEquiv m s hm hs
  have he := congrArg (fun g : integralCuspLattice (12 * m + s : ℕ) =>
    (qExpansion 1 g.val).coeff (j.val + 1)) (e.apply_symm_apply f)
  change (qExpansion 1 (millerIntegerReconstructionMap m s hs (e.symm f))).coeff
    (j.val + 1) = _ at he
  rw [millerIntegerReconstruction_first] at he
  exact he

end
end D5.S3.Arith.ModularForms

#print axioms D5.S3.Arith.ModularForms.millerCoefficientDepth
#print axioms D5.S3.Arith.ModularForms.millerCoefficient
#print axioms D5.S3.Arith.ModularForms.millerForm
#print axioms D5.S3.Arith.ModularForms.integralMillerBasis
#print axioms D5.S3.Arith.ModularForms.millerCoefficientEquiv
#print axioms D5.S3.Arith.ModularForms.millerCoefficientEquiv_apply
#print axioms D5.S3.Arith.ModularForms.millerForm_coefficient
#print axioms D5.S3.Arith.ModularForms.millerForm_unique
#print axioms D5.S3.Arith.ModularForms.miller_integrality_iff
#print axioms D5.S3.Arith.ModularForms.miller_integrality_bound_sharp
#print axioms D5.S3.Arith.ModularForms.integralCuspLattice
#print axioms D5.S3.Arith.ModularForms.millerIntegerLatticeEquiv
#print axioms D5.S3.Arith.ModularForms.millerIntegerLatticeEquiv_symm_coefficient
