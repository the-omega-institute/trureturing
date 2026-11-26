/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Exact conditional expansion and attained heralded recovery for the complementary depolarizing filter. -/

import D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor
import D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellKernelUpperBound
import D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound

/-!
# Exact Datta–Holevo filter benchmark

The filter comes from Datta–Holevo, arXiv:quant-ph/0510145, §3, (11) and (16).
The finite-reference coefficient is that of Hirche–George–Nuradha–Wilde,
arXiv:2608.27171v1, Eq. (2.42). The recovery result uses the scalar-identity
form of exact heralded recovery (Bény–Oreshkov, arXiv:1103.0649, Theorem 2).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark

open scoped _root_.Matrix BigOperators ComplexOrder MatrixOrder Kronecker
open RHLinalg (rtrace)
open FilteredChannelConditionalGap (filterAction)
open FilteredBellKernelProjection (filtered_channel_bell_upper_bound)
open SharpFilteredRecoveryFactor
open BellCenteredConditionalTraceGap (bellProjector)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act ratios)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight)
open UnitaryReconstruction.LiuWildChoiObstruction (bell diagonalVector outer)

open private trace_ratios_nonempty inverse_harmonic_pos from
  D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor

variable {A : Type} [Fintype A] [DecidableEq A]

private theorem sharpFilter_swap (a : ℝ) :
    (sharpFilter A a).reindex (Equiv.prodComm A A) (Equiv.prodComm A A) =
      sharpFilter A a := by
  have hbell (i j : A) : bell A (j, i) = bell A (i, j) := by
    simp [bell, diagonalVector, eq_comm]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap_prod_mk, sharpFilter, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, bellProjector, outer, Matrix.vecMulVec_apply, Pi.star_apply, hbell]
  simp only [Matrix.one_apply, Prod.mk.injEq, and_comm]

private theorem sharpFilter_inverse_marginal_left [Nonempty A]
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hd : 2 ≤ Fintype.card A) :
    (Fintype.card A : ℝ)⁻¹ • partialTraceLeft (sharpFilter A a)⁻¹ =
      (harmonicParameter (Fintype.card A) a)⁻¹ • (1 : Matrix A A ℂ) := by
  have hswap : ((sharpFilter A a)⁻¹).reindex
      (Equiv.prodComm A A) (Equiv.prodComm A A) = (sharpFilter A a)⁻¹ := by
    rw [← Matrix.inv_reindex, sharpFilter_swap]
  have htrace : partialTraceLeft (sharpFilter A a)⁻¹ =
      partialTraceRight (sharpFilter A a)⁻¹ := by
    calc
      _ = partialTraceRight (((sharpFilter A a)⁻¹).reindex
          (Equiv.prodComm A A) (Equiv.prodComm A A)) := rfl
      _ = _ := congrArg partialTraceRight hswap
  rw [htrace, sharpFilter_inverse_marginal a ha ha₁ hd]

/-- Eq. (2.42) for the Datta–Holevo filter on equal input and environment dimensions. -/
theorem sharp_family_expansion_eq
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hd : 2 ≤ Fintype.card A)
    (N : QuantumChannel A (A × A))
    (hN : ∀ X, act N X = filterAction (sharpFilter A a) X)
    (γ : ℝ) (hγ : 1 ≤ γ) (orth : Bool) :
    sInf (ratios N γ orth) = harmonicParameter (Fintype.card A) a := by
  let : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  let d : ℝ := Fintype.card A
  let h : ℝ := harmonicParameter d a
  have hh : h ≠ 0 := by
    have hpos := inverse_harmonic_pos a ha ha₁ hd
    change 0 < h⁻¹ at hpos
    intro hz
    simp [hz] at hpos
  have hinv : (h⁻¹ • (1 : Matrix A A ℂ))⁻¹ = h • (1 : Matrix A A ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hh, one_smul]
  have htrace : rtrace (h • (1 : Matrix A A ℂ)) / d = h := by
    change (Matrix.trace (h • (1 : Matrix A A ℂ))).re / d = h
    rw [Matrix.trace_smul, Complex.smul_re, Matrix.trace_one]
    simp [smul_eq_mul, d]
  have hup := filtered_channel_bell_upper_bound (sharpFilter A a)
    (sharpFilter_posDef a ha ha₁ hd) (sharpFilter_normalized a hd) N hN hd γ hγ orth
  rw [sharpFilter_inverse_marginal_left a ha ha₁ hd] at hup
  change sInf (ratios N γ orth) ≤ rtrace ((h⁻¹ • (1 : Matrix A A ℂ))⁻¹) / d at hup
  rw [hinv, htrace] at hup
  have hsets :=
    D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.result A (A × A) N
  have hratios : ratios N γ orth = ratios N 1 true := by
    have hfull := (hsets.2 γ 1 hγ le_rfl).trans (hsets.1 1 le_rfl)
    cases orth
    · exact hfull
    · exact (hsets.1 γ hγ).symm.trans hfull
  have hne : (ratios N γ orth).Nonempty := hratios.symm ▸ trace_ratios_nonempty N hd
  exact le_antisymm hup (le_csInf hne (fun _ hx =>
    sharp_family_ratio_lower_bound a ha ha₁ hd N hN γ orth hx))

open private bellCombination_inverse bell_complement_psd dimension_square_gt_one parameter_gt_a from
  D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor
open private injection injection_compress injection_expand from
  D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap

private theorem sharpFilter_inverse_effect_le_one [Nonempty A]
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hd : 2 ≤ Fintype.card A) :
    a • (sharpFilter A a)⁻¹ ≤ (1 : Matrix (A × A) (A × A) ℂ) := by
  let b := complementaryParameter (Fintype.card A) a
  have hab : a < b := parameter_gt_a a ha₁ (dimension_square_gt_one hd)
  have hb : 0 < b := ha.trans hab
  have hcoef : a * b⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hab.le (inv_nonneg.mpr hb.le)
    rwa [mul_inv_cancel₀ hb.ne'] at h
  apply sub_nonneg.mp
  change 0 ≤ 1 - a • (a • bellProjector A + b • (1 - bellProjector A))⁻¹
  rw [bellCombination_inverse a b ha.ne' hb.ne', smul_add, smul_smul, smul_smul,
    mul_inv_cancel₀ ha.ne', one_smul,
    show (1 : Matrix (A × A) (A × A) ℂ) -
        (bellProjector A + (a * b⁻¹) • (1 - bellProjector A)) =
        (1 - a * b⁻¹) • (1 - bellProjector A) from by
      rw [sub_smul, one_smul]
      abel]
  exact (bell_complement_psd.smul (sub_nonneg.mpr hcoef)).nonneg

/-- The inverse filter and coordinate slices attain success probability a. -/
theorem sharp_family_recovery_attains
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hd : 2 ≤ Fintype.card A)
    (N : QuantumChannel A (A × A))
    (hN : ∀ X, act N X = filterAction (sharpFilter A a) X) :
    a ∈ heraldedRecoveryProbabilities N := by
  let : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  let d : ℝ := Fintype.card A
  have hd₀ : d ≠ 0 := by
    dsimp only [d]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  let G := sharpFilter A a
  let S := CFC.sqrt G
  let P : A → Matrix (A × A) A ℂ := injection
  let K : A → Matrix A (A × A) ℂ := fun j => Real.sqrt a • ((P j)ᴴ * S⁻¹)
  have hG : G.PosDef := sharpFilter_posDef a ha ha₁ hd
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)).isHermitian
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  let : Invertible S := (isUnit_mul_self_iff.mp (hSS ▸ hG.isUnit)).invertible
  have hsqrt : Real.sqrt a * Real.sqrt a = a := by
    rw [← pow_two, Real.sq_sqrt ha.le]
  refine ⟨ha.le, ha₁.le, A, inferInstance, K, ?_, ?_⟩
  · have hsum : (∑ j, P j * (P j)ᴴ) = 1 := by
      simpa only [P, Matrix.mul_one, Matrix.one_kronecker_one] using
        (injection_expand (E := A) (1 : Matrix A A ℂ))
    calc
      (∑ j, (K j)ᴴ * K j) =
          ∑ j, a • (S⁻¹ * (P j * (P j)ᴴ) * S⁻¹) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [K, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, hS.inv.eq, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul, hsqrt, Matrix.mul_assoc]
      _ = a • (S⁻¹ * (∑ j, P j * (P j)ᴴ) * S⁻¹) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum, Matrix.mul_assoc]
      _ = a • G⁻¹ := by rw [hsum, Matrix.mul_one, ← Matrix.mul_inv_rev, hSS]
      _ ≤ 1 := sharpFilter_inverse_effect_le_one a ha ha₁ hd
  · intro X
    have hKS (j : A) : K j * S = Real.sqrt a • (P j)ᴴ := by
      simp only [K, Matrix.smul_mul, Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
        Matrix.mul_one]
    let T := X ⊗ₖ (1 : Matrix A A ℂ)
    have hslice (j : A) : (P j)ᴴ * T * P j = X := by
      change (injection (A := A) j)ᴴ * T * injection (A := A) j = X
      rw [injection_compress]
      ext i k
      simp [T]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, hN]
    change (∑ j, K j * (S * (d⁻¹ • T) * S) * (K j)ᴴ) = (a : ℂ) • X
    calc
      _ = ∑ j, (K j * S) * (d⁻¹ • T) * (K j * S)ᴴ := by
        simp only [Matrix.conjTranspose_mul, hS.eq, Matrix.mul_assoc]
      _ = ∑ _ : A, (a * d⁻¹) • X := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hKS, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hslice]
        congr 1
        calc
          Real.sqrt a * (d⁻¹ * Real.sqrt a) = (Real.sqrt a * Real.sqrt a) * d⁻¹ := by ring
          _ = a * d⁻¹ := by rw [hsqrt]
      _ = (a : ℂ) • X := by
        simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        change (d * (a * d⁻¹)) • X = _
        rw [show d * (a * d⁻¹) = a by
          calc
            _ = a * (d * d⁻¹) := by ring
            _ = a := by rw [mul_inv_cancel₀ hd₀, mul_one]]
        ext i j
        simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Maximum success probability for finite exact heralded recovery. -/
theorem sharp_family_recovery_sup_eq
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hd : 2 ≤ Fintype.card A)
    (N : QuantumChannel A (A × A))
    (hN : ∀ X, act N X = filterAction (sharpFilter A a) X) :
    sSup (heraldedRecoveryProbabilities N) = a := by
  let : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  have hmem := sharp_family_recovery_attains a ha ha₁ hd N hN
  have hup : ∀ p ∈ heraldedRecoveryProbabilities N, p ≤ a := by
    intro p hp
    rcases hp with ⟨hp₀, _, J, fJ, K, heffect, hrec⟩
    let := fJ
    exact sharp_family_recovery_upper_bound a ha ha₁ hd N hN K p hp₀ heffect hrec
  exact le_antisymm (csSup_le ⟨a, hmem⟩ hup) (le_csSup ⟨a, hup⟩ hmem)

#check sharp_family_expansion_eq
#check sharp_family_recovery_attains
#check sharp_family_recovery_sup_eq

#print axioms sharp_family_expansion_eq
#print axioms sharp_family_recovery_attains
#print axioms sharp_family_recovery_sup_eq

end D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark
