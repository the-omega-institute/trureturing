/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualIterateSum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualIterateSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The dual iterate sum agrees with the finite native BPZ contraction. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualIteratePairing
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! Finite contraction of paired BPZ source-iterate coefficients. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeAllStateReconstruction (mu)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeDualCoefficients (sourceLOne_pow_eq_zero_of_lt)
open P48qNativeDualIteratePairing (sum_range_iterate_simplex_reindex)
open P48qNativeDualLinearField (dualField)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private restrictedDualJacobi_iterate_reindex from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualIteratePairing
open private sourceLOne_pow_weight from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "C" => HVertexOperator.coeff

private theorem sum_range_eq_of_cutoffs (a b : ℕ) (F : ℕ → ℂ)
    (ha : ∀ k ≥ a, F k = 0) (hb : ∀ k ≥ b, F k = 0) :
    (∑ k ∈ Finset.range a, F k) = ∑ k ∈ Finset.range b, F k := by
  rcases le_total a b with hab | hba
  · apply Finset.sum_subset (Finset.range_mono hab)
    intro k _ hk
    exact ha k (Nat.le_of_not_lt fun h => hk (Finset.mem_range.mpr h))
  · symm
    apply Finset.sum_subset (Finset.range_mono hba)
    intro k _ hk
    exact hb k (Nat.le_of_not_lt fun h => hk (Finset.mem_range.mpr h))

set_option maxHeartbeats 2000000 in
/-- The paired right-hand dual iterate sum equals the signed native iterate sum. -/
theorem gradedPairing_dualField_iterate_sum
    (a b : NativeStates) (d e : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hb : L₀ b = (e : ℂ) • b)
    (N : ℕ) (hN : d + e ≤ N)
    (s t p q n : ℤ) (f : RestrictedDual) (v : State) :
    let pNative (i : ℕ) : ℤ := -p + 2 * (d : ℤ) - (i : ℤ) - 2 - n
    let qNative (l : ℕ) : ℤ := -q + 2 * (e : ℤ) - (l : ℤ) - 2 - n
    let T : Module.End ℂ State :=
      ∑ i ∈ Finset.range (d + 1), (i.factorial : ℂ)⁻¹ •
        ∑ l ∈ Finset.range (e + 1), (l.factorial : ℂ)⁻¹ •
          ∑ h ∈ Finset.range ((N : ℤ) - n).toNat,
            Ring.choose ((pNative i : ℂ) - (s : ℂ) / 3) h •
              C (nativeField
                  (mu lattice ((L₁ ^ i) a) (n + (h : ℤ)) ((L₁ ^ l) b)))
                (s + t - 3 * (pNative i + qNative l - (h : ℤ) + 1))
    gradedPairing
      ((∑ j ∈ Finset.range ((N : ℤ) - n).toNat,
        Ring.choose ((p : ℂ) - ((-s : ℤ) : ℂ) / 3) j •
          C (dualField (mu lattice a (n + (j : ℤ)) b))
            (-s + -t - 3 * (p + q - (j : ℤ) + 1))) f) v =
      (-epsilon n * ((-1 : ℂ) ^ d * (-1 : ℂ) ^ e)) * gradedPairing f (T v) := by
  classical
  intro pNative qNative T
  let H : ℕ := ((N : ℤ) - n).toNat
  let K : ℕ := ((d : ℤ) + (e : ℤ) - n).toNat
  let M : ℂ := (p : ℂ) - ((-s : ℤ) : ℂ) / 3
  let B (i : ℕ) : ℂ := 2 * (d : ℂ) - (n : ℂ) - (i : ℂ) - 2
  let phase : ℂ := epsilon ((d : ℤ) + (e : ℤ) - 1 - n)
  let kTarget (j : ℕ) : ℤ := -s + -t - 3 * (p + q - (j : ℤ) + 1)
  let kNative (i l h : ℕ) : ℤ := s + t - 3 * (pNative i + qNative l - (h : ℤ) + 1)
  let target (j : ℕ) : ℂ :=
    Ring.choose M j *
      gradedPairing (C (dualField (mu lattice a (n + (j : ℤ)) b)) (kTarget j) f) v
  let F (i l h : ℕ) : ℂ :=
    (i.factorial : ℂ)⁻¹ * ((l.factorial : ℂ)⁻¹ *
      gradedPairing f
        (C (nativeField (mu lattice ((L₁ ^ i) a) (n + (h : ℤ)) ((L₁ ^ l) b)))
          (kNative i l h) v))
  let G (i l j u : ℕ) : ℂ :=
    Ring.choose M j * (((-1 : ℂ) ^ j * Ring.choose (B i - (j : ℂ)) u) * F i l (j + u))
  let nativeTerm (i l h : ℕ) : ℂ :=
    Ring.choose ((pNative i : ℂ) - (s : ℂ) / 3) h * F i l h

  have hKH : K ≤ H := by
    dsimp only [K, H]
    omega
  have hTargetTail (j : ℕ) (hj : K ≤ j) : target j = 0 := by
    have hneg : (d : ℤ) + (e : ℤ) < n + (j : ℤ) + 1 := by
      dsimp only [K] at hj
      omega
    have hz := sourceMu_eq_zero_of_weight_lt_mode_succ a b d e ha hb
      (n + (j : ℤ)) hneg
    simp only [target, hz, map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero]

  have hDivided (i l : ℕ) (m : ℤ) :
      mu lattice (dividedTranslation L₁ i a) m (dividedTranslation L₁ l b) =
        (i.factorial : ℂ)⁻¹ • ((l.factorial : ℂ)⁻¹ •
          mu lattice ((L₁ ^ i) a) m ((L₁ ^ l) b)) := by
    simp only [mu, dividedTranslation, map_smul, Pi.smul_apply, LinearMap.smul_apply]
    exact smul_comm _ _ _
  have hFold (i l h : ℕ) :
      gradedPairing f
        (C (nativeField (mu lattice (dividedTranslation L₁ i a)
          (n + (h : ℤ)) (dividedTranslation L₁ l b))) (kNative i l h) v) = F i l h := by
    rw [hDivided]
    simp only [F, map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul]

  have hInv : (-1 : ℂ)⁻¹ = -1 := by norm_num
  have hEpsAdd (x y : ℤ) : epsilon (x + y) = epsilon x * epsilon y :=
    zpow_add₀ (by norm_num) x y
  have hEpsNeg (x : ℤ) : epsilon (-x) = epsilon x := by
    unfold epsilon
    rw [zpow_neg, ← inv_zpow, hInv]
  have hEpsNat (m : ℕ) : epsilon (m : ℤ) = (-1 : ℂ) ^ m :=
    zpow_natCast _ _
  have hPhase : phase = -epsilon n * ((-1 : ℂ) ^ d * (-1 : ℂ) ^ e) := by
    change epsilon ((d : ℤ) + (e : ℤ) - 1 - n) = _
    have he : (d : ℤ) + (e : ℤ) - 1 - n =
        ((-1 : ℤ) + -n) + ((d : ℤ) + (e : ℤ)) := by omega
    have hm : epsilon (-1) = -1 := by
      simp only [epsilon, zpow_neg_one, hInv]
    rw [he, hEpsAdd, hEpsAdd (-1) (-n), hEpsAdd (d : ℤ) (e : ℤ),
      hEpsNeg n, hEpsNat d, hEpsNat e, hm, neg_one_mul]

  have castChoose (z : ℤ) (u : ℕ) : integerBinomial z u = Ring.choose (z : ℂ) u :=
    Ring.map_choose (Int.castRingHom ℂ) z u
  have hBPZ (j : ℕ) (hj : j < K) :
      target j = phase * (∑ r ∈ Finset.range (K - j),
        ∑ i ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r - i + 1),
          G i l j (r - i - l)) := by
    have hNonneg : 0 ≤ (d : ℤ) + (e : ℤ) - n := by
      dsimp only [K] at hj
      omega
    have hK : (K : ℤ) = (d : ℤ) + (e : ℤ) - n := Int.toNat_of_nonneg hNonneg
    have hm : n + (j : ℤ) + 1 ≤ (d : ℤ) + (e : ℤ) := by omega
    have hD : ((d : ℤ) + (e : ℤ) - (n + (j : ℤ)) - 1).toNat = K - j - 1 := by
      omega
    have hDcast : ((K - j - 1 : ℕ) : ℤ) = (d : ℤ) + (e : ℤ) - n - (j : ℤ) - 1 := by
      omega
    have hSign : (-1 : ℂ) ^ (K - j - 1) = phase * (-1 : ℂ) ^ j := by
      change _ = epsilon ((d : ℤ) + (e : ℤ) - 1 - n) * _
      rw [← hEpsNat (K - j - 1), hDcast,
        show (d : ℤ) + (e : ℤ) - n - (j : ℤ) - 1 =
          ((d : ℤ) + (e : ℤ) - 1 - n) + -(j : ℤ) by omega,
        hEpsAdd, hEpsNeg (j : ℤ), hEpsNat j]
    have hCoeff := gradedPairing_dualField_inverted_iterate_coeff a b d e ha hb
      (n + (j : ℤ)) (kTarget j) hm f v
    dsimp only at hCoeff
    rw [hD] at hCoeff
    dsimp only [target]
    rw [hCoeff, hSign, show K - j - 1 + 1 = K - j by omega]
    simp only [Finset.mul_sum, G]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro l hl
    have hir : i < r + 1 := Finset.mem_range.mp hi
    have hlr : l < r - i + 1 := Finset.mem_range.mp hl
    have hIndex :
        n + (j : ℤ) + (r : ℤ) - (i : ℤ) - (l : ℤ) =
          n + ((j + (r - i - l) : ℕ) : ℤ) := by omega
    have hCover :
        -kTarget j - 6 * ((K - j - 1 : ℕ) : ℤ) + 3 * (r : ℤ) =
          kNative i l (j + (r - i - l)) := by
      dsimp only [kTarget, kNative, pNative, qNative]
      omega
    have hTop :
        ((2 * (d : ℤ) - (n + (j : ℤ)) - (i : ℤ) - 2 : ℤ) : ℂ) =
          B i - (j : ℂ) := by
      simp only [B, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
      ring
    rw [hIndex, hCover, hFold, castChoose, hTop]
    ring

  have hChooseShift (i : ℕ) : B i - M = (pNative i : ℂ) - (s : ℂ) / 3 := by
    simp only [B, M, pNative, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast,
      Int.cast_ofNat]
    ring

  have hLeftZero (i l h : ℕ) (hi : d < i) : F i l h = 0 := by
    have hz := sourceLOne_pow_eq_zero_of_lt a d ha i hi
    simp only [F, hz, mu, map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero]
  have hRightZero (i l h : ℕ) (hl : e < l) : F i l h = 0 := by
    have hz := sourceLOne_pow_eq_zero_of_lt b e hb l hl
    simp only [F, hz, mu, map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero]
  have hNativeTail (i l h : ℕ) (hcut : K ≤ i + l + h) : F i l h = 0 := by
    by_cases hi : i ≤ d
    · by_cases hl : l ≤ e
      · have hai : L₀ ((L₁ ^ i) a) = ((d - i : ℕ) : ℂ) • (L₁ ^ i) a := by
          rw [Nat.cast_sub hi]
          exact sourceLOne_pow_weight a (d : ℂ) ha i
        have hbl : L₀ ((L₁ ^ l) b) = ((e - l : ℕ) : ℂ) • (L₁ ^ l) b := by
          rw [Nat.cast_sub hl]
          exact sourceLOne_pow_weight b (e : ℂ) hb l
        have hneg : ((d - i : ℕ) : ℤ) + ((e - l : ℕ) : ℤ) < n + (h : ℤ) + 1 := by
          dsimp only [K] at hcut
          omega
        have hz := sourceMu_eq_zero_of_weight_lt_mode_succ ((L₁ ^ i) a) ((L₁ ^ l) b)
          (d - i) (e - l) hai hbl (n + (h : ℤ)) hneg
        simp only [F, hz, map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero]
      · exact hRightZero i l h (Nat.lt_of_not_ge hl)
    · exact hLeftZero i l h (Nat.lt_of_not_ge hi)

  have hNativeSum :
      (∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
        ∑ h ∈ Finset.range (K - i - l), nativeTerm i l h) =
      ∑ i ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (e + 1),
        ∑ h ∈ Finset.range H, nativeTerm i l h := by
    calc
      _ = ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
            ∑ h ∈ Finset.range H, nativeTerm i l h := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro h _ hh
        have hh' : K - i - l ≤ h := Nat.le_of_not_lt fun hlt => hh (Finset.mem_range.mpr hlt)
        simp only [nativeTerm, hNativeTail i l h (by omega), mul_zero]
      _ = ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (e + 1),
            ∑ h ∈ Finset.range H, nativeTerm i l h := by
        apply Finset.sum_congr rfl
        intro i _
        apply sum_range_eq_of_cutoffs
        · intro l hl
          apply Finset.sum_eq_zero
          intro h _
          simp only [nativeTerm, hNativeTail i l h (by omega), mul_zero]
        · intro l hl
          apply Finset.sum_eq_zero
          intro h _
          simp only [nativeTerm, hRightZero i l h (by omega), mul_zero]
      _ = _ := by
        apply sum_range_eq_of_cutoffs
        · intro i hi
          apply Finset.sum_eq_zero
          intro l _
          apply Finset.sum_eq_zero
          intro h _
          simp only [nativeTerm, hNativeTail i l h (by omega), mul_zero]
        · intro i hi
          apply Finset.sum_eq_zero
          intro l _
          apply Finset.sum_eq_zero
          intro h _
          simp only [nativeTerm, hLeftZero i l h (by omega), mul_zero]

  have hT : gradedPairing f (T v) =
      ∑ i ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (e + 1),
        ∑ h ∈ Finset.range H, nativeTerm i l h := by
    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      smul_eq_mul, Finset.mul_sum, nativeTerm, F, kNative]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro h _
    ring

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  change (∑ j ∈ Finset.range H, target j) =
    (-epsilon n * ((-1 : ℂ) ^ d * (-1 : ℂ) ^ e)) * gradedPairing f (T v)
  calc
    _ = ∑ j ∈ Finset.range K, target j := by
      symm
      apply Finset.sum_subset (Finset.range_mono hKH)
      intro j _ hj
      exact hTargetTail j (Nat.le_of_not_lt fun h => hj (Finset.mem_range.mpr h))
    _ = phase * (∑ j ∈ Finset.range K, ∑ r ∈ Finset.range (K - j),
          ∑ i ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r - i + 1),
            G i l j (r - i - l)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hBPZ j (Finset.mem_range.mp hj))
    _ = phase * (∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
          ∑ j ∈ Finset.range (K - i - l), ∑ u ∈ Finset.range (K - i - l - j),
            G i l j u) := by
      rw [sum_range_iterate_simplex_reindex K G]
    _ = phase * (∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
          ∑ h ∈ Finset.range (K - i - l), nativeTerm i l h) := by
      apply congrArg (fun x : ℂ => phase * x)
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      simpa only [G, nativeTerm, smul_eq_mul, Finset.mul_sum, hChooseShift] using
        (restrictedDualJacobi_iterate_reindex M (B i) (K - i - l) (F i l))
    _ = _ := by rw [hNativeSum, ← hT, hPhase]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
