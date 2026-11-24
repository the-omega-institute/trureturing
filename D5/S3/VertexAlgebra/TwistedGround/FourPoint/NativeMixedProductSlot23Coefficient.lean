/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedProductSlot23Coefficient
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite upper half-turn exchange of actual native Leech B coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddRightDetectorTranslation

/-! Finite exchange of the two mixed insertions in the actual Leech B product. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Coefficient

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open ActualEnergyRestrictedDual (maxOddWeight)
open Complex (I)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockGradedTrace (actualGrade)
open NativeMixedUpperProductCusp (bProductCoeff)
open Orbifold.NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit oddTranslation paritySign)
open Orbifold.NativeOddUpperRightSkew (rightField lowering)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeMixedPairSkew (swapInput mu_skew_of_grade mu_skew_translation_tail)
open Orbifold.NativeOddRightDetectorTranslation (detector detector_divided_source_translation)
open private maxOddWeight_le_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm

local notation "ℒ" => leechData
local notation "U" => oddTranslation ℒ
local notation "L₁" => lowering ℒ leechUnit

private abbrev State (s : Bool) := Twisted ℒ leechUnit s

set_option maxHeartbeats 1000000 in
-- The actual right field and skew coefficients require unfolding the concrete state types.
/-- Upper half-turn exchange of Q and R at one lattice energy. The translation
order is `h`, the detector lowering order is `j`, and the new pair energy is
`E - h`. The same actual right field acts on the exchanged mixed pair. -/
theorem bProductCoeff_slot23_exchange (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t)) (E : ℕ)
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hS : S.val ∈ actualGrade ℒ leechUnit N) :
    bProductCoeff s t M K L N Q R P S E =
      (-1 : ℂ) ^ (3 + K) * ∑ h ∈ Finset.range (E + 1),
        I ^ (2 * ((E - h : ℕ) : ℤ) - (6 + (K : ℤ) + L)) *
          ∑ j ∈ Finset.range (min h (N / 2) + 1),
            ((j.factorial : ℂ)⁻¹ * Ring.choose ((E : ℂ) + ((M : ℂ) - N) / 2 - 1) (h - j)) *
              bProductCoeff (!s) t M L K (N - 2 * j) R (swapInput Q) P
                ((L₁ (!t) ^ j) S) (E - h) := by
  classical
  let e : ℤ := (N : ℤ) - M - 2 * (E : ℤ)
  let q : ℤ := 2 * (E : ℤ) - (6 + (K : ℤ) + L)
  let source (h : ℕ) : OddCarrier ℒ :=
    (mu (!s) R).coeff (q - 2 * (h : ℤ)) (swapInput Q)
  let term (h : ℕ) : OddCarrier ℒ :=
    (I ^ (q - 2 * (h : ℤ)) * (h.factorial : ℂ)⁻¹) • (U ^ h) (source h)
  have hQmax : (maxOddWeight ℒ leechUnit Q.val : ℤ) ≤ (K : ℤ) := by
    exact_mod_cast maxOddWeight_le_grade hQ
  have hRmax : (maxOddWeight ℒ leechUnit R.val : ℤ) ≤ (L : ℤ) := by
    exact_mod_cast maxOddWeight_le_grade hR
  have hsupport : Function.support term ⊆ (Finset.range (E + 1) : Set ℕ) := by
    intro h hh
    apply Finset.mem_range.mpr
    by_contra! htail
    apply hh
    dsimp only [term, source]
    have htailBound :
        q + (maxOddWeight ℒ leechUnit Q.val : ℤ) + maxOddWeight ℒ leechUnit R.val + 6 ≤
          2 * (h : ℤ) := by
      dsimp only [q]
      omega
    rw [mu_skew_translation_tail s q Q R h htailBound, smul_zero]
  have hskew :
      (mu s Q).coeff q R = (-1 : ℂ) ^ (3 + K) • ∑ h ∈ Finset.range (E + 1), term h := by
    have skew := mu_skew_of_grade true s K L q Q R hQ hR
    change (mu s Q).coeff q R = (-1 : ℂ) ^ (3 + K) • ∑ᶠ h, term h at skew
    rw [skew, finsum_eq_sum_of_support_subset term hsupport]
  let D : OddCarrier ℒ →ₗ[ℂ] ℂ :=
    ((actualForm ℒ leechUnit S.val).comp (paritySpace ℒ leechUnit (paritySign (!t))).subtype).comp
      ((rightField ℒ leechUnit t P).coeff e)
  have hD (a : OddCarrier ℒ) : D a = detector t e P S a := rfl
  have hchoose : -(e : ℂ) / 2 - 1 = (E : ℂ) + ((M : ℂ) - N) / 2 - 1 := by
    dsimp only [e]
    push_cast
    ring
  calc
    _ = D ((mu s Q).coeff q R) := rfl
    _ = (-1 : ℂ) ^ (3 + K) * ∑ h ∈ Finset.range (E + 1),
          I ^ (q - 2 * (h : ℤ)) * ((h.factorial : ℂ)⁻¹ *
            detector t e P S ((U ^ h) (source h))) := by
      rw [hskew, map_smul, map_sum]
      simp only [term, map_smul, smul_eq_mul, mul_assoc]
      simp only [hD]
    _ = _ := by
      apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (3 + K) * z)
      apply Finset.sum_congr rfl
      intro h hh
      have hhE : h ≤ E := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
      have hp : q - 2 * (h : ℤ) = 2 * ((E - h : ℕ) : ℤ) - (6 + (K : ℤ) + L) := by
        dsimp only [q]
        omega
      have hpSwap : q - 2 * (h : ℤ) = 2 * ((E - h : ℕ) : ℤ) - (6 + (L : ℤ) + K) := by
        rw [hp]
        ring
      have htranslate := detector_divided_source_translation t h e N P S (source h) hS
      rw [htranslate, hchoose, hp]
      apply congrArg (fun z : ℂ => I ^ (2 * ((E - h : ℕ) : ℤ) - (6 + (K : ℤ) + L)) * z)
      apply Finset.sum_congr rfl
      intro j hj
      have hjMin : j ≤ min h (N / 2) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjh : j ≤ h := hjMin.trans (min_le_left _ _)
      have hjN : j ≤ N / 2 := hjMin.trans (min_le_right _ _)
      have he : e + 2 * ((h - j : ℕ) : ℤ) =
          ((N - 2 * j : ℕ) : ℤ) - M - 2 * ((E - h : ℕ) : ℤ) := by
        dsimp only [e]
        omega
      simp only [source, detector, bProductCoeff, hpSwap, he]

/-- Reflect the generalized binomial in the finite exchange weight. -/
theorem slot23_choose_reflection (M N E h j : ℕ) (hhE : h ≤ E) (hjh : j ≤ h) :
    Ring.choose ((E : ℂ) + ((M : ℂ) - N) / 2 - 1) (h - j) =
      (-1 : ℂ) ^ (h - j) *
        Ring.choose (((N : ℂ) - M - 2 * (j : ℂ)) / 2 - ((E - h : ℕ) : ℂ)) (h - j) := by
  let r : ℂ := ((N : ℂ) - M) / 2 - (E : ℂ) + 1
  have hx : (E : ℂ) + ((M : ℂ) - N) / 2 - 1 = -r := by
    dsimp only [r]
    ring
  have hy : r + ((h - j : ℕ) : ℂ) - 1 =
      ((N : ℂ) - M - 2 * (j : ℂ)) / 2 - ((E - h : ℕ) : ℂ) := by
    dsimp only [r]
    rw [Nat.cast_sub hjh, Nat.cast_sub hhE]
    ring
  rw [hx]
  simpa only [hy, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast] using
    (Ring.choose_neg r (h - j))

/-!
For the pullback, write `F = E - h`, `k = h - j` and
`δⱼ = (N - M - 2*j) / 2` with signed subtraction. Then `E = F + j + k`.
For fixed `F,j`, the reflected weights `(-1)^k choose(δⱼ - F,k)` are the
coefficients of the formal binomial series for `(1-y)^(δⱼ-F)`.
The upper phase `I^(2*F-a) = I^(-a) (-1)^F`, with `a = 6+K+L`,
makes the resulting weight
`I^(-a) (y^j/j!) (1-y)^δⱼ (-y/(1-y))^F`.
-/

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Coefficient
