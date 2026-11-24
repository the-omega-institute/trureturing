/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedProductSlot23PhysicalRoots
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual native Leech B slot exchange on both inner root lifts at physical scale. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic

/-! Physical-root transport of the actual native B product under slot exchange. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23PhysicalRoots

open ActualLeechHyperbolic (leechData)
open Complex (I)
open LatticeHalfFockGradedTrace (actualGrade)
open NativeMixedBProductInversion (b_joint_product_summable_of_homogeneous)
open NativeMixedProductSlot23Analytic (b_joint_product_hasSum_slot23)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff b_joint_product_neg_root)
open Orbifold.NativeMixedPairField (mu_coeff_even_zero)
open Orbifold.NativeMixedPairSkew (swapInput)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)

open private bEnergyTerm bEnergy_hasSum_iff bModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private swapInput_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s

/-- The two doubled modes on each actual energy diagonal have constant sum.
Scaling both roots multiplies the native sum by the corresponding integer power. -/
theorem b_joint_product_hasSum_scale (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L))
    {X x z B : ℂ} (hX : X ≠ 0)
    (hB : HasSum (bJointTerm s t Q R P S x z) B) :
    HasSum (bJointTerm s t Q R P S (X * x) (X * z))
      (X ^ ((N : ℤ) - M - (6 + (K : ℤ) + L)) * B) := by
  have hs := (bEnergy_hasSum_iff s t M K L N Q R P S hQ hR hP hS hKL x z B).mpr hB
  apply (bEnergy_hasSum_iff s t M K L N Q R P S hQ hR hP hS hKL (X * x) (X * z) _).mp
  refine (hs.mul_left (X ^ ((N : ℤ) - M - (6 + (K : ℤ) + L)))).congr_fun fun E => ?_
  symm
  let j : ℤ := 2 * (E : ℤ) - (6 + (K : ℤ) + L)
  let e : ℤ := (N : ℤ) - M - 2 * (E : ℤ)
  have hdegree : (N : ℤ) - M - (6 + (K : ℤ) + L) = j + e := by
    dsimp only [j, e]
    ring
  change X ^ ((N : ℤ) - M - (6 + (K : ℤ) + L)) *
      (bProductCoeff s t M K L N Q R P S E * (z ^ j * x ^ e)) =
    bProductCoeff s t M K L N Q R P S E * ((X * z) ^ j * (X * x) ^ e)
  rw [hdegree, zpow_add₀ hX, mul_zpow X z, mul_zpow X x]
  ring

/-- In the radial domain the raw native sum is the normalized sum at the
actual root ratio times an integer power of the physical outer root. -/
theorem b_joint_product_tsum_normalize (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {X Z : ℂ} (hX : X ≠ 0) (hZ : Z ≠ 0) (hrad : ‖Z‖ < ‖X‖) :
    (∑' i, bJointTerm s t Q R P S X Z i) =
      X ^ ((N : ℤ) - M - (6 + (K : ℤ) + L)) *
        ∑' i, bJointTerm s t Q R P S 1 (Z / X) i := by
  have hratio : ‖Z / X‖ < ‖(1 : ℂ)‖ := by
    rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr hX)]
    exact hrad
  have hs := b_joint_product_summable_of_homogeneous s t M K L N Q R P S
    hQ hR hP hS hKL hNM one_ne_zero (div_ne_zero hZ hX) hratio
  have hscaled := b_joint_product_hasSum_scale s t M K L N Q R P S hQ hR hP hS hKL
    hX hs.hasSum
  have hroot : X * (Z / X) = Z := by rw [mul_comm, div_mul_cancel₀ _ hX]
  simpa only [mul_one, hroot] using hscaled.tsum_eq

private theorem b_hasSum_neg_inner (s t : Bool)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    {x z B : ℂ} (hB : HasSum (bJointTerm s t Q R P S x z) B) :
    HasSum (bJointTerm s t Q R P S x (-z)) (-B) := by
  refine hB.neg.congr_fun fun i => ?_
  by_cases he : Even i.1
  · simp [bJointTerm, mu_coeff_even_zero s i.1 Q R he]
  · have ho := Int.not_even_iff_odd.mp he
    simp only [bJointTerm, ho.neg_zpow, neg_mul, mul_neg]

set_option maxHeartbeats 1800000 in
/-- The actual slot-(2,3) exchange at the physical roots `X, Z, D`.
The same upper half-turn sends the actual inner root to `I * Z` on either
sheet of `Z / X`. Both native sums have the displayed values, and the
target detector is the finite exponential of `Z ^ 2 • L(1)` on `S`. -/
theorem b_joint_product_hasSum_slot23_physical (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {X Z D v : ℂ} (hX : X ≠ 0) (hv : (Z / X) ^ (2 : ℕ) = v)
    (hv₀ : 0 < ‖v‖) (hv₁ : ‖v‖ < 1 / 2)
    (hD : D / X = Complex.sqrt (1 - v)) :
    let weight (j : ℕ) := (Z ^ (2 : ℕ)) ^ j / (j.factorial : ℂ)
    let translated : State (!t) :=
      ∑ j ∈ Finset.range (N / 2 + 1), weight j • (L₁ (!t) ^ j) S
    let targetValue :=
      ∑ j ∈ Finset.range (N / 2 + 1), weight j *
        ∑' i, bJointTerm (!s) t R (swapInput Q) P ((L₁ (!t) ^ j) S) D (I * Z) i
    HasSum (bJointTerm s t Q R P S X Z) ((-1 : ℂ) ^ (3 + K) * targetValue) ∧
      HasSum (bJointTerm (!s) t R (swapInput Q) P translated D (I * Z)) targetValue := by
  classical
  let r := Z / X
  let d := Complex.sqrt (1 - v)
  let root := Complex.sqrt v
  let degree : ℤ := (N : ℤ) - M - (6 + (K : ℤ) + L)
  let weight (j : ℕ) := (Z ^ (2 : ℕ)) ^ j / (j.factorial : ℂ)
  let translated : State (!t) :=
    ∑ j ∈ Finset.range (N / 2 + 1), weight j • (L₁ (!t) ^ j) S
  let targetTerm (j : ℕ) := bJointTerm (!s) t R (swapInput Q) P ((L₁ (!t) ^ j) S) D (I * Z)
  let targetValue := ∑ j ∈ Finset.range (N / 2 + 1), weight j * ∑' i, targetTerm j i
  let normalizedTerm (j : ℕ) := bJointTerm (!s) t R (swapInput Q) P ((L₁ (!t) ^ j) S) d (I * r)
  let normalizedValue :=
    ∑ j ∈ Finset.range (N / 2 + 1), (v ^ j / (j.factorial : ℂ)) * ∑' i, normalizedTerm j i
  change HasSum (bJointTerm s t Q R P S X Z) ((-1 : ℂ) ^ (3 + K) * targetValue) ∧
    HasSum (bJointTerm (!s) t R (swapInput Q) P translated D (I * Z)) targetValue
  have hvNe := norm_pos_iff.mp hv₀
  have hvSq : r ^ (2 : ℕ) = v := hv
  have hrSq : root ^ (2 : ℕ) = v := Complex.cpow_ofNat_inv_pow v 2
  have hdSq : d ^ (2 : ℕ) = 1 - v := Complex.cpow_ofNat_inv_pow (1 - v) 2
  have hZ : Z = X * r := by dsimp only [r]; rw [mul_comm, div_mul_cancel₀ _ hX]
  have hD' : D = X * d := by
    calc
      D = (D / X) * X := (div_mul_cancel₀ _ hX).symm
      _ = X * d := by rw [hD, mul_comm]
  have hIZ : X * (I * r) = I * Z := by rw [hZ]; ring
  have hPrincipal := b_joint_product_hasSum_slot23 s t M K L N Q R P S
    hQ hR hP hS hKL hNM hvNe hv₁
  change HasSum (bJointTerm s t Q R P S 1 root)
    ((-1 : ℂ) ^ (3 + K) *
      ∑ j ∈ Finset.range (N / 2 + 1), (v ^ j / (j.factorial : ℂ)) *
        ∑' i, bJointTerm (!s) t R (swapInput Q) P ((L₁ (!t) ^ j) S) d (I * root) i)
    at hPrincipal
  have hNormalized : HasSum (bJointTerm s t Q R P S 1 r)
      ((-1 : ℂ) ^ (3 + K) * normalizedValue) := by
    rcases eq_or_eq_neg_of_sq_eq_sq r root (hvSq.trans hrSq.symm) with h | h
    · simpa only [normalizedValue, normalizedTerm, h] using hPrincipal
    · have hNeg := b_hasSum_neg_inner s t Q R P S hPrincipal
      simpa only [normalizedValue, normalizedTerm, h, mul_neg, b_joint_product_neg_root,
        Finset.sum_neg_distrib] using hNeg
  have hrad : ‖I * r‖ < ‖d‖ := by
    have htri : (1 : ℝ) ≤ ‖1 - v‖ + ‖v‖ := by
      simpa only [sub_add_cancel, norm_one] using norm_add_le (1 - v) v
    have hiSq : ‖I * r‖ ^ (2 : ℕ) = ‖v‖ := by
      rw [norm_mul, Complex.norm_I, one_mul, ← norm_pow, hvSq]
    have hoSq : ‖d‖ ^ (2 : ℕ) = ‖1 - v‖ := by rw [← norm_pow, hdSq]
    by_contra! h
    have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [hoSq, hiSq] at hh
    linarith
  have hrNe : r ≠ 0 := fun h => hvNe (by simpa [h] using hvSq.symm)
  have hdNe : d ≠ 0 := by
    exact norm_pos_iff.mp ((norm_nonneg _).trans_lt hrad)
  have hQ' : (swapInput Q).val ∈ actualGrade ℒ leechUnit K := by
    simpa only [swapInput_val] using hQ
  have hLK : Odd ((L : ℤ) + K) := by rwa [add_comm]
  have hPhysical (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      HasSum (targetTerm j)
        (X ^ (((N - 2 * j : ℕ) : ℤ) - M - (6 + (L : ℤ) + K)) *
          ∑' i, normalizedTerm j i) := by
    have hjN := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hj₂ : 2 * j ≤ N := by omega
    have hS' := lowered_grade hS hjN
    have hNM' : Odd (((N - 2 * j : ℕ) : ℤ) - M) := by
      obtain ⟨k, hk⟩ := hNM
      refine ⟨k - (j : ℤ), ?_⟩
      rw [Nat.cast_sub hj₂]
      omega
    have hsum := b_joint_product_summable_of_homogeneous (!s) t M L K (N - 2 * j)
      R (swapInput Q) P ((L₁ (!t) ^ j) S) hR hQ' hP hS' hLK hNM'
      hdNe (mul_ne_zero Complex.I_ne_zero hrNe) hrad
    have hscaled := b_joint_product_hasSum_scale (!s) t M L K (N - 2 * j)
      R (swapInput Q) P ((L₁ (!t) ^ j) S) hR hQ' hP hS' hLK hX hsum.hasSum
    simpa only [targetTerm, normalizedTerm, ← hD', hIZ] using hscaled
  have hweight (j : ℕ) : weight j =
      X ^ (2 * (j : ℤ)) * (v ^ j / (j.factorial : ℂ)) := by
    change (Z ^ (2 : ℕ)) ^ j / (j.factorial : ℂ) =
      X ^ (2 * (j : ℤ)) * (v ^ j / (j.factorial : ℂ))
    rw [hZ, mul_pow X r, hvSq, mul_pow, ← pow_mul X 2 j,
      show 2 * (j : ℤ) = ((2 * j : ℕ) : ℤ) by norm_num, zpow_natCast]
    ring
  have hvalue : X ^ degree * normalizedValue = targetValue := by
    dsimp only [normalizedValue, targetValue]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj₂ : 2 * j ≤ N := by
      have hjN := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    have hdegree : 2 * (j : ℤ) + (((N - 2 * j : ℕ) : ℤ) - M - (6 + (L : ℤ) + K)) =
        degree := by
      rw [Nat.cast_sub hj₂]
      dsimp only [degree]
      push_cast
      ring
    rw [hweight j, (hPhysical j hj).tsum_eq]
    symm
    calc
      _ = (X ^ (2 * (j : ℤ)) * X ^ (((N - 2 * j : ℕ) : ℤ) - M - (6 + (L : ℤ) + K))) *
          ((v ^ j / (j.factorial : ℂ)) * ∑' i, normalizedTerm j i) := by ring
      _ = _ := by rw [← zpow_add₀ hX, hdegree]
  constructor
  · have hscaled := b_joint_product_hasSum_scale s t M K L N Q R P S
      hQ hR hP hS hKL hX hNormalized
    have hscaledValue : X ^ degree * ((-1 : ℂ) ^ (3 + K) * normalizedValue) =
        (-1 : ℂ) ^ (3 + K) * targetValue := by
      rw [← hvalue]
      ring
    change HasSum (bJointTerm s t Q R P S (X * 1) (X * r))
      (X ^ degree * ((-1 : ℂ) ^ (3 + K) * normalizedValue)) at hscaled
    simpa only [mul_one, ← hZ, hscaledValue] using hscaled
  · have hfinite : HasSum (fun i : ℤ × ℤ =>
        ∑ j ∈ Finset.range (N / 2 + 1), weight j * targetTerm j i) targetValue :=
      hasSum_sum (s := Finset.range (N / 2 + 1)) fun j hj =>
        (hPhysical j hj).summable.hasSum.mul_left (weight j)
    refine hfinite.congr_fun fun i => ?_
    symm
    change (∑ j ∈ Finset.range (N / 2 + 1), weight j * targetTerm j i) =
      bJointTerm (!s) t R (swapInput Q) P translated D (I * Z) i
    rw [← bModeLinear_apply (!s) t D (I * Z) i R (swapInput Q) P translated]
    dsimp only [translated]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, bModeLinear_apply, targetTerm]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23PhysicalRoots
