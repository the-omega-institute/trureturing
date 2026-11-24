/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedProductRadialInversion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedProductRadialInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Detector reversal of the actual fixed double product on its complex root cover. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedInverseBPZ

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedProductRadialInversion

open Complex (I)
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeFixedUpperRightSkew
  (rightField rightField_coeff rightField_odd_zero R_pairing_finite)
open NativeFixedPairFourPoint (nu_fourPoint_off_right_grade)
open NativeFourHUpperProduct (fixedBProductCoeff fixedB_inner_coeff_off_grid)
open NativeFixedInverseBPZ (fixedBProductCoeff_detector_reversal)
open NativeFixedCrossedProductToIterate
  (dJointTerm fixed_d_joint_hasSum_crossed_a translatedDetector translationWeight)

open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedInverseBPZ
open private lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private grade_mod_two from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private dJointTerm_translatedDetector from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s

/-- The literal fixed B product in physical order `(u,v,w,b)`. The first mode
acts at the inner root `zR` and the second at the outer root `xR`. -/
abbrev fixedBJointTerm (s t : Bool) (v w : State s) (u b : State t)
    (xR zR : ℂ) (i : ℤ × ℤ) : ℂ :=
  dJointTerm s t v w u b zR xR i

private def fixedBModes (M K L N E : ℕ) : ℤ × ℤ :=
  (2 * (E : ℤ) - (6 + (K : ℤ) + L), (N : ℤ) - M - 2 * (E : ℤ))

/-- Evaluation of the fixed B coefficient at its doubled inner and outer modes. -/
def fixedBEnergyTerm (s t : Bool) (M K L N : ℕ)
    (v w : State s) (u b : State t) (xR zR : ℂ) (E : ℕ) : ℂ :=
  fixedBProductCoeff s t M K L N v w u b E *
    (zR ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)) *
      xR ^ ((N : ℤ) - M - 2 * (E : ℤ)))

private theorem fixedB_outer_pairing_off_grid (s t : Bool) (M K L N E : ℕ)
    (v w : State s) (u b : State t)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Even ((K : ℤ) + L)) (e : ℤ) (he : e ≠ (N : ℤ) - M - 2 * (E : ℤ)) :
    actualForm ℒ leechUnit b.val
      ((rightField ℒ leechUnit t u).coeff e
        ((nu s v).coeff (2 * (E : ℤ) - (6 + (K : ℤ) + L)) w)).val = 0 := by
  by_cases heven : Even e
  · obtain ⟨k, hk⟩ := hKL
    obtain ⟨r, hr⟩ := heven
    let m : ℤ := k + 2 - (E : ℤ)
    let a : ℤ := -r - 1
    have hinner : 2 * (E : ℤ) - (6 + (K : ℤ) + L) = -2 * m - 2 := by
      dsimp [m]
      omega
    have henergy : 2 * (E : ℤ) = (K : ℤ) + L + 4 - 2 * m := by omega
    have houter : e = -2 * a - 2 := by
      dsimp [a]
      omega
    rw [hinner, houter, rightField_coeff ℒ leechUnit t a u _,
      R_pairing_finite ℒ leechUnit t a N u _ b.val hb]
    apply Finset.sum_eq_zero
    intro ell hell
    have hell' : ell ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hell)
    have hdesc := lowered_grade (s := t) (u := b) hb hell'
    have hshift : -2 * (a + (ell : ℤ)) - 2 ≠
        ((N - 2 * ell : ℕ) : ℤ) - M - 2 * (E : ℤ) := by omega
    have hpair := nu_fourPoint_off_right_grade s K L M (N - 2 * ell) m (E : ℤ)
      (-2 * (a + (ell : ℤ)) - 2) v w u.val ((L₁ t ^ ell) b).val
      hv hw hu hdesc henergy hshift
    rw [lowering_pow_val] at hpair
    rw [hpair, mul_zero]
  · rw [rightField_odd_zero ℒ leechUnit t e (Int.not_even_iff_odd.mp heven),
      Submodule.coe_zero, map_zero]

/-- The fixed double-mode sum and its energy diagonal have the same `HasSum`
value. This holds for all homogeneous states, including zero states at
grades of either parity. -/
theorem fixed_b_joint_hasSum_iff_energy (s t : Bool) (M K L N : ℕ)
    (v w : State s) (u b : State t)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (xR zR value : ℂ) :
    HasSum (fixedBEnergyTerm s t M K L N v w u b xR zR) value ↔
      HasSum (fixedBJointTerm s t v w u b xR zR) value := by
  have hinj : Function.Injective (fixedBModes M K L N) := by
    intro E F h
    have hfst := congrArg Prod.fst h
    dsimp only [fixedBModes] at hfst
    omega
  have hoff (i : ℤ × ℤ) (hi : i ∉ Set.range (fixedBModes M K L N)) :
      fixedBJointTerm s t v w u b xR zR i = 0 := by
    rcases i with ⟨j, e⟩
    change actualForm ℒ leechUnit b.val
      ((rightField ℒ leechUnit t u).coeff e ((nu s v).coeff j w)).val *
        (zR ^ j * xR ^ e) = 0
    by_cases hKL : Even ((K : ℤ) + L)
    · by_cases hj : ∃ E : ℕ, j = (fixedBModes M K L N E).1
      · obtain ⟨E, rfl⟩ := hj
        have he : e ≠ (N : ℤ) - M - 2 * (E : ℤ) :=
          fun h => hi ⟨E, Prod.ext rfl h.symm⟩
        dsimp only [fixedBModes]
        rw [fixedB_outer_pairing_off_grid s t M K L N E v w u b hv hw hu hb hKL e he,
          zero_mul]
      · have hinner := fixedB_inner_coeff_off_grid s K L v w hv hw hKL j
          (fun E h => hj ⟨E, h⟩)
        simp only [hinner, map_zero, Submodule.coe_zero, zero_mul]
    · have hzero : v = 0 ∨ w = 0 := by
        by_contra! h
        have hK := grade_mod_two (s := s) (u := v) hv h.1
        have hL := grade_mod_two (s := s) (u := w) hw h.2
        apply hKL
        rw [Int.even_iff]
        cases s <;> simp at hK hL <;> omega
      have hinner : (nu s v).coeff j w = 0 := by
        rcases hzero with rfl | rfl
        · change (((LinearMap.proj j).comp HVertexOperator.coeff).comp (nu s)) (0 : State s) w = 0
          rw [map_zero, LinearMap.zero_apply]
        · exact map_zero ((nu s v).coeff j)
      simp only [hinner, map_zero, Submodule.coe_zero, zero_mul]
  exact hinj.hasSum_iff hoff

/-- Radial summability of the literal homogeneous fixed B product. The
crossed D theorem supplies the same double sum with the roots exchanged. -/
theorem fixed_b_joint_summable_of_homogeneous (s t : Bool) (M K L N : ℕ)
    (v w : State s) (u b : State t)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖zR‖ < ‖xR‖) :
    Summable (fixedBJointTerm s t v w u b xR zR) :=
  (fixed_d_joint_hasSum_crossed_a s t K L M N v w u b hv hw hu hb hz hx hr).summable

/-- The two factorials and the two doubled root powers for lowering orders
`n` at `xR` and `q` at `zR`. -/
def fixedProductReversalWeight (M K : ℕ) (xR zR : ℂ) (n q : ℕ) : ℂ :=
  ((n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹) *
    (xR ^ (2 * (n : ℤ) - 6 - 2 * (M : ℤ)) * zR ^ (2 * (q : ℤ) - 6 - 2 * (K : ℤ)))

/-- Same-energy BPZ reversal of the actual fixed B double series on the
complex root cover. Both parity choices of each fixed pair are allowed. -/
theorem fixed_b_joint_hasSum_detector_reversal (s t : Bool) (M K L N : ℕ)
    (v w : State s) (u b : State t)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖zR‖ < ‖xR‖) :
    HasSum (fixedBJointTerm s t v w u b xR zR)
      (I ^ ((M : ℤ) - K) * ∑ n ∈ Finset.range (M / 2 + 1),
        ∑ q ∈ Finset.range (K / 2 + 1), fixedProductReversalWeight M K xR zR n q *
          ∑' i, fixedBJointTerm t s ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w zR⁻¹ xR⁻¹ i) := by
  have hrInv : ‖xR⁻¹‖ < ‖zR⁻¹‖ := by
    rw [norm_inv, norm_inv]
    exact (inv_lt_inv₀ (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hz)).mpr hr
  have hrev := (hasSum_sum (s := Finset.range (M / 2 + 1)) fun n hn =>
    hasSum_sum (s := Finset.range (K / 2 + 1)) fun q hq => by
      have hn' : n ≤ M / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hq' : q ≤ K / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      have hu' := lowered_grade (s := t) (u := u) hu hn'
      have hv' := lowered_grade (s := s) (u := v) hv hq'
      have hjoint := (fixed_b_joint_summable_of_homogeneous t s (K - 2 * q) (M - 2 * n) N L
        ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w hu' hb hv' hw
        (inv_ne_zero hz) (inv_ne_zero hx) hrInv).hasSum
      exact ((fixed_b_joint_hasSum_iff_energy t s (K - 2 * q) (M - 2 * n) N L
        ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w hu' hb hv' hw _ _ _).mpr hjoint).mul_left
        (fixedProductReversalWeight M K xR zR n q)).mul_left (I ^ ((M : ℤ) - K))
  apply (fixed_b_joint_hasSum_iff_energy s t M K L N v w u b hv hw hu hb xR zR _).mp
  refine hrev.congr_fun fun E => ?_
  simp only [fixedBEnergyTerm]
  rw [fixedBProductCoeff_detector_reversal s t M K L N v w u b E hu hv hw hb]
  simp only [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro q hq
  have hn' : n ≤ M / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hq' : q ≤ K / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have hxpow : (N : ℤ) - M - 2 * (E : ℤ) =
      (2 * (n : ℤ) - 6 - 2 * (M : ℤ)) -
        (2 * (E : ℤ) - (6 + ((M - 2 * n : ℕ) : ℤ) + N)) := by omega
  have hzpow : 2 * (E : ℤ) - (6 + (K : ℤ) + L) =
      (2 * (q : ℤ) - 6 - 2 * (K : ℤ)) -
        ((L : ℤ) - (K - 2 * q : ℕ) - 2 * (E : ℤ)) := by omega
  rw [hxpow, hzpow, zpow_sub₀ hx, zpow_sub₀ hz]
  simp only [fixedProductReversalWeight, inv_zpow, div_eq_mul_inv]
  ring

/-- Fixed D in physical order `(P,Q,R,S)` pairs `P,R` at `xR`. Reversal
pairs the lowered `Q` with `S` at `zR⁻¹` and acts on the lowered `P` at
`xR⁻¹`, with the phase corresponding to the exchanged roots. -/
theorem fixed_d_joint_hasSum_detector_reversal (s t : Bool) (M K L N : ℕ)
    (P R : State s) (Q S : State t)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖xR‖ < ‖zR‖) :
    HasSum (dJointTerm s t P R Q S xR zR)
      (I ^ ((K : ℤ) - M) * ∑ q ∈ Finset.range (K / 2 + 1),
        ∑ n ∈ Finset.range (M / 2 + 1), fixedProductReversalWeight K M zR xR q n *
          ∑' i, dJointTerm t s ((L₁ t ^ q) Q) S ((L₁ s ^ n) P) R zR⁻¹ xR⁻¹ i) :=
  fixed_b_joint_hasSum_detector_reversal s t K M L N P R Q S hP hR hQ hS hz hx hr

/-- Reversal with the finitely translated detector used by upper A-to-D
transport. Each detector descendant becomes the right partner of the
lowered `Q` in the reciprocal fixed pair. -/
theorem fixed_d_joint_hasSum_translated_detector_reversal
    (s t : Bool) (M K L N : ℕ) (P R : State s) (Q S : State t) (a : ℂ)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖xR‖ < ‖zR‖) :
    HasSum (dJointTerm s t P R Q (translatedDetector t N a S) xR zR)
      (∑ ell ∈ Finset.range (N / 2 + 1), translationWeight a ell *
        (I ^ ((K : ℤ) - M) * ∑ q ∈ Finset.range (K / 2 + 1),
          ∑ n ∈ Finset.range (M / 2 + 1), fixedProductReversalWeight K M zR xR q n *
            ∑' i, dJointTerm t s ((L₁ t ^ q) Q) ((L₁ t ^ ell) S)
              ((L₁ s ^ n) P) R zR⁻¹ xR⁻¹ i)) := by
  have hrev := hasSum_sum (s := Finset.range (N / 2 + 1)) fun ell hell => by
    have hell' : ell ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hell)
    have hdesc := lowered_grade (s := t) (u := S) hS hell'
    exact (fixed_d_joint_hasSum_detector_reversal s t M K L (N - 2 * ell)
      P R Q ((L₁ t ^ ell) S) hP hQ hR hdesc hx hz hr).mul_left (translationWeight a ell)
  exact hrev.congr_fun (dJointTerm_translatedDetector s t N P R Q S a xR zR)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedProductRadialInversion
