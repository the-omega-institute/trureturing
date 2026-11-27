/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedBProductInversion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedBProductInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Detector reversal of the convergent native mixed B product on its complex root cover. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ

/-! The native B product inverts on the specified root lifts. The physical
order is `(u, v, w, b)`, so `t = false`, `s = true` exchanges HBHB with BHBH. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion

open Complex (I)
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeGeneratingFieldLocality (Oscillator)
open LatticeHalfFockChargedTensorCoefficients (ActualGround groundRank)
open LatticeTwistedGroundRealization (Half)
open LatticeHalfFockGradedTrace
  (actualGrade actualAmbientBasis actual_basis_apply actual_basis_eigenvalue
   actual_grade_mem_iff_repr_support OddMonomial)
open LatticeHalfFockParityT (actualParity_on_actualGrade actualParity_preserves_grade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit OddCarrier paritySign)
open Orbifold.NativeOddUpperRightSkew (lowering R rightField)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeMixedPairField (mu)
open OriginalFourMChargeCoset (oscillatorLower)
open NativeMixedUpperProductCusp
  (bJointTerm bProductCoeff b_inner_coeff_off_grid b_joint_product_hasSum)
open NativeMixedInverseBPZ (bProductCoeff_detector_reversal)

open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private b_inner_energy b_outer_pairing_off_grid from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private actualGrade_eigen lowering_pow_val doubledCoefficient from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private lower_power_tmul from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private mem_parity from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s

private def bModes (M K L N E : ℕ) : ℤ × ℤ :=
  (2 * (E : ℤ) - (6 + (K : ℤ) + L), (N : ℤ) - M - 2 * (E : ℤ))

private def bEnergyTerm (s t : Bool) (M K L N : ℕ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t))
    (xR zR : ℂ) (E : ℕ) : ℂ :=
  bProductCoeff s t M K L N v w u b E *
    (zR ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)) * xR ^ ((N : ℤ) - M - 2 * (E : ℤ)))

private theorem bEnergy_hasSum_iff (s t : Bool) (M K L N : ℕ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t))
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (xR zR value : ℂ) :
    HasSum (bEnergyTerm s t M K L N v w u b xR zR) value ↔
      HasSum (bJointTerm s t v w u b xR zR) value := by
  have hinj : Function.Injective (bModes M K L N) := by
    intro E F h
    have hfst := congrArg Prod.fst h
    dsimp only [bModes] at hfst
    omega
  have hoff (i : ℤ × ℤ) (hi : i ∉ Set.range (bModes M K L N)) :
      bJointTerm s t v w u b xR zR i = 0 := by
    rcases i with ⟨j, e⟩
    by_cases hj : ∃ E : ℕ, j = (bModes M K L N E).1
    · obtain ⟨E, rfl⟩ := hj
      have he : e ≠ (bModes M K L N E).2 := fun h => hi ⟨E, Prod.ext rfl h.symm⟩
      have hgrade := b_inner_energy s K L E v w hv hw hKL
      have hpair := b_outer_pairing_off_grid t M N E u b hu hb
        ((mu s v).coeff ((bModes M K L N E).1) w) hgrade e he
      rw [bJointTerm, hpair, zero_mul]
    · have hinner := b_inner_coeff_off_grid s K L v w hv hw hKL j (fun E h => hj ⟨E, h⟩)
      simp [bJointTerm, hinner]
  exact hinj.hasSum_iff hoff

private theorem lowered_tmul {s : Bool} (n : ℕ) (u : State s)
    (P : Oscillator ℒ) (p : ActualGround ℒ leechUnit) (hu : u.val = P ⊗ₜ[ℂ] p) :
    ((L₁ s ^ n) u).val = ((oscillatorLower ℒ ^ n) P) ⊗ₜ[ℂ] p := by
  rw [lowering_pow_val, hu]
  exact lower_power_tmul ℒ leechUnit n P p

private theorem b_joint_summable_of_tensors (s t : Bool) (M K L N : ℕ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t))
    (P Q U S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwU : w.val = U ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖zR‖ < ‖xR‖) :
    Summable (bJointTerm s t v w u b xR zR) := by
  have hxpos := norm_pos_iff.mpr hx
  have hρ₀ : 0 < ‖zR / xR‖ := by
    rw [norm_div]
    exact div_pos (norm_pos_iff.mpr hz) hxpos
  have hρ₁ : ‖zR / xR‖ < 1 := by
    rw [norm_div, div_lt_one hxpos]
    exact hr
  exact (b_joint_product_hasSum s t M K L N v w u b P Q U S p q r d
    hv hw hu hb hvQ hwU huP hbS hKL hNM hx hρ₀ hρ₁).summable

private def reversalWeight (M K : ℕ) (xR zR : ℂ) (n q : ℕ) : ℂ :=
  ((n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹) *
    (xR ^ (2 * (n : ℤ) - 6 - 2 * (M : ℤ)) * zR ^ (2 * (q : ℤ) - 6 - 2 * (K : ℤ)))

private theorem b_joint_hasSum_of_reversal (s t : Bool) (M K L N : ℕ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t))
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖zR‖ < ‖xR‖)
    (hsum : ∀ n q : ℕ,
      ((L₁ t ^ n) u).val ∈ actualGrade ℒ leechUnit (M - 2 * n) →
      ((L₁ s ^ q) v).val ∈ actualGrade ℒ leechUnit (K - 2 * q) →
      Odd (((M - 2 * n : ℕ) : ℤ) + N) → Odd ((L : ℤ) - (K - 2 * q : ℕ)) →
      zR⁻¹ ≠ 0 → xR⁻¹ ≠ 0 → ‖xR⁻¹‖ < ‖zR⁻¹‖ →
      Summable (bJointTerm t s ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w zR⁻¹ xR⁻¹)) :
    HasSum (bJointTerm s t v w u b xR zR)
      (I ^ ((M : ℤ) - K) * ∑ n ∈ Finset.range (M / 2 + 1),
        ∑ q ∈ Finset.range (K / 2 + 1), reversalWeight M K xR zR n q *
          ∑' i, bJointTerm t s ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w zR⁻¹ xR⁻¹ i) := by
  have hrInv : ‖xR⁻¹‖ < ‖zR⁻¹‖ := by
    rw [norm_inv, norm_inv]
    exact (inv_lt_inv₀ (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hz)).mpr hr
  have hreversed := (hasSum_sum (s := Finset.range (M / 2 + 1)) fun n hn =>
    hasSum_sum (s := Finset.range (K / 2 + 1)) fun q hq => by
      have hn' : n ≤ M / 2 := by simpa using hn
      have hq' : q ≤ K / 2 := by simpa using hq
      have hu' := lowered_grade (s := t) (u := u) hu hn'
      have hv' := lowered_grade (s := s) (u := v) hv hq'
      have hinner : Odd (((M - 2 * n : ℕ) : ℤ) + N) := by
        obtain ⟨a, ha⟩ := hNM
        exact ⟨a + (M : ℤ) - n, by omega⟩
      have houter : Odd ((L : ℤ) - (K - 2 * q : ℕ)) := by
        obtain ⟨a, ha⟩ := hKL
        exact ⟨a - (K : ℤ) + q, by omega⟩
      have hjoint := (hsum n q hu' hv' hinner houter
        (inv_ne_zero hz) (inv_ne_zero hx) hrInv).hasSum
      exact ((bEnergy_hasSum_iff t s (K - 2 * q) (M - 2 * n) N L
        ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w hu' hb hv' hw hinner _ _ _).mpr hjoint).mul_left
        (reversalWeight M K xR zR n q)).mul_left (I ^ ((M : ℤ) - K))
  apply (bEnergy_hasSum_iff s t M K L N v w u b hv hw hu hb hKL xR zR _).mp
  refine hreversed.congr_fun fun E => ?_
  simp only [bEnergyTerm]
  rw [bProductCoeff_detector_reversal s t M K L N v w u b E hu hv hw hb]
  simp only [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro q hq
  have hn' : n ≤ M / 2 := by simpa using hn
  have hq' : q ≤ K / 2 := by simpa using hq
  have hxpow : (N : ℤ) - M - 2 * (E : ℤ) =
      (2 * (n : ℤ) - 6 - 2 * (M : ℤ)) -
        (2 * (E : ℤ) - (6 + ((M - 2 * n : ℕ) : ℤ) + N)) := by omega
  have hzpow : 2 * (E : ℤ) - (6 + (K : ℤ) + L) =
      (2 * (q : ℤ) - 6 - 2 * (K : ℤ)) -
        ((L : ℤ) - (K - 2 * q : ℕ) - 2 * (E : ℤ)) := by omega
  rw [hxpow, hzpow, zpow_sub₀ hx, zpow_sub₀ hz]
  simp only [reversalWeight, inv_zpow, div_eq_mul_inv]
  ring

/-- Detector reversal for homogeneous pure tensors on the complex root cover.
Each lowered tensor keeps its ground vector and is summed by native B convergence. -/
theorem b_joint_product_hasSum_detector_reversal_of_tensors (s t : Bool) (M K L N : ℕ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t))
    (P Q U S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwU : w.val = U ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖zR‖ < ‖xR‖) :
    HasSum (bJointTerm s t v w u b xR zR)
      (I ^ ((M : ℤ) - K) * ∑ n ∈ Finset.range (M / 2 + 1),
        ∑ j ∈ Finset.range (K / 2 + 1),
          ((n.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹ *
            (xR ^ (2 * (n : ℤ) - 6 - 2 * (M : ℤ)) * zR ^ (2 * (j : ℤ) - 6 - 2 * (K : ℤ)))) *
          ∑' i, bJointTerm t s ((L₁ t ^ n) u) b ((L₁ s ^ j) v) w zR⁻¹ xR⁻¹ i) := by
  apply b_joint_hasSum_of_reversal s t M K L N v w u b hv hw hu hb hKL hNM hx hz hr
  intro n j hu' hv' hinner houter hx' hz' hr'
  exact b_joint_summable_of_tensors t s (K - 2 * j) (M - 2 * n) N L
    ((L₁ t ^ n) u) b ((L₁ s ^ j) v) w
    ((oscillatorLower ℒ ^ j) Q) ((oscillatorLower ℒ ^ n) P) S U q p d r
    hu' hb hv' hw (lowered_tmul n u P p huP) hbS (lowered_tmul j v Q q hvQ) hwU
    hinner houter hx' hz' hr'

private abbrev FourLinear (s t : Bool) :=
  State s →ₗ[ℂ] State (!s) →ₗ[ℂ] State t →ₗ[ℂ] State (!t) →ₗ[ℂ] ℂ

private def bModeLinear (s t : Bool) (xR zR : ℂ) (i : ℤ × ℤ) : FourLinear s t :=
  let inner := ((LinearMap.proj i.1).comp HVertexOperator.coeff).comp (mu s)
  let rightCoeff : State t →ₗ[ℂ] OddCarrier ℒ →ₗ[ℂ] State (!t) :=
    if Even i.2 then 0 else R ℒ leechUnit t ((-i.2 - 3) / 2)
  let sub := (paritySpace ℒ leechUnit (paritySign (!t))).subtype
  let pair := ((actualForm ℒ leechUnit).flip.compl₂ sub).comp sub
  (zR ^ i.1 * xR ^ i.2) • inner.compr₂ (rightCoeff.flip.compr₂ pair)

private theorem bModeLinear_apply (s t : Bool) (xR zR : ℂ) (i : ℤ × ℤ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t)) :
    bModeLinear s t xR zR i v w u b = bJointTerm s t v w u b xR zR i := by
  change (zR ^ i.1 * xR ^ i.2) *
      actualForm ℒ leechUnit b.val
        (((if Even i.2 then 0 else R ℒ leechUnit t ((-i.2 - 3) / 2)) u)
          ((mu s v).coeff i.1 w)).val = _
  unfold bJointTerm rightField
  rw [HVertexOperator.coeff_of_coeff]
  by_cases hi : Even i.2 <;>
    simp only [doubledCoefficient, hi, ite_true, ite_false, LinearMap.zero_apply, mul_comm]

private abbrev basis := actualAmbientBasis ℒ leechUnit
private abbrev BasisIndex := OddMonomial ℒ × Half (groundRank ℒ leechUnit)

private theorem projected_basis_tensor (s : Bool) (G : ℕ) (u : State s)
    (hu : u.val ∈ actualGrade ℒ leechUnit G) (i : BasisIndex)
    (hi : i ∈ (basis.repr u.val).support) :
    (project s (basis i)).val ∈ actualGrade ℒ leechUnit G ∧
      ∃ (P : Oscillator ℒ) (p : ActualGround ℒ leechUnit),
        (project s (basis i)).val = P ⊗ₜ[ℂ] p := by
  have hG := (actual_grade_mem_iff_repr_support ℒ leechUnit G u.val).mp hu i hi
  have hgrade : basis i ∈ actualGrade ℒ leechUnit G := by
    apply (actualGrade_eigen ℒ leechUnit G (basis i)).mpr
    simpa only [hG] using actual_basis_eigenvalue ℒ leechUnit i.1 i.2
  constructor
  · rw [project_val]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hgrade (Submodule.smul_mem _ _
      (actualParity_preserves_grade ℒ leechUnit _ _ hgrade)))
  · let P := MvPolynomial.monomial i.1 (1 : ℂ)
    let p : ActualGround ℒ leechUnit := Pi.single i.2 1
    have ht : basis i = P ⊗ₜ[ℂ] p := actual_basis_apply ℒ leechUnit i.1 i.2
    refine ⟨(2 : ℂ)⁻¹ • (P + paritySign s • ((-1 : ℂ) ^ G • P)), p, ?_⟩
    rw [project_val, actualParity_on_actualGrade ℒ leechUnit G ⟨basis i, hgrade⟩]
    simp only [Subtype.coe_mk, ht, TensorProduct.smul_tmul', ← TensorProduct.add_tmul]

/-- Finite projected-basis expansion supplies native B convergence for all
homogeneous external states with the mixed grade parities. -/
theorem b_joint_product_summable_of_homogeneous (s t : Bool) (M K L N : ℕ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t))
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖zR‖ < ‖xR‖) :
    Summable (bJointTerm s t v w u b xR zR) := by
  classical
  let cv := basis.repr v.val
  let cw := basis.repr w.val
  let cu := basis.repr u.val
  let cb := basis.repr b.val
  let F := bModeLinear s t xR zR
  have hexpand (i : ℤ × ℤ) :
      bJointTerm s t v w u b xR zR i =
        ∑ a ∈ cv.support, cv a * (∑ c ∈ cw.support, cw c * (∑ e ∈ cu.support,
          cu e * (∑ f ∈ cb.support, cb f * F i (project s (basis a)) (project (!s) (basis c))
            (project t (basis e)) (project (!t) (basis f))))) := by
    rw [← bModeLinear_apply]
    conv_lhs =>
      rw [← sum_projectedBasis s v]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis (!s) w]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis t u]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis (!t) b]
      simp only [map_sum, map_smul, smul_eq_mul]
  have hBasis (a : BasisIndex) (ha : a ∈ cv.support) (c : BasisIndex) (hc : c ∈ cw.support)
      (e : BasisIndex) (he : e ∈ cu.support) (f : BasisIndex) (hf : f ∈ cb.support) :
      Summable (fun i => F i (project s (basis a)) (project (!s) (basis c))
        (project t (basis e)) (project (!t) (basis f))) := by
    obtain ⟨hv', Q, q, hvQ⟩ := projected_basis_tensor s K v hv a ha
    obtain ⟨hw', U, r, hwU⟩ := projected_basis_tensor (!s) L w hw c hc
    obtain ⟨hu', P, p, huP⟩ := projected_basis_tensor t M u hu e he
    obtain ⟨hb', S, d, hbS⟩ := projected_basis_tensor (!t) N b hb f hf
    simpa only [F, bModeLinear_apply] using
      b_joint_summable_of_tensors s t M K L N _ _ _ _ P Q U S p q r d
        hv' hw' hu' hb' hvQ hwU huP hbS hKL hNM hx hz hr
  have h := hasSum_sum (s := cv.support) fun a ha => HasSum.mul_left (cv a) <|
    hasSum_sum (s := cw.support) fun c hc => HasSum.mul_left (cw c) <|
    hasSum_sum (s := cu.support) fun e he => HasSum.mul_left (cu e) <|
    hasSum_sum (s := cb.support) fun f hf => (hBasis a ha c hc e he f hf).hasSum.mul_left (cb f)
  exact (h.congr_fun hexpand).summable

private theorem grade_mod_two {s : Bool} {G : ℕ} {u : State s}
    (hu : u.val ∈ actualGrade ℒ leechUnit G) (hne : u ≠ 0) :
    G % 2 = if s then 1 else 0 := by
  have hpar := (mem_parity ℒ leechUnit (paritySign s) u.val).mp u.property
  have hgrade := actualParity_on_actualGrade ℒ leechUnit G ⟨u.val, hu⟩
  have hu₀ : u.val ≠ 0 := fun h => hne (Subtype.ext h)
  have hsign : (-1 : ℂ) ^ G = paritySign s :=
    smul_left_injective ℂ hu₀ (hgrade.symm.trans hpar)
  rw [neg_one_pow_eq_ite] at hsign
  cases s <;> by_cases hG : Even G
  · simpa using Nat.even_iff.mp hG
  · norm_num [paritySign, hG] at hsign
  · norm_num [paritySign, hG] at hsign
  · simpa using Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hG)

private theorem opposite_grade_parities {s : Bool} {A B : ℕ}
    (a : State s) (b : State (!s))
    (ha : a.val ∈ actualGrade ℒ leechUnit A) (hb : b.val ∈ actualGrade ℒ leechUnit B)
    (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) :
    Odd ((A : ℤ) + B) ∧ Odd ((B : ℤ) - A) := by
  have hA := grade_mod_two (s := s) (u := a) ha ha₀
  have hB := grade_mod_two (s := !s) (u := b) hb hb₀
  rw [Int.odd_iff, Int.odd_iff]
  cases s <;> simp at hA hB <;> omega

/-- The actual double-mode B product on the complex root cover has the
detector-reversed value at the reciprocal root lifts. Each reversed double
sum converges by the finite expansion in the actual homogeneous basis.
`HasSum.tsum_eq` gives the equality of the two native product values. -/
theorem b_joint_product_hasSum_detector_reversal (s t : Bool) (M K L N : ℕ)
    (v : State s) (w : State (!s)) (u : State t) (b : State (!t))
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖zR‖ < ‖xR‖) :
    HasSum (bJointTerm s t v w u b xR zR)
      (I ^ ((M : ℤ) - K) * ∑ n ∈ Finset.range (M / 2 + 1),
        ∑ q ∈ Finset.range (K / 2 + 1),
          ((n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹ *
            (xR ^ (2 * (n : ℤ) - 6 - 2 * (M : ℤ)) * zR ^ (2 * (q : ℤ) - 6 - 2 * (K : ℤ)))) *
          ∑' i, bJointTerm t s ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w zR⁻¹ xR⁻¹ i) := by
  by_cases hzero : v = 0 ∨ w = 0 ∨ u = 0 ∨ b = 0
  · change HasSum (fun i => bJointTerm s t v w u b xR zR i) _
    rcases hzero with rfl | rfl | rfl | rfl <;> simp [← bModeLinear_apply]
  push Not at hzero
  obtain ⟨hv₀, hw₀, hu₀, hb₀⟩ := hzero
  have hKL := (opposite_grade_parities v w hv hw hv₀ hw₀).1
  have hNM := (opposite_grade_parities u b hu hb hu₀ hb₀).2
  apply b_joint_hasSum_of_reversal s t M K L N v w u b hv hw hu hb hKL hNM hx hz hr
  intro n q hu' hv' hinner houter hx' hz' hr'
  exact b_joint_product_summable_of_homogeneous t s (K - 2 * q) (M - 2 * n) N L
    ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w hu' hb hv' hw hinner houter hx' hz' hr'

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
