/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedAIterateRadial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedAIterateRadial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal odd-intermediate Leech A iterate sums on the physical radial root domain. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion

/-! Radial convergence of the native mixed A iterate on the two-root cover. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology TensorProduct VertexOperator
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedAIterateRadial

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeInvolution (minusSpace)
open LatticeGeneratingFieldLocality (Oscillator)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade actualAmbientBasis)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit paritySign)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeMixedPairField (mu mu_coeff_even_zero)
open NativeDoubledBPZCoevaluation (mu_fourPoint_off_right_grade)
open NativeFixedPairAIterate (fixedASlitSewn fixedASlitSewn_square)
open NativeMixedWickCuspGerm
  (mixedSewn mixedScalar mixedScalar_negative_square_germ mixedFieldLaurent
    mixedFieldLaurent_coeff_energy mixedFieldLaurent_coeff)
open OriginalGaussianSewnAnalytic (coefficient)

open private fixedASlitSewn_neg_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
open private mixedExponent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
open private opposite_grade_parities projected_basis_tensor from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
private abbrev State (s : Bool) := Twisted ℒ leechUnit s

private theorem mixedScalar_slit_germ (s : Bool) (M K L N : ℕ)
    (u : State s) (v : State (!s))
    (P Q R S : Oscillator ℒ) (x y z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Odd ((M : ℤ) + K)) :
    HasFPowerSeriesAt (fun r => fixedASlitSewn M K P Q R S x y z d (-r))
      (FormalMultilinearSeries.ofScalars ℂ
        (mixedScalar s M K L N u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d))) 0 := by
  obtain ⟨G, hG, hpull⟩ :=
    mixedScalar_negative_square_germ s M K L N u v P Q R S x y z d hu hv huP hvQ hR hS hpar
  have hSquare :
      ∀ᶠ ρ : ℂ in 𝓝 0, G (-(ρ ^ 2)) = fixedASlitSewn M K P Q R S x y z d (ρ ^ 2) := by
    filter_upwards [hpull, ball_mem_nhds (0 : ℂ) zero_lt_one] with ρ hρ hball
    have hn := mem_ball_zero_iff.mp hball
    rw [hρ, ← fixedASlitSewn_square M K P Q R S x y z d hn,
      ← fixedASlitSewn_square M K P Q R S x y z d (ρ := -ρ)
        (by simpa only [norm_neg] using hn), neg_sq]
    ring
  have hsqrt : Tendsto (fun r : ℂ => Complex.sqrt (-r)) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have hc : ContinuousAt Complex.sqrt (0 : ℂ) :=
      Complex.continuousAt_sqrt (Or.inl le_rfl)
    have hn : Tendsto (fun r : ℂ => -r) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using continuous_neg.continuousAt (x := (0 : ℂ)).tendsto
    exact (by simpa using hc.tendsto : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 0)).comp hn
  apply hG.congr
  filter_upwards [hsqrt.eventually hSquare] with r hr
  have hr_sq : (Complex.sqrt (-r)) ^ 2 = -r :=
    Complex.cpow_nat_inv_pow (-r) (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [hr_sq, neg_neg] using hr

/-- The literal mixed A iterate sums at every nonzero doubled root of
norm less than one. The slit numerator includes the original BPZ phase. -/
theorem mixed_a_iterate_hasSum (s : Bool) (M K L N : ℕ)
    (u : State s) (v : State (!s))
    (P Q R S : Oscillator ℒ) (x y z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Odd ((M : ℤ) + K)) {ξ : ℂ} (hξ₀ : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    HasSum (fun j : ℤ => actualForm ℒ leechUnit (S ⊗ₜ[ℂ] d)
      ((correctedField ℒ leechUnit ((mu s u).coeff j v).val).coeff
        ((N : ℤ) - L - (j + (M : ℤ) + K + 6)) (R ⊗ₜ[ℂ] z)) * ξ ^ j)
      (ξ ^ (-((M : ℤ) + K + 6)) * fixedASlitSewn M K P Q R S x y z d (-(ξ ^ 2))) := by
  let G : ℂ → ℂ := fun r => fixedASlitSewn M K P Q R S x y z d (-r)
  let c := mixedScalar s M K L N u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d)
  let A := mixedFieldLaurent s M K L N u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d)
  have hG : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ c) 0 :=
    mixedScalar_slit_germ s M K L N u v P Q R S x y z d hu hv huP hvQ hR hS hpar
  have hcoef (E : ℕ) : coefficient E G = c E := by
    have heq := hG.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hG
    simpa only [FormalMultilinearSeries.coeff_ofScalars, coefficient] using
      congrArg (fun p => FormalMultilinearSeries.coeff p E) heq
  have hball : ξ ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    exact pow_lt_one₀ (norm_nonneg ξ) hξ (by decide)
  have htaylor : HasSum (fun E : ℕ => c E * (ξ ^ 2) ^ E) (G (ξ ^ 2)) := by
    refine (Complex.hasSum_taylorSeries_on_ball
      (fixedASlitSewn_neg_differentiableOn M K P Q R S x y z d) hball).congr_fun ?_
    intro E
    rw [← hcoef]
    simp only [coefficient, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hoff (j : ℤ) (hj : j ∉ Set.range (mixedExponent M K)) : A.coeff j * ξ ^ j = 0 := by
    dsimp only [A, mixedFieldLaurent]
    rw [HahnSeries.embDomain_of_notMem_range hj, zero_mul]
  have hsum : HasSum (fun j : ℤ => A.coeff j * ξ ^ j)
      (ξ ^ (-((M : ℤ) + K + 6)) * G (ξ ^ 2)) := by
    apply ((mixedExponent M K).injective.hasSum_iff hoff).mp
    refine (htaylor.mul_left _).congr_fun fun E => ?_
    change A.coeff (2 * (E : ℤ) - ((M : ℤ) + K + 6)) *
        ξ ^ (2 * (E : ℤ) - ((M : ℤ) + K + 6)) = _
    have hpow : ξ ^ (2 * (E : ℤ) - ((M : ℤ) + K + 6)) =
        ξ ^ (-((M : ℤ) + K + 6)) * (ξ ^ 2) ^ E := by
      rw [show 2 * (E : ℤ) - ((M : ℤ) + K + 6) =
        -((M : ℤ) + K + 6) + 2 * (E : ℤ) by ring,
        zpow_add₀ hξ₀, zpow_mul, zpow_natCast _ E]
      rfl
    rw [show A.coeff _ = c E from mixedFieldLaurent_coeff_energy s M K L N E u v _ _, hpow]
    ring
  refine hsum.congr_fun fun j => ?_
  rw [show A.coeff j = _ from mixedFieldLaurent_coeff s M K L N j u v _ _ hu hv hpar]

/-- The literal mixed A term at its two independent doubled modes. -/
def aJointTerm (s : Bool) (u : State s) (v : State (!s))
    (w b : ActualTensor ℒ leechUnit) (differenceRoot zRoot : ℂ) (i : ℤ × ℤ) : ℂ :=
  actualForm ℒ leechUnit b
    ((correctedField ℒ leechUnit ((mu s u).coeff i.1 v).val).coeff i.2 w) *
      (differenceRoot ^ i.1 * zRoot ^ i.2)

private theorem mixed_a_off_diagonal (s : Bool) (M K L N : ℕ)
    (u : State s) (v : State (!s)) (w b : ActualTensor ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w ∈ actualGrade ℒ leechUnit L) (hb : b ∈ actualGrade ℒ leechUnit N)
    (hpar : Odd ((M : ℤ) + K)) (j e : ℤ)
    (he : e ≠ (N : ℤ) - L - (j + (M : ℤ) + K + 6)) :
    actualForm ℒ leechUnit b
      ((correctedField ℒ leechUnit ((mu s u).coeff j v).val).coeff e w) = 0 := by
  by_cases hj : Even j
  · simp [mu_coeff_even_zero s j u v hj]
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hj
    obtain ⟨m₀, hm₀⟩ := hpar
    have hmode : j = -2 * (-k - 2) - 3 := by omega
    rw [hmode]
    exact mu_fourPoint_off_right_grade s M K L N (-k - 2) (m₀ + k + 4) e
      u v w b hu hv hw hb (by omega) (by omega)

/-- The physical mixed A iterate sums over both integer modes. The two
coordinates are roots of the separation and the outer insertion, and the
homogeneous power of the outer root is retained in the value. -/
theorem mixed_a_joint_hasSum (s : Bool) (M K L N : ℕ)
    (u : State s) (v : State (!s))
    (P Q R S : Oscillator ℒ) (x y z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Odd ((M : ℤ) + K)) {differenceRoot zRoot : ℂ}
    (hd : differenceRoot ≠ 0) (hr : ‖differenceRoot‖ < ‖zRoot‖) :
    HasSum (aJointTerm s u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) differenceRoot zRoot)
      (zRoot ^ ((N : ℤ) - L - ((M : ℤ) + K + 6)) *
        ((differenceRoot / zRoot) ^ (-((M : ℤ) + K + 6)) *
          fixedASlitSewn M K P Q R S x y z d (-((differenceRoot / zRoot) ^ 2)))) := by
  let D : ℤ := (N : ℤ) - L - ((M : ℤ) + K + 6)
  let e (j : ℤ) : ℤ := (N : ℤ) - L - (j + (M : ℤ) + K + 6)
  let mode (j : ℤ) : ℤ × ℤ := (j, e j)
  have hzpos := (norm_nonneg differenceRoot).trans_lt hr
  have hz := norm_pos_iff.mp hzpos
  have hratio : ‖differenceRoot / zRoot‖ < 1 := by
    rw [norm_div, div_lt_one hzpos]
    exact hr
  have hinj : Function.Injective mode := fun _ _ h => congrArg Prod.fst h
  have hoff (i : ℤ × ℤ) (hi : i ∉ Set.range mode) :
      aJointTerm s u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) differenceRoot zRoot i = 0 := by
    rcases i with ⟨j, k⟩
    have he : k ≠ e j := fun h => hi ⟨j, Prod.ext rfl h.symm⟩
    rw [aJointTerm, mixed_a_off_diagonal s M K L N u v _ _ hu hv hR hS hpar j k he, zero_mul]
  apply (hinj.hasSum_iff hoff).mp
  have hsum := mixed_a_iterate_hasSum s M K L N u v P Q R S x y z d
    hu hv huP hvQ hR hS hpar (div_ne_zero hd hz) hratio
  refine (hsum.mul_left (zRoot ^ D)).congr_fun fun j => ?_
  have hpow : differenceRoot ^ j * zRoot ^ e j =
      zRoot ^ D * (differenceRoot / zRoot) ^ j := by
    rw [div_zpow, div_eq_mul_inv, ← zpow_neg]
    calc
      _ = differenceRoot ^ j * (zRoot ^ D * zRoot ^ (-j)) := by
        rw [← zpow_add₀ hz, show D + -j = e j by dsimp only [D, e]; ring]
      _ = _ := by ring
  change actualForm ℒ leechUnit (S ⊗ₜ[ℂ] d)
      ((correctedField ℒ leechUnit ((mu s u).coeff j v).val).coeff (e j) (R ⊗ₜ[ℂ] z)) *
        (differenceRoot ^ j * zRoot ^ e j) = _
  rw [hpow]
  ring

/-- The same sum at any choice of physical lifts of `x - z` and `z` in
the noncollision radial region. -/
theorem mixed_a_joint_hasSum_physical (s : Bool) (M K L N : ℕ)
    (u : State s) (v : State (!s))
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hvQ : v.val = Q ⊗ₜ[ℂ] q)
    (hR : R ⊗ₜ[ℂ] r ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Odd ((M : ℤ) + K)) {x z differenceRoot zRoot : ℂ}
    (hd : differenceRoot ^ 2 = x - z) (hz : zRoot ^ 2 = z)
    (hxz : x ≠ z) (hr : ‖x - z‖ < ‖z‖) :
    HasSum (aJointTerm s u v (R ⊗ₜ[ℂ] r) (S ⊗ₜ[ℂ] d) differenceRoot zRoot)
      (zRoot ^ ((N : ℤ) - L - ((M : ℤ) + K + 6)) *
        ((differenceRoot / zRoot) ^ (-((M : ℤ) + K + 6)) *
          fixedASlitSewn M K P Q R S p q r d (-((differenceRoot / zRoot) ^ 2)))) := by
  apply mixed_a_joint_hasSum s M K L N u v P Q R S p q r d hu hv huP hvQ hR hS hpar
  · intro hd₀
    apply hxz
    simpa only [hd₀, zero_pow (by decide : (2 : ℕ) ≠ 0), eq_comm, sub_eq_zero] using hd
  · apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [← norm_pow, hd, hz] using hr

private abbrev FourLinear (s t : Bool) :=
  State s →ₗ[ℂ] State (!s) →ₗ[ℂ] State t →ₗ[ℂ] State (!t) →ₗ[ℂ] ℂ

private def aModeLinear (s t : Bool) (differenceRoot zRoot : ℂ) (i : ℤ × ℤ) : FourLinear s t :=
  let inner := ((LinearMap.proj i.1).comp HVertexOperator.coeff).comp (mu s)
  let outer := ((LinearMap.proj i.2).comp HVertexOperator.coeff).comp (correctedField ℒ leechUnit)
  let outer' := outer.compl₁₂ (minusSpace ℒ).subtype
    (paritySpace ℒ leechUnit (paritySign t)).subtype
  let pair := (actualForm ℒ leechUnit).flip.compl₂
    (paritySpace ℒ leechUnit (paritySign (!t))).subtype
  (differenceRoot ^ i.1 * zRoot ^ i.2) • inner.compr₂ (outer'.compr₂ pair)

private theorem aModeLinear_apply (s t : Bool) (differenceRoot zRoot : ℂ) (i : ℤ × ℤ)
    (u : State s) (v : State (!s)) (w : State t) (b : State (!t)) :
    aModeLinear s t differenceRoot zRoot i u v w b =
      aJointTerm s u v w.val b.val differenceRoot zRoot i :=
  mul_comm _ _

/-- Finite projected-basis expansion gives convergence for all homogeneous
actual mixed states. An external zero state gives the zero series, including
when its assigned grade has the other parity. -/
theorem mixed_a_joint_summable_of_homogeneous (s t : Bool) (M K L N : ℕ)
    (u : State s) (v : State (!s)) (w : State t) (b : State (!t))
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {differenceRoot zRoot : ℂ} (hd : differenceRoot ≠ 0) (hr : ‖differenceRoot‖ < ‖zRoot‖) :
    Summable (aJointTerm s u v w.val b.val differenceRoot zRoot) := by
  classical
  by_cases hzero : u = 0 ∨ v = 0 ∨ w = 0 ∨ b = 0
  · change Summable (fun i => aJointTerm s u v w.val b.val differenceRoot zRoot i)
    rcases hzero with rfl | rfl | rfl | rfl
    · simp [← aModeLinear_apply s t]
    · simp [← aModeLinear_apply s t]
    · simp [aJointTerm]
    · simp [aJointTerm]
  push Not at hzero
  obtain ⟨hu₀, hv₀, _, _⟩ := hzero
  have hpar := (opposite_grade_parities u v hu hv hu₀ hv₀).1
  let basis := actualAmbientBasis ℒ leechUnit
  let cu := basis.repr u.val
  let cv := basis.repr v.val
  let cw := basis.repr w.val
  let cb := basis.repr b.val
  let F := aModeLinear s t differenceRoot zRoot
  have hexpand (i : ℤ × ℤ) :
      aJointTerm s u v w.val b.val differenceRoot zRoot i =
        ∑ a ∈ cu.support, cu a * (∑ c ∈ cv.support, cv c * (∑ e ∈ cw.support,
          cw e * (∑ f ∈ cb.support, cb f * F i (project s (basis a)) (project (!s) (basis c))
            (project t (basis e)) (project (!t) (basis f))))) := by
    rw [← aModeLinear_apply s t]
    conv_lhs =>
      rw [← sum_projectedBasis s u]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis (!s) v]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis t w]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis (!t) b]
      simp only [map_sum, map_smul, smul_eq_mul]
  have hBasis (a : _) (ha : a ∈ cu.support) (c : _) (hc : c ∈ cv.support)
      (e : _) (he : e ∈ cw.support) (f : _) (hf : f ∈ cb.support) :
      Summable (fun i => F i (project s (basis a)) (project (!s) (basis c))
        (project t (basis e)) (project (!t) (basis f))) := by
    obtain ⟨hu', P, p, huP⟩ := projected_basis_tensor s M u hu a ha
    obtain ⟨hv', Q, q, hvQ⟩ := projected_basis_tensor (!s) K v hv c hc
    obtain ⟨hw', R, r, hwR⟩ := projected_basis_tensor t L w hw e he
    obtain ⟨hb', S, d, hbS⟩ := projected_basis_tensor (!t) N b hb f hf
    rw [hwR] at hw'
    rw [hbS] at hb'
    simp only [F, aModeLinear_apply]
    rw [show (project t (basis e)).val = R ⊗ₜ[ℂ] r from hwR,
      show (project (!t) (basis f)).val = S ⊗ₜ[ℂ] d from hbS]
    exact (mixed_a_joint_hasSum s M K L N _ _ P Q R S p q r d
      hu' hv' huP hvQ hw' hb' hpar hd hr).summable
  have h := hasSum_sum (s := cu.support) fun a ha => HasSum.mul_left (cu a) <|
    hasSum_sum (s := cv.support) fun c hc => HasSum.mul_left (cv c) <|
    hasSum_sum (s := cw.support) fun e he => HasSum.mul_left (cw e) <|
    hasSum_sum (s := cb.support) fun f hf => (hBasis a ha c hc e he f hf).hasSum.mul_left (cb f)
  exact (h.congr_fun hexpand).summable

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedAIterateRadial
