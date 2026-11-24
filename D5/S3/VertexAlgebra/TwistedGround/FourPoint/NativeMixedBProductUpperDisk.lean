/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedBProductUpperDisk
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphic actual mixed Leech B sums at normalized and physical upper-disk roots. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
import Mathlib.Analysis.Complex.SqrtDeriv

/-! The native double-mode B product has a holomorphic sum on radial root
charts. The energy diagonal separates the root powers from a convergent power
series in the squared root ratio. For the upper slot-(2,3) transport, the target
physical roots give the principal square root of the upper disk coordinate as
their ratio. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Finset
open Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductUpperDisk

open ActualLeechHyperbolic (leechData)
open Complex (I)
open LatticeHalfFockGradedTrace (actualGrade oddWeight)
open LatticeHalfFockParityT (actualParity_preserves_grade)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)

open private bEnergy_hasSum_iff bModeLinear bModeLinear_apply opposite_grade_parities from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private BasisIndex basis from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private bEnergyTerm_factor bProductCoeff_summable_on_disk from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic
open private energySum energySum_analyticAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
open private basis_mem_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s

private theorem squared_ratio_norm_lt_one {x z : ℂ} (hx : x ≠ 0)
    (hr : ‖z‖ < ‖x‖) : ‖(z / x) ^ (2 : ℕ)‖ < 1 := by
  have h : ‖z / x‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hx)]
    exact hr
  rw [norm_pow]
  nlinarith [norm_nonneg (z / x)]

set_option maxHeartbeats 1000000 in
/-- On a radial chart of nonzero analytic roots, the actual homogeneous mixed B
modes converge to their holomorphic native sum. The state order is `P,Q,R,S`
with inner pair `Q,R` and detector `S`. -/
theorem b_joint_product_analytic_of_homogeneous (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {U : Set ℂ} (hU : IsOpen U) {x z : ℂ → ℂ}
    (hx : AnalyticOnNhd ℂ x U) (hz : AnalyticOnNhd ℂ z U)
    (hrad : ∀ y ∈ U, x y ≠ 0 ∧ z y ≠ 0 ∧ ‖z y‖ < ‖x y‖) :
    AnalyticOnNhd ℂ (fun y => ∑' i, bJointTerm s t Q R P S (x y) (z y) i) U ∧
      ∀ y ∈ U, HasSum (bJointTerm s t Q R P S (x y) (z y))
        (∑' i, bJointTerm s t Q R P S (x y) (z y) i) := by
  by_cases hzero : Q = 0 ∨ R = 0 ∨ P = 0 ∨ S = 0
  · have hterm (y : ℂ) : bJointTerm s t Q R P S (x y) (z y) = fun _ => 0 := by
      funext i
      rcases hzero with rfl | rfl | rfl | rfl <;>
        simp only [← bModeLinear_apply, map_zero, LinearMap.zero_apply]
    simp only [hterm, tsum_zero]
    exact ⟨analyticOnNhd_const, fun _ _ => hasSum_zero⟩
  push Not at hzero
  obtain ⟨hQ₀, hR₀, hP₀, hS₀⟩ := hzero
  have hKL := (opposite_grade_parities Q R hQ hR hQ₀ hR₀).1
  have hNM := (opposite_grade_parities P S hP hS hP₀ hS₀).2
  let a := bProductCoeff s t M K L N Q R P S
  let pole : ℤ := -(6 + (K : ℤ) + L)
  let F (y : ℂ) :=
    (z y ^ pole * x y ^ ((N : ℤ) - M)) * energySum a ((z y / x y) ^ (2 : ℕ))
  have ha (w : ℂ) (hw : ‖w‖ < 1) : Summable (fun E : ℕ => a E * w ^ E) :=
    bProductCoeff_summable_on_disk s t M K L N Q R P S hQ hR hP hS hKL hNM hw
  have hsum (y : ℂ) (hy : y ∈ U) :
      HasSum (bJointTerm s t Q R P S (x y) (z y)) (F y) := by
    obtain ⟨hx₀, hz₀, hr⟩ := hrad y hy
    apply (bEnergy_hasSum_iff s t M K L N Q R P S hQ hR hP hS hKL (x y) (z y) _).mp
    refine (((ha _ (squared_ratio_norm_lt_one hx₀ hr)).hasSum).mul_left
      (z y ^ pole * x y ^ ((N : ℤ) - M))).congr_fun fun E => ?_
    exact bEnergyTerm_factor s t M K L N Q R P S hx₀ hz₀ E
  have hF : AnalyticOnNhd ℂ F U := by
    intro y hy
    obtain ⟨hx₀, hz₀, hr⟩ := hrad y hy
    have hratio : AnalyticAt ℂ (fun v => (z v / x v) ^ (2 : ℕ)) y :=
      ((hz y hy).div (hx y hy) hx₀).pow 2
    have henergy := AnalyticAt.comp (g := energySum a) (f := fun v => (z v / x v) ^ (2 : ℕ))
      (energySum_analyticAt a ha (squared_ratio_norm_lt_one hx₀ hr)) hratio
    exact (((hz y hy).zpow (n := pole) hz₀).mul
      ((hx y hy).zpow (n := (N : ℤ) - M) hx₀)).mul henergy
  exact ⟨hF.congr hU (fun y hy => (hsum y hy).tsum_eq.symm),
    fun y hy => (hsum y hy).summable.hasSum⟩

private theorem analytic_tsum_of_finite {ι : Type*} (J : Finset ι)
    {U : Set ℂ} (hU : IsOpen U) {a : ι → ℂ → ℤ × ℤ → ℂ} {F : ι → ℂ → ℂ}
    (hF : ∀ j ∈ J, AnalyticOnNhd ℂ (F j) U)
    (hs : ∀ j ∈ J, ∀ y ∈ U, HasSum (a j y) (F j y))
    {term : ℂ → ℤ × ℤ → ℂ}
    (heq : ∀ y ∈ U, ∀ i, term y i = ∑ j ∈ J, a j y i) :
    AnalyticOnNhd ℂ (fun y => ∑' i, term y i) U ∧
      ∀ y ∈ U, HasSum (term y) (∑' i, term y i) := by
  have hsum (y : ℂ) (hy : y ∈ U) : HasSum (term y) (∑ j ∈ J, F j y) :=
    (hasSum_sum (s := J) fun j hj => hs j hj y hy).congr_fun (heq y hy)
  exact ⟨(J.analyticOnNhd_fun_sum hF).congr hU (fun y hy => (hsum y hy).tsum_eq.symm),
    fun y hy => (hsum y hy).summable.hasSum⟩

private abbrev basisComponent (s : Bool) (u : State s) (i : BasisIndex) : State s :=
  basis.repr u.val i • project s (basis i)

private theorem basisComponent_grade (s : Bool) (u : State s) (i : BasisIndex) :
    (basisComponent s u i).val ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
  change basis.repr u.val i • (project s (basis i)).val ∈ _
  rw [project_val]
  have hi := basis_mem_grade i
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.add_mem _ hi
    (Submodule.smul_mem _ _ (actualParity_preserves_grade ℒ leechUnit _ _ hi))))

set_option maxHeartbeats 1000000 in
/-- Finite expansion in the actual graded basis gives holomorphic native B
sums for arbitrary states on radial charts of nonzero analytic roots. -/
theorem b_joint_product_analytic (s t : Bool)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    {U : Set ℂ} (hU : IsOpen U) {x z : ℂ → ℂ}
    (hx : AnalyticOnNhd ℂ x U) (hz : AnalyticOnNhd ℂ z U)
    (hrad : ∀ y ∈ U, x y ≠ 0 ∧ z y ≠ 0 ∧ ‖z y‖ < ‖x y‖) :
    AnalyticOnNhd ℂ (fun y => ∑' i, bJointTerm s t Q R P S (x y) (z y) i) U ∧
      ∀ y ∈ U, HasSum (bJointTerm s t Q R P S (x y) (z y))
        (∑' i, bJointTerm s t Q R P S (x y) (z y) i) := by
  classical
  let J := (basis.repr Q.val).support ×ˢ ((basis.repr R.val).support ×ˢ
    ((basis.repr P.val).support ×ˢ (basis.repr S.val).support))
  let a (j : BasisIndex × BasisIndex × BasisIndex × BasisIndex) (y : ℂ) :=
    bJointTerm s t (basisComponent s Q j.1) (basisComponent (!s) R j.2.1)
      (basisComponent t P j.2.2.1) (basisComponent (!t) S j.2.2.2) (x y) (z y)
  have h (j : BasisIndex × BasisIndex × BasisIndex × BasisIndex) :
      AnalyticOnNhd ℂ (fun y => ∑' i, a j y i) U ∧
        ∀ y ∈ U, HasSum (a j y) (∑' i, a j y i) :=
    b_joint_product_analytic_of_homogeneous s t
      (oddWeight ℒ j.2.2.1.1) (oddWeight ℒ j.1.1)
      (oddWeight ℒ j.2.1.1) (oddWeight ℒ j.2.2.2.1)
      _ _ _ _ (basisComponent_grade s Q j.1) (basisComponent_grade (!s) R j.2.1)
      (basisComponent_grade t P j.2.2.1) (basisComponent_grade (!t) S j.2.2.2)
      hU hx hz hrad
  refine analytic_tsum_of_finite J hU (a := a) (fun j _ => (h j).1)
    (fun j _ => (h j).2) ?_
  intro y _ i
  simp only [a, ← bModeLinear_apply, J, Finset.sum_product]
  conv_lhs =>
    rw [← sum_projectedBasis s Q]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis (!s) R]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis t P]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis (!t) S]
    simp only [map_sum]

/-- The full native B continuation domain in the upper half-plane. -/
def upperUnitDisk : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ {y : ℂ | 0 < y.im}

private theorem isOpen_upperUnitDisk : IsOpen upperUnitDisk :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

/-- The domain of the upper B branch is preconnected for analytic continuation. -/
theorem isPreconnected_upperUnitDisk : IsPreconnected upperUnitDisk :=
  ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_im_gt 0)).isPreconnected

private theorem upper_sqrt_analytic (y : ℂ) (hy : y ∈ upperUnitDisk) :
    AnalyticAt ℂ Complex.sqrt y :=
  Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane y
    (Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hy.2)))

private theorem upper_sqrt_ne_zero (y : ℂ) (hy : y ∈ upperUnitDisk) :
    Complex.sqrt y ≠ 0 := by
  have hy₀ : y ≠ 0 := by
    intro he
    simpa [he] using hy.2
  have hsq : Complex.sqrt y ^ (2 : ℕ) = y := Complex.cpow_ofNat_inv_pow y 2
  intro he
  exact hy₀ (by simpa [he] using hsq.symm)

private theorem upper_sqrt_norm_lt_one (y : ℂ) (hy : y ∈ upperUnitDisk) :
    ‖Complex.sqrt y‖ < 1 := by
  have hsq : Complex.sqrt y ^ (2 : ℕ) = y := Complex.cpow_ofNat_inv_pow y 2
  have hn : ‖Complex.sqrt y‖ ^ (2 : ℕ) = ‖y‖ := by rw [← norm_pow, hsq]
  have hy₁ := mem_ball_zero_iff.mp hy.1
  by_contra! h
  have hle := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h 2
  rw [one_pow, hn] at hle
  exact (not_le_of_gt hy₁) hle

/-- On the full upper unit disk, the actual mixed B modes at the principal
normalized roots `(1, sqrt y)` sum to a holomorphic function. In BBHH order
both `s` and `t` are true. -/
theorem b_joint_product_analytic_upperDisk (s t : Bool)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t)) :
    AnalyticOnNhd ℂ (fun y => ∑' i, bJointTerm s t Q R P S 1 (Complex.sqrt y) i) upperUnitDisk ∧
      ∀ y ∈ upperUnitDisk, HasSum (bJointTerm s t Q R P S 1 (Complex.sqrt y))
        (∑' i, bJointTerm s t Q R P S 1 (Complex.sqrt y) i) := by
  exact b_joint_product_analytic s t Q R P S
    isOpen_upperUnitDisk analyticOnNhd_const upper_sqrt_analytic
    (fun y hy => ⟨one_ne_zero, upper_sqrt_ne_zero y hy, by
      simpa only [norm_one] using upper_sqrt_norm_lt_one y hy⟩)

/-- The outer target root `D` for the upper slot-(2,3) transport. -/
def physicalOuterRoot (y : ℂ) : ℂ :=
  I / (Complex.sqrt y * Complex.sqrt (1 - y))

/-- The inner target root `I * Z` for the upper slot-(2,3) transport. -/
def physicalInnerRoot (y : ℂ) : ℂ :=
  I / Complex.sqrt (1 - y)

private theorem one_sub_mem_slitPlane (y : ℂ) (hy : y ∈ upperUnitDisk) :
    1 - y ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero] using ne_of_gt hy.2

private theorem one_sub_sqrt_ne_zero (y : ℂ) (hy : y ∈ upperUnitDisk) :
    Complex.sqrt (1 - y) ≠ 0 := by
  have hsq : Complex.sqrt (1 - y) ^ (2 : ℕ) = 1 - y :=
    Complex.cpow_ofNat_inv_pow (1 - y) 2
  intro he
  exact Complex.slitPlane_ne_zero (one_sub_mem_slitPlane y hy) (by simpa [he] using hsq.symm)

private theorem one_sub_sqrt_analytic (y : ℂ) (hy : y ∈ upperUnitDisk) :
    AnalyticAt ℂ (fun v : ℂ => Complex.sqrt (1 - v)) y :=
  AnalyticAt.comp (f := fun v : ℂ => 1 - v) (g := Complex.sqrt)
    (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane (1 - y)
      (one_sub_mem_slitPlane y hy)) (analyticAt_const.sub analyticAt_id)

/-- The normalized root inherited from the physical transport is the
principal square root throughout the upper unit disk. -/
theorem physical_root_ratio {y : ℂ} (hy : y ∈ upperUnitDisk) :
    physicalInnerRoot y / physicalOuterRoot y = Complex.sqrt y := by
  unfold physicalInnerRoot physicalOuterRoot
  field_simp [upper_sqrt_ne_zero y hy, one_sub_sqrt_ne_zero y hy, Complex.I_ne_zero]

private theorem physical_chart :
    AnalyticOnNhd ℂ physicalOuterRoot upperUnitDisk ∧
      AnalyticOnNhd ℂ physicalInnerRoot upperUnitDisk ∧
      ∀ y ∈ upperUnitDisk, physicalOuterRoot y ≠ 0 ∧ physicalInnerRoot y ≠ 0 ∧
        ‖physicalInnerRoot y‖ < ‖physicalOuterRoot y‖ := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact analyticAt_const.div ((upper_sqrt_analytic y hy).mul (one_sub_sqrt_analytic y hy))
      (mul_ne_zero (upper_sqrt_ne_zero y hy) (one_sub_sqrt_ne_zero y hy))
  · intro y hy
    exact analyticAt_const.div (one_sub_sqrt_analytic y hy) (one_sub_sqrt_ne_zero y hy)
  · intro y hy
    have hz := one_sub_sqrt_ne_zero y hy
    have hx : physicalOuterRoot y ≠ 0 :=
      div_ne_zero Complex.I_ne_zero (mul_ne_zero (upper_sqrt_ne_zero y hy) hz)
    refine ⟨hx, div_ne_zero Complex.I_ne_zero hz, ?_⟩
    have h := upper_sqrt_norm_lt_one y hy
    rw [← physical_root_ratio hy, norm_div] at h
    exact (div_lt_one (norm_pos_iff.mpr hx)).mp h

/-- The actual B sum is holomorphic at the target roots of the physical
upper slot-(2,3) transport on the full upper unit disk. -/
theorem b_joint_product_analytic_physical (s t : Bool)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t)) :
    AnalyticOnNhd ℂ (fun y => ∑' i,
      bJointTerm s t Q R P S (physicalOuterRoot y) (physicalInnerRoot y) i) upperUnitDisk ∧
      ∀ y ∈ upperUnitDisk,
        HasSum (bJointTerm s t Q R P S (physicalOuterRoot y) (physicalInnerRoot y))
          (∑' i, bJointTerm s t Q R P S (physicalOuterRoot y) (physicalInnerRoot y) i) :=
  b_joint_product_analytic s t Q R P S isOpen_upperUnitDisk
    physical_chart.1 physical_chart.2.1 physical_chart.2.2

set_option maxHeartbeats 1000000 in
/-- The physical B sum with the detector translated by the finite upper
slot-(2,3) exponential is holomorphic on the full upper unit disk. The
monomials use the inherited source root `Z = 1 / sqrt (1 - y)`. -/
theorem b_joint_product_analytic_physical_translated (s t : Bool) (N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t)) :
    let weight (j : ℕ) (y : ℂ) :=
      ((1 / Complex.sqrt (1 - y)) ^ (2 : ℕ)) ^ j / (j.factorial : ℂ)
    let translated (y : ℂ) : State (!t) :=
      ∑ j ∈ Finset.range (N / 2 + 1), weight j y • (L₁ (!t) ^ j) S
    let B (y : ℂ) := ∑' i,
      bJointTerm s t Q R P (translated y) (physicalOuterRoot y) (physicalInnerRoot y) i
    AnalyticOnNhd ℂ B upperUnitDisk ∧
      ∀ y ∈ upperUnitDisk, HasSum
        (bJointTerm s t Q R P (translated y) (physicalOuterRoot y) (physicalInnerRoot y)) (B y) := by
  dsimp only
  let weight (j : ℕ) (y : ℂ) :=
    ((1 / Complex.sqrt (1 - y)) ^ (2 : ℕ)) ^ j / (j.factorial : ℂ)
  let term (j : ℕ) (y : ℂ) :=
    bJointTerm s t Q R P ((L₁ (!t) ^ j) S) (physicalOuterRoot y) (physicalInnerRoot y)
  have hw (j : ℕ) : AnalyticOnNhd ℂ (weight j) upperUnitDisk := by
    intro y hy
    have h : AnalyticAt ℂ (fun v : ℂ => 1 / Complex.sqrt (1 - v)) y :=
      analyticAt_const.div (one_sub_sqrt_analytic y hy) (one_sub_sqrt_ne_zero y hy)
    exact ((h.pow 2).pow j).div_const
  have ha (j : ℕ) := b_joint_product_analytic_physical s t Q R P ((L₁ (!t) ^ j) S)
  refine analytic_tsum_of_finite (Finset.range (N / 2 + 1)) isOpen_upperUnitDisk
    (a := fun j y i => weight j y * term j y i)
    (F := fun j y => weight j y * ∑' i, term j y i)
    (fun j _ y hy => (hw j y hy).mul ((ha j).1 y hy))
    (fun j _ y hy => ((ha j).2 y hy).mul_left (weight j y)) ?_
  intro y _ i
  simp only [← bModeLinear_apply, term, weight, map_sum, map_smul, smul_eq_mul]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductUpperDisk
