/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldTraceSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldTraceSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute analytic character of the actual Leech orbifold stress grades. -/

import D5.S3.Arith.Lattices.LatticeThetaTransformation
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldAllWeightDimension
import D5.S3.VertexAlgebra.Characters.LatticeFourCurrentThermal
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.Discriminant

/-! The absolutely convergent character of the native Leech stress eigenspaces.
The untwisted series is regrouped by energy, and the twisted parity difference
is reindexed from odd oscillator degrees to integer weights. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Function Matrix
open UpperHalfPlane hiding I
open scoped BigOperators

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (leechUnit leechPosDef)
open ActualLeechOrbifoldAllWeightDimension
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeThetaCharacter LatticeHalfFockCharacter LatticeHalfFockParityT
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (bRank actual_ground_finrank actual_grade_insert_trace_bRank)
open LatticeFourCurrentThermal (ordinary_oscillator_hasProd)
open D5.S3.Arith.Lattices.LatticeThetaTransformation (latticeTheta)
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open D5.S3.Fourier.MatrixGaussian (quadratic summable_norm_theta)

local notation "D" => leechData
local notation "H" => actualInverse D
local notation "hHG" => actualInverse_left D leechUnit
local notation "hGH" => actualInverse_right D leechUnit
local notation "𝕢" => Periodic.qParam 1

private theorem q_eq_exp (τ : ℍ) : 𝕢 τ = exp (2 * Real.pi * I * (τ : ℂ)) := by
  simp [Periodic.qParam]

private theorem q_norm (τ : ℍ) : ‖𝕢 τ‖ < 1 :=
  Periodic.norm_qParam_lt_one one_pos τ.im_pos

/-- The identity trace on each actual untwisted grade. -/
def ordinaryTrace (n : ℤ) : ℂ :=
  LinearMap.trace ℂ (UntwistedWeight n) LinearMap.id

/-- The trace normalization subtracts the vacuum energy 24/24. -/
def ordinaryCharacter (τ : ℍ) : ℂ :=
  (𝕢 τ)⁻¹ * ∑' n : ℕ, ordinaryTrace n * 𝕢 τ ^ n

/-- The dimension of the literal assembled stress eigenspace. -/
def dimension (n : ℤ) : ℕ := Module.finrank ℂ (OrbifoldWeight n)

/-- The character with the central-charge shift made explicit. -/
def character (τ : ℍ) : ℂ :=
  (𝕢 τ)⁻¹ * ∑' n : ℕ, (dimension n : ℂ) * 𝕢 τ ^ n

theorem ordinaryTrace_eq_card (n : ℤ) :
    ordinaryTrace n = (Nat.card (EnergyFiber D n) : ℂ) := by
  rw [ordinaryTrace, LinearMap.trace_id]
  exact congrArg (fun d : ℕ => (d : ℂ)) (calc
    Module.finrank ℂ (UntwistedWeight n) = Module.finrank ℂ (grade D n) := by
      rw [show UntwistedWeight n = grade D n from actualL0_eigenspace_eq_grade D H hHG hGH n]
    _ = Nat.card (EnergyFiber D n) := Module.finrank_eq_nat_card_basis (gradeBasis D n))

private def chargeDegree (a : Charge D) : ℕ := (chargeEnergy D a).toNat

private theorem chargeDegree_cast (a : Charge D) : (chargeDegree a : ℤ) = chargeEnergy D a :=
  Int.toNat_of_nonneg (chargeEnergy_nonneg D leechPosDef a)

private theorem charge_term (τ : ℍ) (a : Charge D) :
    exp (Real.pi * I * (τ : ℂ) * (bilinear D a a : ℂ)) = 𝕢 τ ^ chargeDegree a := by
  have h : (bilinear D a a : ℂ) = 2 * (chargeDegree a : ℂ) := by
    have h := (two_chargeEnergy D a).symm
    rw [← chargeDegree_cast a] at h
    exact_mod_cast h
  rw [q_eq_exp, ← exp_nat_mul, h]
  congr 1
  ring

private theorem charge_absolute (τ : ℍ) :
    Summable (fun a : Charge D => ‖𝕢 τ ^ chargeDegree a‖) := by
  have h := summable_norm_theta (leechData.G.map (Int.castRingHom ℝ))
    leechPosDef τ τ.im_pos
  have hquadratic (a : Charge D) :
      quadratic (leechData.G.map (Int.castRingHom ℝ)) (fun i => (a i : ℝ)) =
        (bilinear D a a : ℝ) := by
    simp [quadratic, bilinear, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc]
  simpa only [hquadratic, Complex.ofReal_intCast, charge_term τ] using h

private theorem occupation_absolute (τ : ℍ) :
    Summable (fun d : Exponent D => ‖𝕢 τ ^ oscillatorEnergy d‖) := by
  simpa [signedIntegerMonomial, integerEnergy, oscillatorEnergy] using
    summable_norm_signed_integer_occupations (Fin leechData.rank) (q_norm τ)

private theorem normalized_occupation_eq_eta (τ : ℍ) :
    (𝕢 τ)⁻¹ * (∑' d : Exponent D, 𝕢 τ ^ oscillatorEnergy d) =
      (ModularForm.eta τ ^ (24 : ℕ))⁻¹ := by
  have hp := ordinary_oscillator_hasProd D (𝕢 τ) (q_norm τ)
  rw [leech_spec.1] at hp
  have hz : (∏' n : ℕ, (1 - 𝕢 τ ^ (n + 1))) ≠ 0 := by
    simpa [ModularForm.eta_q] using ModularForm.eta_tprod_ne_zero τ.im_pos
  have hprod := ModularForm.multipliable_one_sub_pow (q_norm τ)
  have he := (hprod.hasProd.inv₀ hz).pow 24
  have heta : ModularForm.eta τ ^ (24 : ℕ) =
      𝕢 τ * (∏' n : ℕ, (1 - 𝕢 τ ^ (n + 1))) ^ (24 : ℕ) := by
    calc
      _ = 𝕢 τ * (∏' n : ℕ, (1 - 𝕢 τ ^ (n + 1)) ^ (24 : ℕ)) :=
        ModularForm.discriminant_eq_q_prod τ
      _ = _ := congrArg (fun z : ℂ => 𝕢 τ * z) (hprod.tprod_pow 24)
  rw [hp.unique he, heta, _root_.mul_inv_rev, inv_pow]
  exact mul_comm _ _

private def labelDegree (x : Label D) : ℕ := chargeDegree x.1 + oscillatorEnergy x.2

private theorem labelDegree_cast (x : Label D) : (labelDegree x : ℤ) = energy D x := by
  simp only [labelDegree, Nat.cast_add, chargeDegree_cast, energy]

private def degreeFiberEquiv (n : ℕ) :
    {x : Label D // labelDegree x = n} ≃ EnergyFiber D (n : ℤ) where
  toFun x := ⟨x.1, (labelDegree_cast x.1).symm.trans (congrArg (fun m : ℕ => (m : ℤ)) x.2)⟩
  invFun x := ⟨x.1, by
    have h : (labelDegree x.1 : ℤ) = n := (labelDegree_cast x.1).trans x.2
    exact_mod_cast h⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 1200000 in
/-- Regroup the absolutely summable joint basis by the actual finite energy fibers,
then evaluate the separate charge and oscillator sums. -/
theorem ordinary_trace_series (τ : ℍ) :
    Summable (fun n : ℕ => ‖ordinaryTrace n * 𝕢 τ ^ n‖) ∧
      ordinaryCharacter τ = latticeTheta D τ / ModularForm.eta τ ^ (24 : ℕ) := by
  classical
  let f : Label D → ℂ := fun x => 𝕢 τ ^ labelDegree x
  have hfactor (x : Label D) : f x =
      𝕢 τ ^ chargeDegree x.1 * 𝕢 τ ^ oscillatorEnergy x.2 :=
    pow_add _ _ _
  have habs : Summable (fun x => ‖f x‖) := by
    have hprod := Summable.mul_norm (f := fun a : Charge D => 𝕢 τ ^ chargeDegree a)
      (g := fun d : Exponent D => 𝕢 τ ^ oscillatorEnergy d)
      (charge_absolute τ) (occupation_absolute τ)
    exact hprod.congr (fun x => congrArg norm (hfactor x).symm)
  have hfiber (n : ℕ) :
      (∑' x : {x : Label D // labelDegree x = n}, f x.1) = ordinaryTrace n * 𝕢 τ ^ n := by
    let : Finite (EnergyFiber D (n : ℤ)) := energyFiber_finite D leechPosDef (n : ℤ)
    let : Fintype (EnergyFiber D (n : ℤ)) := Fintype.ofFinite _
    calc
      _ = ∑' _ : {x : Label D // labelDegree x = n}, 𝕢 τ ^ n := by
        apply tsum_congr
        intro x
        exact congrArg (fun m : ℕ => 𝕢 τ ^ m) x.2
      _ = ∑' _ : EnergyFiber D (n : ℤ), 𝕢 τ ^ n :=
        (degreeFiberEquiv n).tsum_eq (fun _ : EnergyFiber D (n : ℤ) => 𝕢 τ ^ n)
      _ = _ := by
        rw [ordinaryTrace_eq_card, Nat.card_eq_fintype_card, tsum_fintype]
        simp [nsmul_eq_mul]
  have hnorm (n : ℕ) :
      ‖ordinaryTrace n * 𝕢 τ ^ n‖ ≤
        ∑' x : {x : Label D // labelDegree x = n}, ‖f x.1‖ := by
    rw [← hfiber n]
    exact norm_tsum_le_tsum_norm (habs.subtype (fun x => labelDegree x = n))
  have hgroup := habs.hasSum.tsum_fiberwise labelDegree
  have hs : HasSum (fun n : ℕ => ordinaryTrace n * 𝕢 τ ^ n) (∑' x, f x) :=
    (habs.of_norm.hasSum.tsum_fiberwise labelDegree).congr_fun (fun n => (hfiber n).symm)
  refine ⟨hgroup.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm, ?_⟩
  rw [ordinaryCharacter, hs.tsum_eq]
  simp_rw [hfactor]
  rw [← tsum_mul_tsum_of_summable_norm (charge_absolute τ) (occupation_absolute τ)]
  have htheta : (∑' a : Charge D, 𝕢 τ ^ chargeDegree a) = latticeTheta D τ :=
    tsum_congr (fun a => (charge_term τ a).symm)
  rw [htheta, mul_left_comm, normalized_occupation_eq_eta, div_eq_mul_inv]

local notation "BTrace" => positiveFullThetaTrace D H hHG hGH leechPosDef
local notation "B" => positiveFullThetaCharacter D H hHG hGH leechPosDef
local notation "U" => actualInsertedCharacter D leechUnit LinearMap.id
local notation "P" => actualParityInsertedCharacter D leechUnit LinearMap.id

/-- The homogeneous fixed projection contributes half the sum of the ordinary
trace and the signed involution trace, with the negative twisted grade added. -/
theorem homogeneous_projection (n : ℤ) :
    (dimension n : ℂ) = (ordinaryTrace n + BTrace n) / 2 + (twistedMultiplicity n : ℂ) := by
  rw [dimension, (weightEquiv n).finrank_eq, Module.finrank_prod, Nat.cast_add,
    fixed_weight_finrank_eq_trace n, twisted_weight_finrank n, ordinaryTrace, LinearMap.trace_id]

set_option maxHeartbeats 1200000 in
private theorem normalized_twisted_series (τ : ℍ) :
    Summable (fun n : ℕ => ‖(𝕢 τ)⁻¹ * ((twistedMultiplicity n : ℂ) * 𝕢 τ ^ n)‖) ∧
    HasSum (fun n : ℕ => (𝕢 τ)⁻¹ * ((twistedMultiplicity n : ℂ) * 𝕢 τ ^ n))
      ((U τ - P τ) / 2) := by
  let t := exp (Real.pi * I * (τ : ℂ))
  have hsq : t ^ 2 = 𝕢 τ := by
    calc
      t ^ 2 = exp (((2 : ℕ) : ℂ) * (Real.pi * I * (τ : ℂ))) := (exp_nat_mul _ 2).symm
      _ = 𝕢 τ := by
        rw [q_eq_exp]
        congr 1
        push_cast
        ring
  have hv : exp (2 * Real.pi * I * (τ : ℂ) * leechData.rank / 48) = t := by
    rw [leech_spec.1]
    dsimp [t]
    congr 1
    push_cast
    ring
  let u := actualTraceTerm D leechUnit LinearMap.id t
  let p := actualParityTraceTerm D leechUnit LinearMap.id t
  have hu := actual_character_modular D leechUnit LinearMap.id τ τ.im_pos
  have hU : HasSum (fun n => t * u n) (U τ) := by
    rw [hu.2.2.1]
    simpa only [hv, u] using hu.2.1
  have hP : HasSum (fun n => t * p n) (P τ) := by
    simpa only [hv, p] using
      (actual_parity_character_series D leechUnit LinearMap.id τ τ.im_pos).2
  let diff : ℕ → ℂ := fun n => (t * u n - t * p n) / 2
  have hdiff : HasSum diff ((U τ - P τ) / 2) := (hU.sub hP).div_const 2
  have hpar (n : ℕ) : p n = (-1 : ℂ) ^ n * u n := by
    simp only [p, u, actualParityTraceTerm, actualTraceTerm, actualParityTraceTerm_eq]
    ring
  have hground : Module.finrank ℂ (ActualGround D leechUnit) = 4096 := by
    rw [actual_ground_finrank, leech_spec.1] <;> norm_num
  have hcount (n : ℕ) : u n = (4096 : ℂ) * (bRank 24 n : ℂ) * t ^ n := by
    dsimp only [u, actualTraceTerm]
    rw [actual_grade_insert_trace_bRank, LinearMap.trace_id, hground, leech_spec.1]
    change (bRank 24 n : ℂ) * 4096 * t ^ n = _
    ring
  have heven (k : ℕ) : diff (2 * k) = 0 := by
    dsimp only [diff]
    rw [hpar, neg_one_pow_eq_pow_mod_two, show (2 * k) % 2 = 0 by omega]
    simp
  have hodd (k : ℕ) : diff (2 * k + 1) =
      (4096 : ℂ) * (bRank 24 (2 * k + 1) : ℂ) * 𝕢 τ ^ (k + 1) := by
    have htq : t * t ^ (2 * k + 1) = 𝕢 τ ^ (k + 1) := calc
      _ = t ^ (2 * k + 1 + 1) := (pow_succ' t (2 * k + 1)).symm
      _ = t ^ (2 * (k + 1)) := congrArg (fun n : ℕ => t ^ n) (by omega)
      _ = _ := by rw [pow_mul, hsq]
    dsimp only [diff]
    rw [hpar, neg_one_pow_eq_pow_mod_two, show (2 * k + 1) % 2 = 1 by omega, pow_one, hcount]
    calc
      _ = (4096 : ℂ) * (bRank 24 (2 * k + 1) : ℂ) * (t * t ^ (2 * k + 1)) := by ring
      _ = _ := by rw [htq]
  have hoddInjective : Injective (fun k : ℕ => 2 * k + 1) := by
    intro k l h
    change 2 * k + 1 = 2 * l + 1 at h
    omega
  have hoddSummable : Summable (fun k : ℕ => diff (2 * k + 1)) :=
    hdiff.summable.comp_injective hoddInjective
  have hsumOdd : HasSum (fun k : ℕ => diff (2 * k + 1)) ((U τ - P τ) / 2) := by
    have hevenSummable : Summable (fun k : ℕ => diff (2 * k)) := by
      simp only [heven, summable_zero]
    have h := tsum_even_add_odd hevenSummable hoddSummable
    simp only [heven, tsum_zero, zero_add, hdiff.tsum_eq] at h
    exact h ▸ hoddSummable.hasSum
  let weightTerm : ℕ → ℂ := fun n => (𝕢 τ)⁻¹ * ((twistedMultiplicity n : ℂ) * 𝕢 τ ^ n)
  have hq0 : 𝕢 τ ≠ 0 := Periodic.qParam_ne_zero (h := 1) (τ : ℂ)
  have hshift (k : ℕ) : weightTerm (k + 2) = diff (2 * k + 1) := by
    have hge : (2 : ℤ) ≤ ((k + 2 : ℕ) : ℤ) := by omega
    have hidx : (2 * ((k + 2 : ℕ) : ℤ) - 3).toNat = 2 * k + 1 := by omega
    rw [hodd]
    simp only [weightTerm, twistedMultiplicity, ite_eq_left hge, hidx, Nat.cast_mul,
      Nat.cast_ofNat]
    have hpow : 𝕢 τ ^ (k + 2) = 𝕢 τ ^ (k + 1) * 𝕢 τ := pow_succ (𝕢 τ) (k + 1)
    calc
      _ = ((𝕢 τ)⁻¹ * 𝕢 τ) * ((4096 : ℂ) * (bRank 24 (2 * k + 1) : ℂ) *
          𝕢 τ ^ (k + 1)) := by
        rw [hpow]
        ring
      _ = _ := by rw [inv_mul_cancel₀ hq0, one_mul]
  have hshiftSum : HasSum (fun k : ℕ => weightTerm (k + 2)) ((U τ - P τ) / 2) :=
    hsumOdd.congr_fun hshift
  have hzero : weightTerm 0 = 0 := by
    simp only [weightTerm, twistedMultiplicity, ite_eq_right (by decide : ¬ (2 : ℤ) ≤ 0),
      Nat.cast_zero, zero_mul, mul_zero]
  have hone : weightTerm 1 = 0 := by
    norm_num [weightTerm, twistedMultiplicity]
  have hsum : HasSum weightTerm ((U τ - P τ) / 2) := by
    have h := (hasSum_nat_add_iff (f := weightTerm) 2).mp hshiftSum
    simpa [Finset.sum_range_succ, hzero, hone] using h
  exact ⟨summable_norm_iff.mpr hsum.summable, hsum⟩

set_option maxHeartbeats 1200000 in
/-- Absolute q-summability and the half-sum of the four literal finite-grade traces. -/
theorem graded_dimension_series (τ : ℍ) :
    Summable (fun n : ℕ => ‖(dimension n : ℂ) * 𝕢 τ ^ n‖) ∧
    HasSum (fun n : ℕ => (𝕢 τ)⁻¹ * ((dimension n : ℂ) * 𝕢 τ ^ n))
      ((ordinaryCharacter τ + B τ + U τ - P τ) / 2) := by
  have hA := (ordinary_trace_series τ).1.of_norm
  have hB := (positive_full_theta_character D H hHG hGH leechPosDef (q_norm τ)).2.1.of_norm
  have sumA : HasSum (fun n : ℕ => (𝕢 τ)⁻¹ * (ordinaryTrace n * 𝕢 τ ^ n))
      (ordinaryCharacter τ) :=
    hA.hasSum.mul_left (𝕢 τ)⁻¹
  have sumB : HasSum (fun n : ℕ => (𝕢 τ)⁻¹ * (BTrace n * 𝕢 τ ^ n)) (B τ) := by
    have hv : exp (-2 * Real.pi * I * (τ : ℂ) * leechData.rank / 24) = (𝕢 τ)⁻¹ := by
      rw [leech_spec.1, q_eq_exp, ← exp_neg]
      congr 1
      push_cast
      ring
    rw [positiveFullThetaCharacter, hv, ← q_eq_exp τ]
    exact hB.hasSum.mul_left (𝕢 τ)⁻¹
  have hsum := ((sumA.add sumB).div_const 2).add (normalized_twisted_series τ).2
  have htarget : (ordinaryCharacter τ + B τ) / 2 + (U τ - P τ) / 2 =
      (ordinaryCharacter τ + B τ + U τ - P τ) / 2 := by ring
  rw [htarget] at hsum
  have h : HasSum (fun n : ℕ => (𝕢 τ)⁻¹ * ((dimension n : ℂ) * 𝕢 τ ^ n))
      ((ordinaryCharacter τ + B τ + U τ - P τ) / 2) := by
    refine hsum.congr_fun fun n => ?_
    rw [homogeneous_projection]
    ring
  refine ⟨summable_norm_iff.mpr ?_, h⟩
  simpa only [mul_inv_cancel_left₀ (Periodic.qParam_ne_zero (h := 1) (τ : ℂ))] using
    (h.mul_left (𝕢 τ)).summable

end D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries

#print axioms D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries.ordinary_trace_series
#print axioms D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries.graded_dimension_series
