/- GID: D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/RealignmentSchurBound
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Sharp elementary-symmetric tail bounds for actual separable realignment spectra. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Analytic.RealRootedCoefficientNewton
import D5.S3.Analytic.HypergeometricShiftTuran.Defs
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.Basic

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormCovariance
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false
noncomputable section

open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped BigOperators Kronecker MatrixOrder ComplexOrder
open Finset
open scoped Topology

namespace D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound

open D5.S3.Quantum.Information.SLDSpectralEnergy

/-- The realignment used by Li--Poon--Sze, with Alice indices first. -/
def realign {ι κ : Type*}
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix (ι × ι) (κ × κ) ℂ :=
  fun (i,j) (a,b) => ρ (i,a) (j,b)

/-- The row-side singular-value vector, obtained from the row Gram matrix.
For realignment with Alice dimension at most Bob dimension, its length is m². -/
def singularVector {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : Fin (Fintype.card ι) → ℝ :=
  fun i => A.conjTranspose.toEuclideanLin.singularValues i

/-- The ℓ-th elementary symmetric function of the rectangular singular values. -/
def esymmSV {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ℓ : ℕ) (A : Matrix ι κ ℂ) : ℝ :=
  (Finset.univ.val.map (singularVector A)).esymm ℓ

/-- Elementary symmetric evaluation on a finite real vector. -/
def esymmVec {k : ℕ} (ℓ : ℕ) (x : Fin k → ℝ) : ℝ :=
  (Finset.univ.val.map x).esymm ℓ

private lemma esymmVec_eq_sum {k ℓ : ℕ} (x : Fin k → ℝ) :
    esymmVec ℓ x = ∑ t ∈ Finset.powersetCard ℓ Finset.univ, t.prod x := by
  exact Finset.esymm_map_val _ _ _

private lemma esymmVec_mono {k ℓ : ℕ} {x y : Fin k → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    esymmVec ℓ x ≤ esymmVec ℓ y := by
  rw [esymmVec_eq_sum, esymmVec_eq_sum]
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.prod_le_prod₀
  · intro i hi
    exact hx i
  · intro i hi
    exact hxy i



/-- The common tail coordinate of a unit-mass profile with k coordinates. -/
def tailMean (k : ℕ) (a : ℝ) : ℝ := (1 - a) / (k - 1 : ℕ)

/-- The elementary-symmetric polynomial at (a,b,...,b), b=(1-a)/(k-1). -/
def schurProfile (k ℓ : ℕ) (a : ℝ) : ℝ :=
  ((k - 1).choose ℓ : ℝ) * tailMean k a ^ ℓ +
    ((k - 1).choose (ℓ - 1) : ℝ) * a * tailMean k a ^ (ℓ - 1)

private lemma tailMean_hasDerivAt (k : ℕ) (a : ℝ) :
    HasDerivAt (tailMean k) (-1 / (k - 1 : ℕ)) a := by
  convert! ((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)).div_const (k - 1 : ℕ) using 1 <;> simp [tailMean]

/-- Differentiation exposes the difference between the distinguished coordinate and its tail. -/
private theorem schurProfile_hasDerivAt {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 2 ≤ ℓ)
    (hℓk : ℓ ≤ k) (a : ℝ) :
    HasDerivAt (schurProfile k ℓ)
      (((ℓ - 1 : ℕ) : ℝ) / (k - 1 : ℕ) * ((k - 1).choose (ℓ - 1) : ℝ) *
        tailMean k a ^ (ℓ - 2) * (tailMean k a - a)) a := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  have hk0 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
  have hc := Nat.choose_succ_right_eq (k - 1) (r + 1)
  have hc' : ((k - 1).choose (r + 2) : ℝ) * (r + 2 : ℝ) =
      ((k - 1).choose (r + 1) : ℝ) * ((k - 1 : ℕ) - (r + 1) : ℕ) := by
    exact_mod_cast hc
  have hcast : (((k - 1 : ℕ) - (r + 1) : ℕ) : ℝ) =
      ((k - 1 : ℕ) : ℝ) - (r + 1 : ℝ) := by
    rw [Nat.cast_sub (show r + 1 ≤ k - 1 by omega)]
    norm_num
  rw [hcast] at hc'
  have hr1 : 2 + r - 1 = r + 1 := by omega
  have hr2 : 2 + r - 2 = r := by omega
  have hr3 : r + 2 - 1 = r + 1 := by omega
  have hd := (((tailMean_hasDerivAt k a).pow (r + 2)).const_mul
      ((k - 1).choose (r + 2) : ℝ)).add
    (((hasDerivAt_id a).mul ((tailMean_hasDerivAt k a).pow (r + 1))).const_mul
      ((k - 1).choose (r + 1) : ℝ))
  convert hd using 1
  · ext x
    simp [schurProfile, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mul_assoc]
  · simp only [hr1, hr2, hr3, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, Pi.mul_apply, Pi.pow_apply, id_eq, one_mul, Nat.add_sub_cancel] at *
    field_simp [hk0]
    simp only [pow_succ]
    linear_combination tailMean k a ^ r * tailMean k a * hc' 

/-- The elementary-symmetric profile strictly decreases above the uniform coordinate. -/
private theorem schurProfile_strictAntiOn {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 2 ≤ ℓ)
    (hℓk : ℓ ≤ k) :
    StrictAntiOn (schurProfile k ℓ) (Set.Icc (1 / (k : ℝ)) 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hqpos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro a ha
    exact (schurProfile_hasDerivAt hk hℓ hℓk a).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Icc] at ha
    rw [(schurProfile_hasDerivAt hk hℓ hℓk a).deriv]
    have hb : 0 < tailMean k a := div_pos (by linarith [ha.2]) hqpos
    have hba : tailMean k a < a := by
      rw [tailMean, div_lt_iff₀ hqpos]
      have hqa : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ k by omega)]; norm_num
      rw [hqa]
      have hka : 1 < a * k := (div_lt_iff₀ hkpos).mp ha.1
      nlinarith
    have hchoose : (0 : ℝ) < ((k - 1).choose (ℓ - 1) : ℝ) := by
      exact_mod_cast (Nat.choose_pos (show ℓ - 1 ≤ k - 1 by omega))
    exact mul_neg_of_pos_of_neg
      (mul_pos (mul_pos (div_pos (by exact_mod_cast (show 0 < ℓ - 1 by omega)) hqpos)
        hchoose) (pow_pos hb _)) (sub_neg.mpr hba)

/-- The complement of the normalized covariance tail budget. -/
def separableThreshold (m n : ℕ) : ℝ :=
  1 - Real.sqrt ((1 - 1 / (m : ℝ)) * (1 - 1 / (n : ℝ)))

private theorem complement_sqrt_gt_half {x y : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1) :
    x / 2 < 1 - Real.sqrt ((1 - x) * (1 - y)) := by
  have hc := Real.sq_sqrt (mul_nonneg (by linarith : 0 ≤ 1 - x) (by linarith : 0 ≤ 1 - y))
  have hs := Real.sqrt_nonneg ((1 - x) * (1 - y))
  have hp : 0 < y * (1 - x) := mul_pos hy (by linarith)
  nlinarith [sq_nonneg (Real.sqrt ((1 - x) * (1 - y)) - (1 - x / 2))]

private theorem complement_sqrt_gt_geometric {x y : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hyx : y < x) :
    Real.sqrt (x * y) < 1 - Real.sqrt ((1 - x) * (1 - y)) := by
  have hy1 : y < 1 := hyx.trans hx1
  have ha := Real.sq_sqrt hx.le
  have hb := Real.sq_sqrt hy.le
  have ha0 := Real.sqrt_nonneg x
  have hb0 := Real.sqrt_nonneg y
  have hab : Real.sqrt y < Real.sqrt x := Real.sqrt_lt_sqrt hy.le hyx
  have ha1 : Real.sqrt x < 1 := by nlinarith
  have hb1 : Real.sqrt y < 1 := by nlinarith
  have hab1 : Real.sqrt x * Real.sqrt y < 1 := by nlinarith
  have hc := Real.sq_sqrt (mul_nonneg (by linarith : 0 ≤ 1 - x) (by linarith : 0 ≤ 1 - y))
  have hc0 := Real.sqrt_nonneg ((1 - x) * (1 - y))
  rw [Real.sqrt_mul hx.le]
  have hgap : Real.sqrt ((1 - x) * (1 - y)) ^ 2 <
      (1 - Real.sqrt x * Real.sqrt y) ^ 2 := by
    calc
      _ = (1 - Real.sqrt x ^ 2) * (1 - Real.sqrt y ^ 2) := by rw [hc, ha, hb]
      _ < _ := by nlinarith only [sq_pos_of_pos (sub_pos.mpr hab)]
  have hlt : Real.sqrt ((1 - x) * (1 - y)) < 1 - Real.sqrt x * Real.sqrt y :=
    (sq_lt_sq₀ hc0 (by linarith)).mp hgap
  linarith

/-- Every rectangular separability threshold lies strictly above 1/(2m). -/
private theorem separableThreshold_gt_half {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    1 / (2 * (m : ℝ)) < separableThreshold m n := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hx : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hy : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hh := complement_sqrt_gt_half hx ((div_lt_one (by positivity)).mpr hm1)
    hy ((div_lt_one (by positivity)).mpr hn1)
  unfold separableThreshold
  convert hh using 1 <;> ring

/-- The LPS leading singular value is strictly below the separability threshold. -/
private theorem separableThreshold_gt_alpha {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    1 / Real.sqrt ((m : ℝ) * n) < separableThreshold m n := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hm0 : (0 : ℝ) < m := by positivity
  have hn0 : (0 : ℝ) < n := hm0.trans hmn'
  have hh := complement_sqrt_gt_geometric (one_div_pos.mpr hm0)
    ((div_lt_one hm0).mpr hm1) (one_div_pos.mpr hn0)
    ((one_div_lt_one_div hn0 hm0).mpr hmn')
  unfold separableThreshold
  convert hh using 1
  rw [one_div_mul_one_div, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]

/-- The threshold remains inside the unit-mass profile interval. -/
theorem separableThreshold_lt_one {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    separableThreshold m n < 1 := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hx : 0 < 1 - 1 / (m : ℝ) := by
    have := (div_lt_one (by positivity : (0 : ℝ) < m)).mpr hm1
    linarith
  have hy : 0 < 1 - 1 / (n : ℝ) := by
    have := (div_lt_one (by positivity : (0 : ℝ) < n)).mpr hn1
    linarith
  have := Real.sqrt_pos.mpr (mul_pos hx hy)
  unfold separableThreshold
  linarith

/-- The covariance threshold is strictly above the uniform leading coordinate. -/
theorem separableThreshold_gt_uniform {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    1 / ((m : ℝ) ^ 2) < separableThreshold m n := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < 2 * m := by positivity
  have hden : 2 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  exact lt_of_le_of_lt (one_div_le_one_div_of_le hp hden) (separableThreshold_gt_half hm hn)

/-- In the exceptional band the supported witness's leading coordinate is
strictly between the uniform coordinate and 1/(2m). -/
private theorem exceptional_alpha_bounds {m : ℕ} (hm : 3 ≤ m) :
    1 / ((m : ℝ) ^ 2) < 1 / ((m : ℝ) * Real.sqrt ((m : ℝ)^2 - 1)) ∧
    1 / ((m : ℝ) * Real.sqrt ((m : ℝ)^2 - 1)) < 1 / (2 * (m : ℝ)) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hx : 0 ≤ (m : ℝ)^2 - 1 := by nlinarith
  have hs := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg ((m : ℝ)^2 - 1)
  have hs2 : 2 < Real.sqrt ((m : ℝ)^2 - 1) := by nlinarith
  have hsm : Real.sqrt ((m : ℝ)^2 - 1) < m := by nlinarith
  constructor
  · apply (one_div_lt_one_div (sq_pos_of_pos hm0) (mul_pos hm0 (by linarith))).mpr
    nlinarith
  · apply (one_div_lt_one_div (mul_pos hm0 (by linarith)) (by positivity)).mpr
    nlinarith

/-- The main construction's leading coordinate is above the uniform coordinate
through the cubic-dimensional boundary. -/
private theorem main_alpha_ge_uniform {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (hnm : n ≤ m ^ 3) :
    1 / ((m : ℝ) ^ 2) ≤ 1 / Real.sqrt ((m : ℝ) * n) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (n : ℝ) ≤ (m : ℝ)^3 := by exact_mod_cast hnm
  have hs0 : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr (mul_pos hm0 hn0)
  have hs := Real.sq_sqrt (mul_pos hm0 hn0).le
  apply one_div_le_one_div_of_le hs0
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · calc
      (m : ℝ) * n ≤ (m : ℝ) * (m : ℝ)^3 := mul_le_mul_of_nonneg_left hn' hm0.le
      _ = ((m : ℝ)^2)^2 := by ring

/-- Strict scalar gap for the main LPS prescribed spectrum. -/
theorem main_profile_gap {m n ℓ : ℕ} (hm : 2 ≤ m) (hmn : m < n)
    (hnm : n ≤ m ^ 3) (hℓ : 2 ≤ ℓ) (hℓk : ℓ ≤ m ^ 2) :
    schurProfile (m ^ 2) ℓ (separableThreshold m n) <
      schurProfile (m ^ 2) ℓ (1 / Real.sqrt ((m : ℝ) * n)) := by
  have hn : 2 ≤ n := hm.trans (Nat.le_of_lt hmn)
  have hαδ := separableThreshold_gt_alpha hm hmn
  have hδ1 := separableThreshold_lt_one hm hn
  have hαu := main_alpha_ge_uniform hm (by omega) hnm
  have hu : 1 / ((m : ℝ)^2) < separableThreshold m n := separableThreshold_gt_uniform hm hn
  have hk : 2 ≤ m ^ 2 := by nlinarith
  apply schurProfile_strictAntiOn hk hℓ hℓk
  · exact ⟨by exact_mod_cast hαu, le_of_lt (hαδ.trans hδ1)⟩
  · exact ⟨by exact_mod_cast hu.le, hδ1.le⟩
  · exact hαδ

/-- Strict scalar gap for the uniform realignment spectrum. -/
theorem uniform_profile_gap {m n ℓ : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hℓ : 2 ≤ ℓ) (hℓk : ℓ ≤ m ^ 2) :
    schurProfile (m ^ 2) ℓ (separableThreshold m n) <
      schurProfile (m ^ 2) ℓ (1 / ((m : ℝ)^2)) := by
  have hu := separableThreshold_gt_uniform hm hn
  have hδ1 := separableThreshold_lt_one hm hn
  have hk : 2 ≤ m ^ 2 := by nlinarith
  apply schurProfile_strictAntiOn hk hℓ hℓk
  · exact ⟨by norm_cast, le_of_lt (hu.trans hδ1)⟩
  · exact ⟨by exact_mod_cast hu.le, hδ1.le⟩
  · exact hu

private theorem exceptional_alpha_two_lt_threshold {n : ℕ} (hn : 2 ≤ n) :
    1 / ((2 : ℝ) * Real.sqrt ((2 : ℝ)^2 - 1)) < separableThreshold 2 n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by positivity
  have hinv : 0 < 1 / (n : ℝ) := by positivity
  have hinv1 : 1 / (n : ℝ) < 1 := (div_lt_one hn0).mpr hn1
  have hc := Real.sq_sqrt (show 0 ≤ (1 - 1 / (2 : ℝ)) * (1 - 1 / (n : ℝ)) by positivity)
  have hc0 := Real.sqrt_nonneg ((1 - 1 / (2 : ℝ)) * (1 - 1 / (n : ℝ)))
  have hcBound : Real.sqrt ((1 - 1 / (2 : ℝ)) * (1 - 1 / (n : ℝ))) < 17 / 24 := by
    apply (sq_lt_sq₀ hc0 (by norm_num : (0 : ℝ) ≤ 17 / 24)).mp
    rw [hc]
    nlinarith only [hinv]
  have hs : Real.sqrt ((2 : ℝ)^2 - 1) ^ 2 = 3 := by norm_num
  have hs0 := Real.sqrt_nonneg ((2 : ℝ)^2 - 1)
  have hsBound : 12 / 7 < Real.sqrt ((2 : ℝ)^2 - 1) := by
    apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 12 / 7) hs0).mp
    rw [hs]
    norm_num
  have hα : 1 / ((2 : ℝ) * Real.sqrt ((2 : ℝ)^2 - 1)) < 7 / 24 := by
    apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * Real.sqrt ((2 : ℝ)^2 - 1))).mpr
    nlinarith
  change 1 / ((2 : ℝ) * Real.sqrt ((2 : ℝ)^2 - 1)) <
    1 - Real.sqrt ((1 - 1 / (2 : ℝ)) * (1 - 1 / (n : ℝ)))
  linarith only [hα, hcBound]

/-- Strict scalar gap for the supported exceptional-band spectrum. -/
theorem exceptional_profile_gap {m n ℓ : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hℓ : 2 ≤ ℓ) (hℓk : ℓ ≤ m ^ 2) :
    schurProfile (m ^ 2) ℓ (separableThreshold m n) <
      schurProfile (m ^ 2) ℓ (1 / ((m : ℝ) * Real.sqrt ((m : ℝ)^2 - 1))) := by
  have hm2 : 2 ≤ m := hm
  have hαδ : 1 / ((m : ℝ) * Real.sqrt ((m : ℝ)^2 - 1)) < separableThreshold m n := by
    by_cases hm3 : 3 ≤ m
    · exact (exceptional_alpha_bounds hm3).2.trans (separableThreshold_gt_half hm2 hn)
    · have hmEq : m = 2 := by omega
      subst m
      exact exceptional_alpha_two_lt_threshold hn
  have hαu : 1 / ((m : ℝ)^2) ≤ 1 / ((m : ℝ) * Real.sqrt ((m : ℝ)^2 - 1)) := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hs := Real.sq_sqrt (show 0 ≤ (m : ℝ)^2 - 1 by nlinarith)
    have hs0 := Real.sqrt_nonneg ((m : ℝ)^2 - 1)
    have hspos : 0 < Real.sqrt ((m : ℝ)^2 - 1) := by nlinarith
    apply one_div_le_one_div_of_le (mul_pos hm0 hspos)
    nlinarith
  have hδ1 := separableThreshold_lt_one hm2 hn
  have hu := separableThreshold_gt_uniform hm2 hn
  have hk : 2 ≤ m ^ 2 := by nlinarith
  apply schurProfile_strictAntiOn hk hℓ hℓk
  · exact ⟨by exact_mod_cast hαu, le_of_lt (hαδ.trans hδ1)⟩
  · exact ⟨by exact_mod_cast hu.le, hδ1.le⟩
  · exact hαδ


private lemma esymmVec_pos {N j : ℕ} {x : Fin N → ℝ}
    (hx : ∀ i, 0 < x i) (hj : j ≤ N) : 0 < esymmVec j x := by
  classical
  rw [esymmVec_eq_sum]
  apply Finset.sum_pos
  · intro t ht
    exact Finset.prod_pos fun i hi => hx i
  · exact Finset.powersetCard_nonempty.mpr (by simpa using hj)

private lemma esymmVec_one {N : ℕ} (x : Fin N → ℝ) :
    esymmVec 1 x = ∑ i, x i := by
  simp [esymmVec, Multiset.esymm, Multiset.powersetCard_one, Function.comp_def, List.sum_ofFn]

private lemma esymmVec_zero {N : ℕ} (x : Fin N → ℝ) :
    esymmVec 0 x = 1 := by simp [esymmVec]

/-- Newton's inequality bounds every adjacent coefficient ratio by the first one. -/
private lemma esymmVec_ratio {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    (hx : ∀ i, 0 < x i) (j : ℕ) (hj : j + 1 ≤ N) :
    (j + 1 : ℝ) * esymmVec (j + 1) x ≤
      ((N : ℝ) - j) * ((∑ i, x i) / N) * esymmVec j x := by
  induction j with
  | zero =>
    rw [esymmVec_one, esymmVec_zero]
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    simp only [Nat.cast_zero, zero_add, one_mul, sub_zero, mul_one]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hNr]
  | succ j ih =>
    have hprev := ih (by omega)
    have hn : (j + 2 : ℝ) * ((N : ℝ) - j) *
        (esymmVec j x * esymmVec (j + 2) x) ≤
          (j + 1 : ℝ) * ((N : ℝ) - j - 1) * (esymmVec (j + 1) x)^2 := by
      simpa only [Multiset.card_map, Finset.card_val, Finset.card_univ,
        Fintype.card_fin, esymmVec] using
        D5.S3.Analytic.RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm
          ((Finset.univ : Finset (Fin N)).val.map x) j
    have hNj : (0 : ℝ) < N - j := by
      have : (j : ℝ) < N := by exact_mod_cast (show j < N by omega)
      linarith
    have hNj' : (0 : ℝ) ≤ N - j - 1 := by
      have : (j + 2 : ℝ) ≤ N := by exact_mod_cast hj
      linarith
    have he : 0 < esymmVec j x := esymmVec_pos hx (by omega)
    have hep : 0 ≤ esymmVec (j + 1) x := (esymmVec_pos hx (by omega)).le
    have hmul := mul_le_mul_of_nonneg_right hprev
      (mul_nonneg hNj' hep)
    have hfactor : 0 < ((N : ℝ) - j) * esymmVec j x := mul_pos hNj he
    apply (mul_le_mul_iff_right₀ hfactor).mp
    have hstep :
        (((N : ℝ) - j) * esymmVec j x) * ((j + 2 : ℝ) * esymmVec (j + 2) x) ≤
          (((N : ℝ) - j) * esymmVec j x) *
            (((N : ℝ) - j - 1) * ((∑ i, x i) / N) * esymmVec (j + 1) x) := by
      nlinarith only [hn, hmul]
    convert hstep using 1 <;> push_cast <;> ring

/-- Maclaurin's sharp upper bound, first for strictly positive coordinates. -/
private theorem esymmVec_le_mean_pos {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    (hx : ∀ i, 0 < x i) (j : ℕ) :
    esymmVec j x ≤ (N.choose j : ℝ) * ((∑ i, x i) / N)^j := by
  classical
  by_cases hj : j ≤ N
  · induction j with
    | zero => simp [esymmVec]
    | succ j ih =>
      have hjN : j ≤ N := by omega
      have hi := ih hjN
      have hr := esymmVec_ratio hN x hx j hj
      have hM : 0 ≤ (∑ i, x i) / (N : ℝ) :=
        div_nonneg (Finset.sum_nonneg (fun i _ => (hx i).le)) (Nat.cast_nonneg N)
      have hNj : 0 ≤ (N : ℝ) - j := by
        have : (j : ℝ) ≤ N := by exact_mod_cast hjN
        linarith
      have hchoose : ((N.choose (j + 1) : ℕ) : ℝ) * (j + 1 : ℝ) =
          (N.choose j : ℝ) * ((N : ℝ) - j) := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hjN] using
          congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_succ_right_eq N j)
      apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < j + 1 by positivity)).mp
      calc
        (j + 1 : ℝ) * esymmVec (j + 1) x ≤
            ((N : ℝ) - j) * ((∑ i, x i) / N) * esymmVec j x := hr
        _ ≤ ((N : ℝ) - j) * ((∑ i, x i) / N) *
            ((N.choose j : ℝ) * ((∑ i, x i) / N)^j) :=
          mul_le_mul_of_nonneg_left hi (mul_nonneg hNj hM)
        _ = (j + 1 : ℝ) * ((N.choose (j + 1) : ℝ) * ((∑ i, x i) / N)^(j+1)) := by
          rw [pow_succ]
          nlinarith only [congrArg (fun z : ℝ => z * ((∑ i, x i) / N)^j * ((∑ i, x i) / N)) hchoose]
  · have he : esymmVec j x = 0 := by
      apply Multiset.esymm_of_card_lt
      simpa using (show N < j by omega)
    rw [he, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The elementary symmetric function is a continuous polynomial of its coordinates. -/
private lemma continuous_esymmVec {N : ℕ} (j : ℕ) :
    Continuous (fun x : Fin N → ℝ => esymmVec j x) := by
  classical
  simp_rw [esymmVec_eq_sum]
  fun_prop

/-- Maclaurin's sharp bound for nonnegative finite real vectors. -/
private theorem esymmVec_le_mean {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (j : ℕ) :
    esymmVec j x ≤ (N.choose j : ℝ) * ((∑ i, x i) / N)^j := by
  have he : ∀ ε > (0 : ℝ),
      esymmVec j (fun i => x i + ε) ≤
        (N.choose j : ℝ) * ((∑ i, (x i + ε)) / N)^j := by
    intro ε hε
    exact esymmVec_le_mean_pos hN _ (fun i => by linarith [hx i]) j
  have hc : Continuous (fun ε : ℝ =>
      (N.choose j : ℝ) * ((∑ i, (x i + ε)) / N)^j -
        esymmVec j (fun i => x i + ε)) := by
    apply Continuous.sub
    · fun_prop
    · exact (continuous_esymmVec j).comp (by fun_prop)
  have hh : 0 ≤ (N.choose j : ℝ) * ((∑ i, (x i + 0)) / N)^j -
      esymmVec j (fun i => x i + 0) := by
    apply ge_of_tendsto (f := fun ε : ℝ =>
      (N.choose j : ℝ) * ((∑ i, (x i + ε)) / N)^j -
        esymmVec j (fun i => x i + ε))
      (hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact sub_nonneg.mpr (he ε hε)
  simpa using sub_nonneg.mp hh

private lemma esymmVec_split {N j : ℕ} (x : Fin (N+1) → ℝ) :
    esymmVec (j+1) x = esymmVec (j+1) (fun i => x i.succ) +
      x 0 * esymmVec j (fun i => x i.succ) := by
  classical
  have hc (a : ℝ) (s : Multiset ℝ) (j : ℕ) :
      (a ::ₘ s).esymm (j+1) = s.esymm (j+1) + a * s.esymm j := by
    simp [Multiset.esymm, Multiset.sum_map_mul_left]
  simp only [esymmVec, Fin.univ_succ, Finset.cons_val, Finset.map_val,
    Multiset.map_cons, Multiset.map_map, Function.comp_def]
  exact hc _ _ _

/-- The exact elementary-symmetric value of a distinguished coordinate and a constant tail. -/
private theorem esymmVec_cons_const (N j : ℕ) (a b : ℝ) :
    esymmVec (j+1) (Fin.cons a (fun _ : Fin N => b)) =
      (N.choose (j+1) : ℝ) * b^(j+1) + (N.choose j : ℝ) * a * b^j := by
  rw [esymmVec_split]
  simp only [Fin.cons_succ, Fin.cons_zero]
  rw [show esymmVec (j+1) (fun _ : Fin N => b) =
        (N.choose (j+1) : ℝ) * b^(j+1) from
      D5.S3.Analytic.HypergeometricShiftTuran.Defs.esymm_const N (j+1) b,
    show esymmVec j (fun _ : Fin N => b) = (N.choose j : ℝ) * b^j from
      D5.S3.Analytic.HypergeometricShiftTuran.Defs.esymm_const N j b]
  ring

/-- The same profile formula on a multiset, ready for an unordered singular spectrum. -/
theorem esymm_cons_replicate (N j : ℕ) (a b : ℝ) :
    (a ::ₘ Multiset.replicate N b).esymm (j+1) =
      (N.choose (j+1) : ℝ) * b^(j+1) + (N.choose j : ℝ) * a * b^j := by
  simpa only [esymmVec, Fin.univ_succ, Finset.cons_val, Finset.map_val,
    Multiset.map_cons, Multiset.map_map, Function.comp_def, Fin.cons_zero,
    Fin.cons_succ, Function.Embedding.coeFn_mk, Multiset.map_const', Finset.card_val, Finset.card_univ,
    Fintype.card_fin] using esymmVec_cons_const N j a b

/-- At fixed total mass and first coordinate, the equal tail gives the sharp bound. -/
private theorem esymmVec_le_equal_tail {N j : ℕ} (hN : 0 < N)
    (x : Fin (N+1) → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) :
    esymmVec (j+1) x ≤
      (N.choose (j+1) : ℝ) * ((1-x 0)/N)^(j+1) +
        (N.choose j : ℝ) * x 0 * ((1-x 0)/N)^j := by
  have ht : (∑ i : Fin N, x i.succ) = 1-x 0 := by
    rw [Fin.sum_univ_succ] at hs
    linarith
  rw [esymmVec_split]
  have ha := esymmVec_le_mean hN (fun i : Fin N => x i.succ)
    (fun i => hx _) (j+1)
  have hb := mul_le_mul_of_nonneg_left
    (esymmVec_le_mean hN (fun i : Fin N => x i.succ) (fun i => hx _) j) (hx 0)
  rw [ht] at ha hb
  nlinarith only [ha, hb]

/-- A total-mass bound and a tail budget imply the sharp one-heavy-coordinate bound.
The input need not be ordered: only the distinguished coordinate is used. -/
private theorem esymmVec_le_schurProfile {N ℓ : ℕ} (hN : 0 < N)
    (hℓ : 2 ≤ ℓ) (hℓN : ℓ ≤ N+1) (s : Fin (N+1) → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∑ i, s i ≤ 1)
    (δ : ℝ) (hδ : 1 / (N+1 : ℝ) ≤ δ) (hδ1 : δ ≤ 1)
    (htail : (∑ i : Fin N, s i.succ) ≤ 1-δ) :
    esymmVec ℓ s ≤ schurProfile (N+1) ℓ δ := by
  classical
  let a : ℝ := 1 - ∑ i : Fin N, s i.succ
  have hsa : s 0 ≤ a := by
    rw [Fin.sum_univ_succ] at hs
    dsimp [a]
    linarith
  have ha0 : 0 ≤ a := (hs0 0).trans hsa
  have ha1 : a ≤ 1 := by
    have ht0 : 0 ≤ ∑ i : Fin N, s i.succ := Finset.sum_nonneg (fun i _ => hs0 _)
    dsimp [a]
    linarith
  have hδa : δ ≤ a := by dsimp [a]; linarith
  let x : Fin (N+1) → ℝ := Fin.cons a (fun i => s i.succ)
  have hx0 : ∀ i, 0 ≤ x i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha0
    · exact hs0 j.succ
  have hsx : ∑ i, x i = 1 := by
    simp only [Fin.sum_univ_succ, x, Fin.cons_zero, Fin.cons_succ]
    dsimp [a]
    ring
  have hs_le : ∀ i, s i ≤ x i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hsa
    · exact le_rfl
  have hbound := esymmVec_le_equal_tail (j := ℓ-1) hN x hx0 hsx
  have hℓeq : ℓ - 1 + 1 = ℓ := by omega
  rw [hℓeq] at hbound
  have hprofile : esymmVec ℓ x ≤ schurProfile (N+1) ℓ a := by
    simpa only [schurProfile, tailMean, Nat.add_sub_cancel, x, Fin.cons_zero] using hbound
  exact (esymmVec_mono hs0 hs_le).trans (hprofile.trans
    ((schurProfile_strictAntiOn (by omega) hℓ hℓN).antitoneOn
      ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hδ, hδ1⟩
      ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hδ.trans hδa, ha1⟩ hδa))

/-- The sharp tail-budget bound with the original finite dimension retained. -/
theorem esymmVec_le_schurProfile_fin {k ℓ : ℕ} (hk : 2 ≤ k)
    (hℓ : 2 ≤ ℓ) (hℓk : ℓ ≤ k) (s : Fin k → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∑ i, s i ≤ 1)
    (δ : ℝ) (hδ : 1 / (k : ℝ) ≤ δ) (hδ1 : δ ≤ 1)
    (htail : (∑ i ∈ Finset.univ.filter (fun i : Fin k => 0 < i.val), s i) ≤ 1-δ) :
    esymmVec ℓ s ≤ schurProfile k ℓ δ := by
  cases k with
  | zero => omega
  | succ N =>
    have he : (∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => 0 < i.val), s i) =
        ∑ i : Fin N, s i.succ := by
      rw [Finset.sum_filter, Fin.sum_univ_succ]
      simp
    apply esymmVec_le_schurProfile (by omega) hℓ hℓk s hs0 hs δ
      (by simpa only [Nat.cast_add, Nat.cast_one] using hδ) hδ1
    simpa only [he] using htail

private lemma rowGram_toEuclideanLin {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) :
    (A * Aᴴ).toEuclideanLin =
      Aᴴ.toEuclideanLin.adjoint.comp Aᴴ.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_conjTranspose]
  ext x i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
private lemma symmetric_eigenvalues_congr {ι : Type*} [Fintype ι]
    (T S : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (he : T = S)
    (i : Fin (Fintype.card ι)) :
    hT.eigenvalues finrank_euclideanSpace i =
      hS.eigenvalues finrank_euclideanSpace i := by
  subst S
  rfl
theorem singularVector_eq_sqrt_rowGram {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) (i : Fin (Fintype.card ι)) :
    singularVector A i =
      Real.sqrt (A.posSemidef_self_mul_conjTranspose.isHermitian.eigenvalues₀ i) := by
  rw [singularVector, LinearMap.singularValues_fin _ finrank_euclideanSpace]
  congr 1
  exact symmetric_eigenvalues_congr _ _ _ _ (rowGram_toEuclideanLin A).symm i

open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open scoped Kronecker MatrixOrder ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormCovariance
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral

private theorem hermitianMat_finrank (n : ℕ) :
    Module.finrank ℝ (HermitianMat (Fin n) ℂ) = n ^ 2 := by
  let e : HermitianMat (Fin n) ℂ ≃ₗ[ℝ]
      D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace n :=
    { toFun := fun A => ⟨A.mat, A.property⟩
      invFun := fun A => ⟨A.val, A.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq.trans
    (D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition.hermitian_space_finrank n)

/-- Complete trace-product normalized Hermitian coordinates exist in every
finite dimension, including the empty dimension. -/
private theorem exists_hermitian_basis (n : ℕ) :
    ∃ a : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, IsHermBasis a := by
  classical
  let b := (stdOrthonormalBasis ℝ (HermitianMat (Fin n) ℂ)).reindex
    (finCongr (hermitianMat_finrank n))
  refine ⟨fun i => (b i).mat, (fun i => (b i).property), rfl, ?_⟩
  intro i j
  rw [← HermitianMat.inner_eq_trace_mul (R := ℝ), b.inner_eq_ite]
  split_ifs <;> simp

/-- Columns are the actual flattened local Hermitian matrices. -/
private def basisMatrix {n : ℕ}
    (a : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin (n ^ 2)) ℂ :=
  fun ij k => a k ij.1 ij.2

/-- Trace-product orthonormality is complex Hilbert--Schmidt orthonormality. -/
private theorem basisMatrix_gram {n : ℕ}
    (a : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a) :
    (basisMatrix a)ᴴ * basisMatrix a = 1 := by
  classical
  ext i j
  calc
    _ = ((a i)ᴴ * a j).trace := by
      simp only [basisMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.trace, Matrix.diag]
      rw [Finset.sum_comm]
    _ = _ := by rw [(ha.1 i).eq, ha.2.2]; rfl

/-- Flattened density matrices are reconstructed by the local coordinate map. -/
private theorem basisMatrix_coordinates {n : ℕ}
    (a : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (ij : Fin n × Fin n) :
    ∑ k, basisMatrix a ij k * ((coordinates a A k : ℝ) : ℂ) = A ij.1 ij.2 := by
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M ij.1 ij.2)
    (coordinate_reconstruction a ha A hA)
  simpa only [basisMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm] using he.symm

/-- A product-density realignment is the complex image of its real rank-one
correlation matrix, with the transpose on Bob's side. -/
private theorem realign_product_coordinates {m n : ℕ}
    (a : Fin (m ^ 2) → Matrix (Fin m) (Fin m) ℂ) (ha : IsHermBasis a)
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b)
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.IsHermitian)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) :
    realign (A ⊗ₖ B) =
      basisMatrix a * (corr (A ⊗ₖ B) a b).map Complex.ofReal * (basisMatrix b)ᵀ := by
  classical
  ext ij ab
  simp only [realign, Matrix.kroneckerMap_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply,
    corr_product_entry A B a b hA hB ha.1 hb.1, Complex.ofReal_mul]
  symm
  calc
    _ = (∑ k, basisMatrix a ij k * ((coordinates a A k : ℝ) : ℂ)) *
        (∑ l, basisMatrix b ab l * ((coordinates b B l : ℝ) : ℂ)) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [basisMatrix_coordinates a ha A hA,
      basisMatrix_coordinates b hb B hB]

/-- The exact matrix bridge from the actual finite separable decomposition;
no spectral correspondence is assumed. -/
private theorem realign_separable_coordinates {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (m ^ 2) → Matrix (Fin m) (Fin m) ℂ) (ha : IsHermBasis a)
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b) :
    realign ρ = basisMatrix a * (corr ρ a b).map Complex.ofReal * (basisMatrix b)ᵀ := by
  classical
  obtain ⟨v, w, A, B, hw, hs, hab, heq⟩ := hρ
  rw [heq]
  have hre : realign (∑ k, (w k : ℂ) • (A k ⊗ₖ B k)) =
      ∑ k, (w k : ℂ) • realign (A k ⊗ₖ B k) := by
    ext ij ab
    simp only [realign, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hc : (corr (∑ k, (w k : ℂ) • (A k ⊗ₖ B k)) a b).map Complex.ofReal =
      ∑ k, (w k : ℂ) • (corr (A k ⊗ₖ B k) a b).map Complex.ofReal := by
    ext i j
    simp [corr, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      Complex.re_sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  rw [hre, hc, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_smul, Matrix.smul_mul,
    realign_product_coordinates a ha b hb (A k) (hab k).1.1.isHermitian
      (B k) (hab k).2.1.isHermitian]

private lemma coordinates_density_norm_le {n : ℕ}
    (a : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsDensity A) :
    ‖coordinates a A‖ ≤ 1 := by
  have he := coordinates_purity a ha A hA.1.isHermitian
  have hp := (density_purity_bounds A hA).2
  nlinarith [norm_nonneg (coordinates a A)]

/-- CCNR on the actual complete local Hermitian correlation matrix. -/
private theorem separable_correlation_ccnr {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (m ^ 2) → Matrix (Fin m) (Fin m) ℂ) (ha : IsHermBasis a)
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b) :
    traceNorm (corr ρ a b) ≤ 1 := by
  classical
  obtain ⟨v, w, A, B, hw, hs, hab, heq⟩ := hρ
  have hc := correlation_finite_decomposition w A B a b
    (fun k => (hab k).1.1.isHermitian) (fun k => (hab k).2.1.isHermitian) ha.1 hb.1
  rw [heq, hc]
  change traceNorm (weightedOuter (fun k => coordinates a (A k))
    (fun k => coordinates b (B k)) w) ≤ 1
  calc
    _ ≤ ∑ k, w k * ‖coordinates a (A k)‖ * ‖coordinates b (B k)‖ :=
      traceNorm_weightedOuter_le _ _ _ hw
    _ ≤ ∑ k, w k * 1 * 1 := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (coordinates_density_norm_le a ha _ (hab k).1) (hw k))
        (coordinates_density_norm_le b hb _ (hab k).2)
        (norm_nonneg _) (by simpa using hw k)
    _ = 1 := by simpa using hs

/-- The transpose in the realignment convention cancels Bob's local basis. -/
private theorem basisMatrix_transpose_cogram {n : ℕ}
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b) :
    (basisMatrix b)ᵀ * ((basisMatrix b)ᵀ)ᴴ = 1 := by
  have h := congrArg Matrix.transpose (basisMatrix_gram b hb)
  simpa only [Matrix.transpose_mul, Matrix.transpose_one,
    Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose] using h

/-- The actual row Gram is a unitary transport of the complex correlation Gram. -/
private theorem realign_separable_rowGram {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (m ^ 2) → Matrix (Fin m) (Fin m) ℂ) (ha : IsHermBasis a)
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b) :
    realign ρ * (realign ρ)ᴴ = basisMatrix a *
      ((corr ρ a b).map Complex.ofReal * ((corr ρ a b).map Complex.ofReal)ᴴ) *
        (basisMatrix a)ᴴ := by
  rw [realign_separable_coordinates ρ hρ a ha b hb]
  simp only [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisMatrix b)ᵀ, basisMatrix_transpose_cogram b hb,
    Matrix.one_mul]

/-- Local Hilbert--Schmidt isometries preserve the complete characteristic
polynomial, including zero eigenvalues. -/
private theorem basisMatrix_gram_charpoly {n : ℕ}
    (a : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a)
    (G : Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℂ) :
    (basisMatrix a * G * (basisMatrix a)ᴴ).charpoly = G.charpoly := by
  have h := Matrix.charpoly_mul_comm_of_le (basisMatrix a)
    (G * (basisMatrix a)ᴴ) (by simp [pow_two])
  simpa only [Matrix.mul_assoc, basisMatrix_gram a ha, Matrix.mul_one,
    Fintype.card_prod, Fintype.card_fin, ← pow_two, Nat.sub_self,
    pow_zero, one_mul] using h

/-- Characteristic-polynomial version of the complex realignment bridge. -/
private theorem realign_separable_rowGram_charpoly {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (m ^ 2) → Matrix (Fin m) (Fin m) ℂ) (ha : IsHermBasis a)
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b) :
    (realign ρ * (realign ρ)ᴴ).charpoly =
      ((corr ρ a b).map Complex.ofReal * ((corr ρ a b).map Complex.ofReal)ᴴ).charpoly := by
  rw [realign_separable_rowGram ρ hρ a ha b hb, basisMatrix_gram_charpoly a ha]

/-- Both scalar constraints on the smaller-side real singular vector. The
transpose identity transports the published covariance tail without assuming
an equality of separately chosen eigenvector bases. -/
private theorem separable_correlation_row_constraints {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (m ^ 2) → Matrix (Fin m) (Fin m) ℂ) (ha : IsHermBasis a)
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b) :
    (∑ i : Fin (m ^ 2), (corr ρ a b)ᵀ.toEuclideanLin.singularValues i) ≤ 1 ∧
      (∑ i ∈ Finset.Ico 1 (m ^ 2), (corr ρ a b)ᵀ.toEuclideanLin.singularValues i) ≤
        Real.sqrt ((((m : ℝ) - 1) / m) * (((n : ℝ) - 1) / n)) := by
  constructor
  · rw [← traceNorm_eq_native_sum, traceNorm_transpose]
    exact separable_correlation_ccnr ρ hρ a ha b hb
  · let C := corr ρ a b
    have hm2 : 0 < m ^ 2 := pow_pos hm 2
    have hn2 : 0 < n ^ 2 := pow_pos hn 2
    have hmn2 : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hmn 2
    have hc := (correlation_tail_corrected hm hn ρ hρ a ha b hb).1.trans
      (correlation_tail_corrected hm hn ρ hρ a ha b hb).2
    simp only [min_eq_left hmn, max_eq_right hmn] at hc
    have ht := native_tail_eq_traceNorm_sub C hm2 hn2
    have htt := native_tail_eq_traceNorm_sub Cᵀ hn2 hm2
    rw [min_eq_left hmn2] at ht
    rw [min_eq_right hmn2, traceNorm_transpose] at htt
    have hnorm : ‖Cᵀ‖ = ‖C‖ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.l2_opNorm_conjTranspose C
    rw [hnorm, ← ht] at htt
    change (∑ i ∈ Finset.Ico 1 (m ^ 2), Cᵀ.toEuclideanLin.singularValues i) ≤ _
    rw [htt]
    exact hc

private lemma eigenvalues₀_of_charpoly_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (B : Matrix κ κ ℝ) (hB : B.IsHermitian)
    (hcard : Fintype.card ι = Fintype.card κ)
    (hchar : A.charpoly = B.charpoly.map Complex.ofRealHom)
    (i : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ i = hB.eigenvalues₀ (Fin.cast hcard i) := by
  have hlist : List.ofFn hA.eigenvalues₀ = List.ofFn hB.eigenvalues₀ := by
    rw [← hA.sort_roots_charpoly_eq_eigenvalues₀,
      ← hB.sort_roots_charpoly_eq_eigenvalues₀, hchar,
      hB.splits_charpoly.roots_map Complex.ofRealHom]
    simp
  have he := congrArg (fun l : List ℝ => l[i.val]?) hlist
  have hi : i.val < Fintype.card κ := by simpa only [← hcard] using i.isLt
  have he' : hA.eigenvalues₀ i = hB.eigenvalues₀ ⟨i.val, hi⟩ := by
    simpa [List.getElem?_ofFn, i.isLt, hi] using he
  exact he'.trans (congrArg hB.eigenvalues₀ (Fin.ext (by simp)))

/-- Realification of the real row Gram commutes with the complex adjoint. -/
private theorem correlation_complex_rowGram {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℝ) :
    C.map Complex.ofReal * (C.map Complex.ofReal)ᴴ =
      (C * Cᵀ).map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum]

/-- The actual complex realignment and the real correlation transpose have
identical descending singular vectors, with the canonical dimension cast. -/
private theorem realign_separable_singularVector {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (m ^ 2) → Matrix (Fin m) (Fin m) ℂ) (ha : IsHermBasis a)
    (b : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (hb : IsHermBasis b)
    (i : Fin (Fintype.card (Fin m × Fin m))) :
    singularVector (realign ρ) i = (corr ρ a b)ᵀ.toEuclideanLin.singularValues
      (Fin.cast (show Fintype.card (Fin m × Fin m) = m ^ 2 by simp [pow_two]) i) := by
  let C := corr ρ a b
  have hG : (C * Cᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      C.posSemidef_self_mul_conjTranspose.isHermitian
  have hc : (realign ρ * (realign ρ)ᴴ).charpoly =
      (C * Cᵀ).charpoly.map Complex.ofRealHom := by
    rw [realign_separable_rowGram_charpoly ρ hρ a ha b hb,
      correlation_complex_rowGram]
    exact Matrix.charpoly_map (C * Cᵀ) Complex.ofRealHom
  rw [singularVector_eq_sqrt_rowGram]
  have hn := CorrelationMinorNormSpectral.native_singular_value Cᵀ
    (Fin.cast (show Fintype.card (Fin m × Fin m) = Fintype.card (Fin (m ^ 2)) by
      simp [pow_two]) i)
  change Real.sqrt _ = Cᵀ.toEuclideanLin.singularValues _
  simp only [Fin.val_cast] at hn ⊢
  rw [hn]
  congr 1
  exact eigenvalues₀_of_charpoly_map _
    (realign ρ).posSemidef_self_mul_conjTranspose.isHermitian _ hG
    (by simp [pow_two]) hc i

/-- CCNR and the dimension-only covariance tail for the actual complex
realignment. No local bases occur among the hypotheses. -/
private theorem separable_realignment_constraints {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ) :
    (∑ i, singularVector (realign ρ) i) ≤ 1 ∧
      (∑ i ∈ Finset.Ico 1 (m ^ 2), (realign ρ)ᴴ.toEuclideanLin.singularValues i) ≤
        Real.sqrt ((((m : ℝ) - 1) / m) * (((n : ℝ) - 1) / n)) := by
  classical
  obtain ⟨a, ha⟩ := exists_hermitian_basis m
  obtain ⟨b, hb⟩ := exists_hermitian_basis n
  have hc := separable_correlation_row_constraints hm hn hmn ρ hρ a ha b hb
  constructor
  · calc
      _ = ∑ i : Fin (m ^ 2), (corr ρ a b)ᵀ.toEuclideanLin.singularValues i := by
        apply Fintype.sum_equiv (finCongr (show Fintype.card (Fin m × Fin m) = m ^ 2 by
          simp [pow_two]))
        intro i
        exact realign_separable_singularVector ρ hρ a ha b hb i
      _ ≤ 1 := hc.1
  · have he : (∑ i ∈ Finset.Ico 1 (m ^ 2),
        (realign ρ)ᴴ.toEuclideanLin.singularValues i) =
        ∑ i ∈ Finset.Ico 1 (m ^ 2), (corr ρ a b)ᵀ.toEuclideanLin.singularValues i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hip : i < Fintype.card (Fin m × Fin m) := by
        simpa only [Fintype.card_prod, Fintype.card_fin, ← pow_two] using
          (Finset.mem_Ico.mp hi).2
      exact realign_separable_singularVector ρ hρ a ha b hb ⟨i, hip⟩
    rw [he]
    exact hc.2


theorem separable_esymm_bound {m n ℓ : ℕ} (hm : 2 ≤ m) (hmn : m < n)
    (hℓ : 2 ≤ ℓ) (hℓk : ℓ ≤ m ^ 2)
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hρ : IsSeparable ρ) :
    esymmSV ℓ (realign ρ) ≤ schurProfile (m ^ 2) ℓ (separableThreshold m n) := by
  classical
  let k := Fintype.card (Fin m × Fin m)
  let s := singularVector (realign ρ)
  have hk : k = m ^ 2 := by simp [k, pow_two]
  have hn : 2 ≤ n := by omega
  have hc := separable_realignment_constraints (by omega) (by omega) hmn.le ρ hρ
  have htail : (∑ i ∈ Finset.univ.filter (fun i : Fin k => 0 < i.val), s i) ≤
      1 - separableThreshold m n := by
    have he : (∑ i ∈ Finset.univ.filter (fun i : Fin k => 0 < i.val), s i) =
        ∑ i ∈ Finset.Ico 1 k, (realign ρ)ᴴ.toEuclideanLin.singularValues i := by
      rw [Finset.sum_filter]
      change (∑ i : Fin k, if 0 < i.val then
        (realign ρ)ᴴ.toEuclideanLin.singularValues i else 0) = _
      rw [← Finset.sum_range (fun j : ℕ => if 0 < j then
        (realign ρ)ᴴ.toEuclideanLin.singularValues j else 0), ← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [he, hk]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hem : ((m : ℝ) - 1) / m = 1 - 1 / m := by field_simp [hm0]
    have hen : ((n : ℝ) - 1) / n = 1 - 1 / n := by field_simp [hn0]
    calc
      _ ≤ Real.sqrt ((((m : ℝ) - 1) / m) * (((n : ℝ) - 1) / n)) := hc.2
      _ = 1 - separableThreshold m n := by rw [hem, hen, separableThreshold]; ring
  have hk2 : 2 ≤ k := by rw [hk]; nlinarith
  have hp := esymmVec_le_schurProfile_fin hk2 hℓ (by simpa only [hk] using hℓk) s
    (fun i => LinearMap.singularValues_nonneg (realign ρ)ᴴ.toEuclideanLin i) hc.1 (separableThreshold m n)
    (by simpa only [hk, Nat.cast_pow] using (separableThreshold_gt_uniform hm hn).le)
    (separableThreshold_lt_one hm hn).le htail
  change esymmVec ℓ s ≤ _
  simpa only [hk] using hp

end D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
