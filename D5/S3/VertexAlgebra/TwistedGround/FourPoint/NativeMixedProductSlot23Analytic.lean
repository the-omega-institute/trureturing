import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Coefficient
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateInversionGerm
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Absolute regrouping of the finite slot-(2,3) exchange law and its application
to the native B product on the punctured disk of radius one half. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic

open private hasSum_binomial from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateInversionGerm

private theorem choose_eq_product (z : ℂ) (k : ℕ) :
    Ring.choose z k = (∏ i ∈ Finset.range k, (z - (i : ℂ))) / (k.factorial : ℂ) := by
  have hprod : (descPochhammer ℤ k).smeval z = ∏ i ∈ Finset.range k, (z - (i : ℂ)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
      simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
        npow_one, npow_zero, nsmul_one]
  rw [Ring.choose_eq_smul, hprod, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem norm_choose_sub_nat_le (δ : ℂ) {c : ℕ} (hc : ‖δ‖ ≤ (c : ℝ))
    (F k : ℕ) :
    ‖Ring.choose (δ - (F : ℂ)) k‖ ≤ ((k + (F + c)).choose k : ℝ) := by
  rw [choose_eq_product, norm_div, norm_prod, Complex.norm_natCast,
    Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.prod_range_reflect (fun i : ℕ => ((k + (F + c) : ℕ) : ℝ) - i) k]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i hi => ?_
  have hik : i < k := Finset.mem_range.mp hi
  have hindex : (((k - 1 - i : ℕ) : ℝ)) + (i : ℝ) + 1 = k := by
    exact_mod_cast (show k - 1 - i + i + 1 = k by omega)
  calc
    ‖δ - (F : ℂ) - (i : ℂ)‖ ≤ ‖δ‖ + ‖(F : ℂ)‖ + ‖(i : ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ ((k + (F + c) : ℕ) : ℝ) - ((k - 1 - i : ℕ) : ℝ) := by
      simp only [Complex.norm_natCast, Nat.cast_add]
      linarith

private def binomialTerm (δ : ℂ) (b : ℕ → ℂ) (y : ℂ) (p : ℕ × ℕ) : ℂ :=
  b p.1 * (-y) ^ p.1 * (Ring.choose (δ - (p.1 : ℂ)) p.2 * (-y) ^ p.2)

/-- The coupled binomial family is absolutely summable under a single radial
bound on the exchanged energy series. -/
private theorem summable_norm_binomialTerm (δ : ℂ) (b : ℕ → ℂ) (y : ℂ)
    (hy : ‖y‖ < 1)
    (hb : Summable (fun F : ℕ => ‖b F‖ * (‖y‖ / (1 - ‖y‖)) ^ F)) :
    Summable (fun p : ℕ × ℕ => ‖binomialTerm δ b y p‖) := by
  obtain ⟨c, hc⟩ := exists_nat_ge ‖δ‖
  let r := ‖y‖
  have hr₀ : 0 ≤ r := norm_nonneg _
  have hr₁ : 0 < 1 - r := sub_pos.mpr hy
  let majorant (p : ℕ × ℕ) : ℝ :=
    (‖b p.1‖ * r ^ p.1) * (((p.2 + (p.1 + c)).choose p.2 : ℝ) * r ^ p.2)
  have hrow (F : ℕ) :
      HasSum (fun k : ℕ => majorant (F, k))
        ((‖b F‖ * r ^ F) * (1 / (1 - r) ^ (F + c + 1))) :=
    by
      have h := (hasSum_choose_mul_geometric_of_norm_lt_one (F + c)
        (r := r) (by simpa [Real.norm_eq_abs, abs_of_nonneg hr₀, r] using hy)).mul_left
        (‖b F‖ * r ^ F)
      refine h.congr_fun fun k => ?_
      dsimp only [majorant]
      rw [Nat.choose_symm_add (a := k) (b := F + c)]
  have hm : Summable majorant := by
    refine (summable_prod_of_nonneg (f := majorant) (fun p => by
      dsimp only [majorant]
      positivity)).mpr ⟨fun F => (hrow F).summable, ?_⟩
    refine (hb.mul_right (1 / (1 - r) ^ (c + 1))).congr fun F => ?_
    rw [(hrow F).tsum_eq, show F + c + 1 = F + (c + 1) by omega,
      pow_add (1 - r) F (c + 1), div_pow]
    change ‖b F‖ * (r ^ F / (1 - r) ^ F) * (1 / (1 - r) ^ (c + 1)) = _
    field_simp [ne_of_gt hr₁]
  refine hm.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨F, k⟩
  simp only [binomialTerm, majorant, norm_mul, norm_pow, norm_neg]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (norm_choose_sub_nat_le δ hc F k) (pow_nonneg hr₀ _))
    (mul_nonneg (norm_nonneg _) (pow_nonneg hr₀ _))

private def binomialCoeff (δ : ℂ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
    b p.1 * (-1 : ℂ) ^ p.1 * (Ring.choose (δ - (p.1 : ℂ)) p.2 * (-1 : ℂ) ^ p.2)

/-- Sum the reflected coefficient as a principal power times the exchanged
series. Absolute summability precedes both the row and energy regroupings. -/
private theorem hasSum_binomialCoeff (δ : ℂ) (b : ℕ → ℂ) {y : ℂ}
    (hy : ‖y‖ < 1)
    (hb : Summable (fun F : ℕ => ‖b F‖ * (‖y‖ / (1 - ‖y‖)) ^ F)) :
    HasSum (fun n : ℕ => binomialCoeff δ b n * y ^ n)
      ((1 - y) ^ δ * ∑' F : ℕ, b F * (-y / (1 - y)) ^ F) := by
  classical
  let f := binomialTerm δ b y
  have hf : Summable f := (summable_norm_binomialTerm δ b y hy hb).of_norm
  have hone : 1 - y ≠ 0 := by
    intro hz
    have he : y = 1 := (sub_eq_zero.mp hz).symm
    simp [he] at hy
  have hrow (F : ℕ) :
      HasSum (fun k : ℕ => f (F, k))
        ((1 - y) ^ δ * (b F * (-y / (1 - y)) ^ F)) := by
    have hs := (hasSum_binomial (δ - (F : ℂ))
      (ρ := -y) (by simpa only [norm_neg] using hy)).mul_left (b F * (-y) ^ F)
    simp only [← sub_eq_add_neg] at hs
    rw [Complex.cpow_sub _ _ hone, Complex.cpow_natCast] at hs
    convert hs using 1
    · rfl
    · rw [div_pow]
      ring
  have hrows := hf.hasSum.prod_fiberwise hrow
  have hvalue : ((1 - y) ^ δ * ∑' F : ℕ, b F * (-y / (1 - y)) ^ F) = ∑' p, f p := by
    simpa only [tsum_mul_left] using hrows.tsum_eq
  have htotal : HasSum f ((1 - y) ^ δ * ∑' F : ℕ, b F * (-y / (1 - y)) ^ F) := by
    rw [hvalue]
    exact hf.hasSum
  have hsigma : HasSum (fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) => f (p.2 : ℕ × ℕ))
      ((1 - y) ^ δ * ∑' F : ℕ, b F * (-y / (1 - y)) ^ F) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr htotal
  apply hsigma.sigma
  intro n
  have hterms : binomialCoeff δ b n * y ^ n =
      ∑ p : ↥(Finset.HasAntidiagonal.antidiagonal n), f (p : ℕ × ℕ) := by
    calc
      _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p := by
        rw [binomialCoeff, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        have hn := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        dsimp only [f, binomialTerm]
        rw [← hn, pow_add, neg_eq_neg_one_mul y, mul_pow, mul_pow]
        ring
      _ = _ := (Finset.sum_coe_sort _ f).symm
  rw [hterms]
  exact hasSum_fintype _

private def shiftedCoeff (δ : ℂ) (b : ℕ → ℂ) (j n : ℕ) : ℂ :=
  if j ≤ n then binomialCoeff δ b (n - j) else 0

private theorem hasSum_shiftedCoeff (δ : ℂ) (b : ℕ → ℂ) (j : ℕ) {y : ℂ}
    (hy : ‖y‖ < 1)
    (hb : Summable (fun F : ℕ => ‖b F‖ * (‖y‖ / (1 - ‖y‖)) ^ F)) :
    HasSum (fun n : ℕ => shiftedCoeff δ b j n * y ^ n)
      (y ^ j * ((1 - y) ^ δ * ∑' F : ℕ, b F * (-y / (1 - y)) ^ F)) := by
  let shift (n : ℕ) := n + j
  have hinj : Function.Injective shift := by
    intro n m h
    dsimp only [shift] at h
    omega
  have hoff (n : ℕ) (hn : n ∉ Set.range shift) : shiftedCoeff δ b j n * y ^ n = 0 := by
    have hnj : ¬ j ≤ n := by
      intro h
      apply hn
      exact ⟨n - j, by dsimp only [shift]; omega⟩
    simp [shiftedCoeff, hnj]
  apply (hinj.hasSum_iff hoff).mp
  refine ((hasSum_binomialCoeff δ b hy hb).mul_left (y ^ j)).congr_fun fun n => ?_
  change shiftedCoeff δ b j (n + j) * y ^ (n + j) = _
  rw [shiftedCoeff, ite_eq_left (by omega), Nat.add_sub_cancel, pow_add]
  ring

open ActualLeechHyperbolic (leechData)
open Complex (I)
open LatticeHalfFockGradedTrace (actualGrade)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff)
open NativeMixedBProductInversion (b_joint_product_summable_of_homogeneous)
open NativeMixedProductSlot23Coefficient (bProductCoeff_slot23_exchange slot23_choose_reflection)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeMixedPairSkew (swapInput)
open private swapInput_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew

open private bEnergyTerm bEnergy_hasSum_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev energyPole (K L : ℕ) : ℤ := 6 + (K : ℤ) + L
private abbrev detectorExponent (M N j : ℕ) : ℂ :=
  ((N : ℂ) - M - 2 * (j : ℂ)) / 2

private theorem sum_slot23_indices (E J : ℕ) (g : ℕ → ℕ → ℕ → ℂ) :
    (∑ h ∈ Finset.range (E + 1), ∑ j ∈ Finset.range (min h J + 1),
      g j (E - h) (h - j)) =
    ∑ j ∈ Finset.range (J + 1), ∑ p ∈
      (if j ≤ E then Finset.HasAntidiagonal.antidiagonal (E - j) else ∅), g j p.1 p.2 := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  let S := (Finset.range (E + 1)).sigma (fun h => Finset.range (min h J + 1))
  let T := (Finset.range (J + 1)).sigma
    (fun j => if j ≤ E then Finset.HasAntidiagonal.antidiagonal (E - j) else ∅)
  let toTarget (p : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ × ℕ :=
    ⟨p.2, (E - p.1, p.1 - p.2)⟩
  let toSource (p : Σ _ : ℕ, ℕ × ℕ) : Σ _ : ℕ, ℕ :=
    ⟨p.1 + p.2.2, p.1⟩
  have source_mem (p : Σ _ : ℕ, ℕ) :
      p ∈ S ↔ p.1 ≤ E ∧ p.2 ≤ p.1 ∧ p.2 ≤ J := by
    simp [S, Finset.mem_sigma]
  have target_mem (p : Σ _ : ℕ, ℕ × ℕ) :
      p ∈ T ↔ p.1 ≤ J ∧ p.1 ≤ E ∧ p.2.1 + p.2.2 = E - p.1 := by
    by_cases hp : p.1 ≤ E <;>
      simp [T, Finset.mem_sigma, hp, Finset.HasAntidiagonal.mem_antidiagonal]
  change (∑ p ∈ S, g p.2 (E - p.1) (p.1 - p.2)) =
    ∑ p ∈ T, g p.1 p.2.1 p.2.2
  apply Finset.sum_nbij' toTarget toSource
  · intro p hp
    obtain ⟨hh, hjh, hjJ⟩ := (source_mem p).mp hp
    apply (target_mem _).mpr
    dsimp only [toTarget]
    omega
  · intro p hp
    obtain ⟨hjJ, hjE, hFk⟩ := (target_mem p).mp hp
    apply (source_mem _).mpr
    dsimp only [toSource]
    omega
  · rintro ⟨h, j⟩ hp
    obtain ⟨hh, hjh, _⟩ := (source_mem _).mp hp
    have hback : j + (h - j) = h := by simpa using Nat.add_sub_of_le hjh
    simp [toTarget, toSource, hback]
  · rintro ⟨j, F, k⟩ hp
    obtain ⟨_, hjE, hFk⟩ := (target_mem _).mp hp
    change j ≤ E at hjE
    change F + k = E - j at hFk
    have hF : E - (j + k) = F := by omega
    have hk : j + k - j = k := by omega
    simp [toTarget, toSource, hF, hk]
  · intro p _
    rfl

private theorem zpow_twice (x : ℂ) (n : ℕ) :
    x ^ (2 * (n : ℤ)) = (x ^ (2 : ℕ)) ^ n := by
  change x ^ (((2 : ℕ) : ℤ) * (n : ℤ)) = (x ^ (2 : ℕ)) ^ n
  rw [zpow_mul, zpow_natCast, zpow_natCast]

set_option maxHeartbeats 1200000 in
-- Expanding the native exchange law exposes grade-dependent finite sums.
private theorem bProductCoeff_eq_shiftedCoeff (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hS : S.val ∈ actualGrade ℒ leechUnit N) (E : ℕ) :
    bProductCoeff s t M K L N Q R P S E =
      ((-1 : ℂ) ^ (3 + K) * I ^ (-energyPole K L)) *
        ∑ j ∈ Finset.range (N / 2 + 1), (j.factorial : ℂ)⁻¹ *
          shiftedCoeff (detectorExponent M N j)
            (bProductCoeff (!s) t M L K (N - 2 * j) R (swapInput Q) P ((L₁ (!t) ^ j) S))
            j E := by
  classical
  let b (j : ℕ) :=
    bProductCoeff (!s) t M L K (N - 2 * j) R (swapInput Q) P ((L₁ (!t) ^ j) S)
  let g (j F k : ℕ) : ℂ :=
    (j.factorial : ℂ)⁻¹ *
      (b j F * (-1 : ℂ) ^ F * (Ring.choose (detectorExponent M N j - (F : ℂ)) k * (-1 : ℂ) ^ k))
  calc
    _ = ((-1 : ℂ) ^ (3 + K) * I ^ (-energyPole K L)) *
          ∑ h ∈ Finset.range (E + 1), ∑ j ∈ Finset.range (min h (N / 2) + 1),
            g j (E - h) (h - j) := by
      rw [bProductCoeff_slot23_exchange s t M K L N Q R P S E hQ hR hS, mul_assoc]
      apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (3 + K) * z)
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro j hj
      have hhE := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
      have hjh := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans (min_le_left _ _)
      rw [slot23_choose_reflection M N E h j hhE hjh]
      rw [sub_eq_add_neg, zpow_add₀ Complex.I_ne_zero, zpow_twice, Complex.I_sq]
      dsimp only [g, b, detectorExponent, energyPole]
      ring
    _ = _ := by
      rw [sum_slot23_indices]
      apply congrArg (fun z : ℂ => ((-1 : ℂ) ^ (3 + K) * I ^ (-energyPole K L)) * z)
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ≤ E
      · rw [ite_eq_left hj, shiftedCoeff, ite_eq_left hj, binomialCoeff, Finset.mul_sum]
      · simp [shiftedCoeff, hj]

private theorem bEnergyTerm_factor (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    {x z : ℂ} (hx : x ≠ 0) (hz : z ≠ 0) (E : ℕ) :
    bEnergyTerm s t M K L N Q R P S x z E =
      (z ^ (-energyPole K L) * x ^ ((N : ℤ) - M)) *
        (bProductCoeff s t M K L N Q R P S E * ((z / x) ^ (2 : ℕ)) ^ E) := by
  rw [bEnergyTerm,
    show 2 * (E : ℤ) - energyPole K L = -energyPole K L + 2 * (E : ℤ) by ring,
    show (N : ℤ) - M - 2 * (E : ℤ) = ((N : ℤ) - M) + -(2 * (E : ℤ)) by ring,
    zpow_add₀ hz, zpow_add₀ hx, zpow_neg x (2 * (E : ℤ)), zpow_twice, zpow_twice, div_pow, div_pow]
  simp only [div_eq_mul_inv]
  ring

set_option maxHeartbeats 1200000 in
-- The homogeneous summability and energy regrouping use the concrete state types.
private theorem bProductCoeff_summable_on_disk (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun F : ℕ => bProductCoeff s t M K L N Q R P S F * w ^ F) := by
  by_cases hw₀ : w = 0
  · subst w
    apply summable_of_ne_finset_zero (s := {0})
    intro F hF
    simp only [Finset.mem_singleton] at hF
    simp [zero_pow hF]
  let z := w ^ (2⁻¹ : ℂ)
  have hsq : z ^ (2 : ℕ) = w := Complex.cpow_ofNat_inv_pow w 2
  have hz : z ≠ 0 := by
    intro he
    apply hw₀
    simpa [he] using hsq.symm
  have hzr : ‖z‖ < ‖(1 : ℂ)‖ := by
    have hn : ‖z‖ ^ (2 : ℕ) = ‖w‖ := by rw [← norm_pow, hsq]
    rw [norm_one]
    by_contra! h
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h 2
    rw [one_pow, hn] at hs
    exact (not_le_of_gt hw) hs
  have hj := b_joint_product_summable_of_homogeneous s t M K L N Q R P S
    hQ hR hP hS hKL hNM one_ne_zero hz hzr
  have he := (bEnergy_hasSum_iff s t M K L N Q R P S hQ hR hP hS hKL 1 z _).mpr hj.hasSum
  have hp : z ^ (-energyPole K L) ≠ 0 := zpow_ne_zero _ hz
  apply (summable_mul_left_iff hp).mp
  apply he.summable.congr
  intro F
  simpa only [one_zpow, mul_one, div_one, hsq] using
    (bEnergyTerm_factor s t M K L N Q R P S one_ne_zero hz F)

set_option maxHeartbeats 1200000 in
-- The lowered states require elaborating their complete grade and parity data.
/-- The actual normalized B energy series is the reflected finite detector
sum on the half disk, with the principal binomial and the upper phase. -/
theorem bProductCoeff_slot23_hasSum (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {y : ℂ} (hy : ‖y‖ < 1 / 2) :
    HasSum (fun E : ℕ => bProductCoeff s t M K L N Q R P S E * y ^ E)
      (((-1 : ℂ) ^ (3 + K) * I ^ (-energyPole K L)) *
        ∑ j ∈ Finset.range (N / 2 + 1), ((j.factorial : ℂ)⁻¹ * y ^ j) *
          ((1 - y) ^ detectorExponent M N j * ∑' F : ℕ,
            bProductCoeff (!s) t M L K (N - 2 * j) R (swapInput Q) P ((L₁ (!t) ^ j) S) F *
              (-y / (1 - y)) ^ F)) := by
  let r := ‖y‖
  let q := r / (1 - r)
  have hr₀ : 0 ≤ r := norm_nonneg _
  have hr : r < 1 := by dsimp only [r]; linarith
  have hq₀ : 0 ≤ q := div_nonneg hr₀ (sub_pos.mpr hr).le
  have hq : q < 1 := (div_lt_one (sub_pos.mpr hr)).mpr (by dsimp only [r]; linarith)
  let b (j : ℕ) :=
    bProductCoeff (!s) t M L K (N - 2 * j) R (swapInput Q) P ((L₁ (!t) ^ j) S)
  have hQ' : (swapInput Q).val ∈ actualGrade ℒ leechUnit K := by simpa only [swapInput_val] using hQ
  have hLK : Odd ((L : ℤ) + K) := by rwa [add_comm]
  have hb (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      Summable (fun F : ℕ => ‖b j F‖ * q ^ F) := by
    have hjN := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hj2 : 2 * j ≤ N := by omega
    have hNM' : Odd (((N - 2 * j : ℕ) : ℤ) - M) := by
      obtain ⟨m, hm⟩ := hNM
      refine ⟨m - j, ?_⟩
      push_cast [Nat.cast_sub hj2]
      omega
    have hrad : ‖(q : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq₀]
      exact hq
    have hdisk := bProductCoeff_summable_on_disk (!s) t M L K (N - 2 * j) R (swapInput Q) P
      ((L₁ (!t) ^ j) S) hR hQ' hP (lowered_grade hS hjN) hLK hNM' hrad
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq₀]
      using hdisk.norm
  have hrows (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      HasSum (fun E : ℕ => (j.factorial : ℂ)⁻¹ *
        (shiftedCoeff (detectorExponent M N j) (b j) j E * y ^ E))
        (((j.factorial : ℂ)⁻¹ * y ^ j) * ((1 - y) ^ detectorExponent M N j *
          ∑' F : ℕ, b j F * (-y / (1 - y)) ^ F)) := by
    simpa only [mul_assoc] using
      (hasSum_shiftedCoeff (detectorExponent M N j) (b j) j hr (hb j hj)).mul_left
        ((j.factorial : ℂ)⁻¹)
  have hs := (hasSum_sum (s := Finset.range (N / 2 + 1)) hrows).mul_left
    ((-1 : ℂ) ^ (3 + K) * I ^ (-energyPole K L))
  refine hs.congr_fun fun E => ?_
  rw [bProductCoeff_eq_shiftedCoeff s t M K L N Q R P S hQ hR hS E, mul_assoc,
    Finset.sum_mul]
  simp only [b, mul_assoc]

set_option maxHeartbeats 1200000 in
-- The native joint and energy terms require unfolding the concrete state types.
/-- The slot-(2,3) transport of the actual native B product compares the
source at (1, sqrt y) with the lowered products at (sqrt (1-y), I*sqrt y).
Both square roots are principal powers. -/
theorem b_joint_product_hasSum_slot23 (s t : Bool) (M K L N : ℕ)
    (Q : State s) (R : State (!s)) (P : State t) (S : State (!t))
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {y : ℂ} (hy₀ : y ≠ 0) (hy : ‖y‖ < 1 / 2) :
    let zRoot := y ^ (2⁻¹ : ℂ)
    let d := (1 - y) ^ (2⁻¹ : ℂ)
    HasSum (bJointTerm s t Q R P S 1 zRoot)
      ((-1 : ℂ) ^ (3 + K) *
        ∑ j ∈ Finset.range (N / 2 + 1), (y ^ j / (j.factorial : ℂ)) *
          ∑' i : ℤ × ℤ, bJointTerm (!s) t R (swapInput Q) P ((L₁ (!t) ^ j) S) d (I * zRoot) i) := by
  dsimp only
  let zRoot := y ^ (2⁻¹ : ℂ)
  let d := (1 - y) ^ (2⁻¹ : ℂ)
  let tRoot := I * zRoot
  have hy₁ : 1 - y ≠ 0 := by
    intro h
    have he : y = 1 := (sub_eq_zero.mp h).symm
    have : (1 : ℝ) < 1 / 2 := by simpa [he] using hy
    norm_num at this
  have hzsq : zRoot ^ (2 : ℕ) = y := Complex.cpow_ofNat_inv_pow y 2
  have hdsq : d ^ (2 : ℕ) = 1 - y := Complex.cpow_ofNat_inv_pow (1 - y) 2
  have hz : zRoot ≠ 0 := by
    intro h
    apply hy₀
    simpa [h] using hzsq.symm
  have hd : d ≠ 0 := by
    intro h
    apply hy₁
    simpa [h] using hdsq.symm
  have ht : tRoot ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have hrat : (tRoot / d) ^ (2 : ℕ) = -y / (1 - y) := by
    dsimp only [tRoot]
    rw [div_pow, hdsq, mul_pow, Complex.I_sq, hzsq, neg_one_mul]
  have hrad : ‖tRoot‖ < ‖d‖ := by
    have htri : (1 : ℝ) ≤ ‖1 - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel, norm_one] using (norm_add_le (1 - y) y)
    have htSq : ‖tRoot‖ ^ (2 : ℕ) = ‖y‖ := by
      dsimp only [tRoot]
      rw [← norm_pow, mul_pow, Complex.I_sq, hzsq, neg_one_mul, norm_neg]
    have hdSq : ‖d‖ ^ (2 : ℕ) = ‖1 - y‖ := by rw [← norm_pow, hdsq]
    by_contra! h
    have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [hdSq, htSq] at hh
    linarith
  let b (j : ℕ) :=
    bProductCoeff (!s) t M L K (N - 2 * j) R (swapInput Q) P ((L₁ (!t) ^ j) S)
  let B (j : ℕ) := bJointTerm (!s) t R (swapInput Q) P ((L₁ (!t) ^ j) S) d tRoot
  have hQ' : (swapInput Q).val ∈ actualGrade ℒ leechUnit K := by simpa only [swapInput_val] using hQ
  have hLK : Odd ((L : ℤ) + K) := by rwa [add_comm]
  have hpole : energyPole L K = energyPole K L := by dsimp only [energyPole]; ring
  have hphase : tRoot ^ (-energyPole K L) = I ^ (-energyPole K L) * zRoot ^ (-energyPole K L) := by
    exact mul_zpow _ _ _
  have htarget (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      (∑' i : ℤ × ℤ, B j i) =
        (tRoot ^ (-energyPole K L) * (1 - y) ^ detectorExponent M N j) *
          ∑' F : ℕ, b j F * (-y / (1 - y)) ^ F := by
    have hjN := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hj2 : 2 * j ≤ N := by omega
    have hS' := lowered_grade hS hjN
    have hNM' : Odd (((N - 2 * j : ℕ) : ℤ) - M) := by
      obtain ⟨m, hm⟩ := hNM
      refine ⟨m - j, ?_⟩
      push_cast [Nat.cast_sub hj2]
      omega
    have hδ : ((((N - 2 * j : ℕ) : ℤ) - M : ℤ) : ℂ) * (2⁻¹ : ℂ) =
        detectorExponent M N j := by
      dsimp only [detectorExponent]
      push_cast [Nat.cast_sub hj2]
      ring
    have hdpow : d ^ (((N - 2 * j : ℕ) : ℤ) - M) = (1 - y) ^ detectorExponent M N j := by
      rw [← hδ, Complex.cpow_int_mul]
    have hjoint : Summable (B j) :=
      b_joint_product_summable_of_homogeneous (!s) t M L K (N - 2 * j) R (swapInput Q) P
        ((L₁ (!t) ^ j) S) hR hQ' hP hS' hLK hNM' hd ht hrad
    have henergy := (bEnergy_hasSum_iff (!s) t M L K (N - 2 * j) R (swapInput Q) P
      ((L₁ (!t) ^ j) S) hR hQ' hP hS' hLK d tRoot _).mpr hjoint.hasSum
    have heq (F : ℕ) : bEnergyTerm (!s) t M L K (N - 2 * j) R (swapInput Q) P
        ((L₁ (!t) ^ j) S) d tRoot F =
          (tRoot ^ (-energyPole K L) * (1 - y) ^ detectorExponent M N j) *
            (b j F * (-y / (1 - y)) ^ F) := by
      rw [bEnergyTerm_factor (!s) t M L K (N - 2 * j) R (swapInput Q) P
        ((L₁ (!t) ^ j) S) hd ht F, hpole, hdpow, hrat]
    simpa only [heq, tsum_mul_left] using henergy.tsum_eq.symm
  change HasSum (bJointTerm s t Q R P S 1 zRoot)
    ((-1 : ℂ) ^ (3 + K) *
      ∑ j ∈ Finset.range (N / 2 + 1), (y ^ j / (j.factorial : ℂ)) * ∑' i : ℤ × ℤ, B j i)
  apply (bEnergy_hasSum_iff s t M K L N Q R P S hQ hR hP hS hKL 1 zRoot _).mp
  have hnormalized := (bProductCoeff_slot23_hasSum s t M K L N Q R P S
    hQ hR hP hS hKL hNM hy).mul_left (zRoot ^ (-energyPole K L))
  have hvalue : (zRoot ^ (-energyPole K L)) *
      (((-1 : ℂ) ^ (3 + K) * I ^ (-energyPole K L)) *
        ∑ j ∈ Finset.range (N / 2 + 1), ((j.factorial : ℂ)⁻¹ * y ^ j) *
          ((1 - y) ^ detectorExponent M N j * ∑' F : ℕ, b j F * (-y / (1 - y)) ^ F)) =
      (-1 : ℂ) ^ (3 + K) *
        ∑ j ∈ Finset.range (N / 2 + 1), (y ^ j / (j.factorial : ℂ)) * ∑' i : ℤ × ℤ, B j i := by
    calc
      _ = (-1 : ℂ) ^ (3 + K) *
            (tRoot ^ (-energyPole K L) *
              ∑ j ∈ Finset.range (N / 2 + 1), ((j.factorial : ℂ)⁻¹ * y ^ j) *
                ((1 - y) ^ detectorExponent M N j *
                  ∑' F : ℕ, b j F * (-y / (1 - y)) ^ F)) := by rw [hphase]; ring
      _ = _ := by
        apply congrArg (fun w : ℂ => (-1 : ℂ) ^ (3 + K) * w)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [htarget j hj, div_eq_mul_inv]
        ring
  change HasSum _ ((zRoot ^ (-energyPole K L)) *
      (((-1 : ℂ) ^ (3 + K) * I ^ (-energyPole K L)) *
        ∑ j ∈ Finset.range (N / 2 + 1), ((j.factorial : ℂ)⁻¹ * y ^ j) *
          ((1 - y) ^ detectorExponent M N j * ∑' F : ℕ, b j F * (-y / (1 - y)) ^ F))) at hnormalized
  rw [hvalue] at hnormalized
  refine hnormalized.congr_fun fun E => ?_
  rw [bEnergyTerm_factor s t M K L N Q R P S one_ne_zero hz E, div_one, hzsq, one_zpow, mul_one]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic
