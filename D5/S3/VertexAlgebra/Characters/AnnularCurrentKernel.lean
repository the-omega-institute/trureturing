/- GID: D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Characters/AnnularCurrentKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolutely convergent annular current kernels and the regularized Weierstrass lattice sum. -/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The scalar annular kernel is compared with the original regularized lattice sum. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable section
open Complex Filter Topology
open scoped BigOperators Real

namespace D5.S3.VertexAlgebra.AnnularCurrentKernel

/-- The exponential coordinate with additive period one. -/
def expCoord (w : ℂ) : ℂ := exp (2 * π * I * w)

/-- The period pair of the complex torus with modulus `τ`. -/
def periodPair (τ : UpperHalfPlane) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have hi := congrArg Complex.im h
    simp at hi
    have hb : b = 0 := hi.resolve_right (ne_of_gt τ.im_pos)
    subst b
    simpa using h

/-- Two independent radial parameters before the annular substitution. -/
def splitKernel (q₁ q₂ : ℂ) : ℂ :=
  ∑' n : ℕ+, (n : ℂ) * (q₁ ^ (n : ℕ) + q₂ ^ (n : ℕ)) /
    (1 - (q₁ * q₂) ^ (n : ℕ))

/-- The ordinary multiplicative-coordinate annular kernel. -/
def annularKernel (q z : ℂ) : ℂ := splitKernel (q / z) z

private def lambert (q a : ℂ) : ℂ :=
  ∑' n : ℕ+, (n : ℂ) * a ^ (n : ℕ) / (1 - q ^ (n : ℕ))

private def moment (a : ℂ) : ℂ := ∑' n : ℕ+, (n : ℂ) * a ^ (n : ℕ)

private lemma expCoord_add (u v : ℂ) : expCoord (u + v) = expCoord u * expCoord v := by
  simp [expCoord, mul_add, exp_add]

private lemma expCoord_nat_mul (n : ℕ) (u : ℂ) :
    expCoord ((n : ℂ) * u) = expCoord u ^ n := by
  simpa [expCoord, mul_left_comm, mul_comm, mul_assoc] using
    (Complex.exp_nat_mul (2 * π * I * u) n)

private lemma expCoord_norm_lt_one {u : ℂ} (hu : 0 < u.im) : ‖expCoord u‖ < 1 :=
  UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨u, hu⟩

private lemma expCoord_div (u v : ℂ) : expCoord u / expCoord v = expCoord (u - v) := by
  simp [expCoord, mul_sub, exp_sub]

private lemma first_moment_summable {a : ℂ} (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ+ => (n : ℂ) * a ^ (n : ℕ)) := by
  have hs : Summable (fun n : ℕ => (n : ℂ) * a ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 ha
  exact hs.comp_injective PNat.coe_injective

private lemma denominator_bound {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ+) :
    0 < 1 - ‖q‖ ∧ 1 - ‖q‖ ≤ ‖1 - q ^ (n : ℕ)‖ := by
  refine ⟨sub_pos.mpr hq, ?_⟩
  have hp := pow_le_of_le_one (norm_nonneg q) hq.le (ne_of_gt n.pos)
  have hn := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ))
  rw [norm_one, norm_pow] at hn
  linarith

private lemma lambert_summable {q a : ℂ} (hq : ‖q‖ < 1) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ+ => (n : ℂ) * a ^ (n : ℕ) / (1 - q ^ (n : ℕ))) := by
  apply Summable.of_norm_bounded ((first_moment_summable ha).norm.div_const (1 - ‖q‖))
  intro n
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (denominator_bound hq n).1
    (denominator_bound hq n).2

private lemma annularKernel_eq_lambert {q z : ℂ} (hz : z ≠ 0)
    (hq : ‖q‖ < 1) (hz₁ : ‖z‖ < 1) (hqz : ‖q / z‖ < 1) :
    annularKernel q z = lambert q (q / z) + lambert q z := by
  unfold annularKernel splitKernel lambert
  simp only [div_mul_cancel₀ _ hz, mul_add, add_div]
  exact Summable.tsum_add (lambert_summable hq hqz) (lambert_summable hq hz₁)

private lemma strict_annulus (τ : UpperHalfPlane) (w : ℂ)
    (hw : 0 < w.im) (hwτ : w.im < τ.im) :
    expCoord τ ≠ 0 ∧ expCoord w ≠ 0 ∧
      0 < ‖expCoord τ‖ ∧ ‖expCoord τ‖ < ‖expCoord w‖ ∧
      ‖expCoord w‖ < 1 ∧ ‖expCoord τ / expCoord w‖ < 1 := by
  have hz : expCoord w ≠ 0 := Complex.exp_ne_zero _
  have hqz : ‖expCoord τ / expCoord w‖ < 1 := by
    rw [expCoord_div]
    exact expCoord_norm_lt_one (by simpa using sub_pos.mpr hwτ)
  have hq : expCoord τ ≠ 0 := Complex.exp_ne_zero _
  refine ⟨hq, hz, norm_pos_iff.mpr hq, ?_, expCoord_norm_lt_one hw, hqz⟩
  rw [norm_div] at hqz
  exact (div_lt_one (norm_pos_iff.mpr hz)).mp hqz

/-- Both geometric first moments control the strict annular kernel. -/
theorem annular_summable (τ : UpperHalfPlane) (w : ℂ)
    (hw : 0 < w.im) (hwτ : w.im < τ.im) :
    Summable (fun n : ℕ+ => (n : ℂ) *
      ((expCoord τ / expCoord w) ^ (n : ℕ) + expCoord w ^ (n : ℕ)) /
      (1 - expCoord τ ^ (n : ℕ))) := by
  obtain ⟨_, _, _, hqz₀, hz, hqz⟩ := strict_annulus τ w hw hwτ
  simpa [mul_add, add_div] using
    (lambert_summable (hqz₀.trans hz) hqz).add
      (lambert_summable (hqz₀.trans hz) hz)

private def jacobianSq : ℂ := (2 * π * I) ^ 2

private def row (u : ℂ) : ℂ := ∑' m : ℤ, 1 / (u + m) ^ 2

private lemma row_summable (u : ℂ) :
    Summable (fun m : ℤ => 1 / (u + m) ^ 2) := by
  simpa using EisensteinSeries.linear_right_summable u 1 (k := 2) (by norm_num)

private lemma row_fourier (u : ℂ) (hu : 0 < u.im) :
    row u = jacobianSq * moment (expCoord u) := by
  simpa [row, jacobianSq, moment, expCoord] using
    EisensteinSeries.qExpansion_identity_pnat (k := 1) (by norm_num) ⟨u, hu⟩

private lemma row_neg (u : ℂ) : row (-u) = row u := by
  unfold row
  rw [← tsum_comp_neg]
  apply tsum_congr
  intro m
  simp only [Int.cast_neg]
  congr 1
  ring

private lemma row_zero (τ : UpperHalfPlane) : row 0 = (π : ℂ) ^ 2 / 3 := by
  have h := EisensteinSeries.e2Summand_zero_eq_two_riemannZeta_two τ
  simp only [EisensteinSeries.e2Summand, EisensteinSeries.eisSummand] at h
  convert h using 1 <;> simp [row, riemannZeta_two] <;> ring

private lemma moment_double_summable {q a : ℂ} (hq : ‖q‖ < 1) (ha : ‖a‖ < 1) :
    Summable (fun p : ℕ × ℕ+ => (p.2 : ℂ) * (a * q ^ p.1) ^ (p.2 : ℕ)) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one hq).norm.mul_of_nonneg
      (first_moment_summable ha).norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
  intro ⟨m, n⟩
  simp only [norm_mul, norm_pow]
  rw [mul_pow]
  calc
    ‖(n : ℂ)‖ * (‖a‖ ^ (n : ℕ) * (‖q‖ ^ m) ^ (n : ℕ)) =
        (‖(n : ℂ)‖ * ‖a‖ ^ (n : ℕ)) * (‖q‖ ^ m) ^ (n : ℕ) := by ring
    _ ≤ (‖(n : ℂ)‖ * ‖a‖ ^ (n : ℕ)) * ‖q‖ ^ m := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) hq.le
        (Nat.le_mul_of_pos_right m n.pos)
    _ = _ := by ring

private lemma moment_rows_summable {q a : ℂ} (hq : ‖q‖ < 1) (ha : ‖a‖ < 1) :
    Summable (fun m : ℕ => moment (a * q ^ m)) :=
  (moment_double_summable hq ha).prod

private lemma moment_rows_eq_lambert {q a : ℂ} (hq : ‖q‖ < 1) (ha : ‖a‖ < 1) :
    (∑' m : ℕ, moment (a * q ^ m)) = lambert q a := by
  unfold moment lambert
  rw [← Summable.tsum_comm
    (f := fun (m : ℕ) (n : ℕ+) => (n : ℂ) * (a * q ^ m) ^ (n : ℕ))
    (moment_double_summable hq ha)]
  apply tsum_congr
  intro n
  have hqn : ‖q ^ (n : ℕ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (ne_of_gt n.pos)
  calc
    (∑' m : ℕ, (n : ℂ) * (a * q ^ m) ^ (n : ℕ)) =
        (n : ℂ) * a ^ (n : ℕ) * ∑' m : ℕ, (q ^ (n : ℕ)) ^ m := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm m (n : ℕ)]
      ring
    _ = _ := by rw [tsum_geometric_of_norm_lt_one hqn]; rfl

/-- The subtraction remains inside the absolutely summable lattice sum during reindexing. -/
private lemma weierstrass_rows (τ : UpperHalfPlane) (w : ℂ) :
    (periodPair τ).weierstrassP w =
      ∑' n : ℤ, (row (w + n * (τ : ℂ)) - row (n * (τ : ℂ))) := by
  let L := periodPair τ
  let f : L.lattice → ℂ := fun l => 1 / (w - l) ^ 2 - 1 / (l : ℂ) ^ 2
  let e : ℤ × ℤ ≃ L.lattice :=
    (Equiv.prodComm ℤ ℤ).trans ((Equiv.neg (ℤ × ℤ)).trans L.latticeEquivProd.symm.toEquiv)
  have he (p : ℤ × ℤ) : (e p : ℂ) = -(p.2 + p.1 * (τ : ℂ)) := by
    change (L.latticeEquivProd.symm (-p.2, -p.1) : ℂ) = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [L, periodPair, add_comm]
  have hterm (p : ℤ × ℤ) : f (e p) =
      1 / ((w + p.1 * (τ : ℂ)) + p.2) ^ 2 -
        1 / ((p.1 : ℂ) * (τ : ℂ) + p.2) ^ 2 := by
    dsimp [f]
    rw [he]
    congr 1 <;> congr 1 <;> ring
  have hs : Summable (fun p : ℤ × ℤ =>
      1 / ((w + p.1 * (τ : ℂ)) + p.2) ^ 2 -
        1 / ((p.1 : ℂ) * (τ : ℂ) + p.2) ^ 2) :=
    (e.summable_iff.mpr (L.hasSum_weierstrassP w).summable).congr hterm
  calc
    L.weierstrassP w = ∑' p, f (e p) := (e.tsum_eq f).symm
    _ = ∑' p : ℤ × ℤ,
        (1 / ((w + p.1 * (τ : ℂ)) + p.2) ^ 2 -
          1 / ((p.1 : ℂ) * (τ : ℂ) + p.2) ^ 2) := tsum_congr hterm
    _ = ∑' n : ℤ, ∑' m : ℤ,
        (1 / ((w + n * (τ : ℂ)) + m) ^ 2 -
          1 / ((n : ℂ) * (τ : ℂ) + m) ^ 2) := hs.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro n
      exact (row_summable _).tsum_sub (row_summable _)

private lemma shifted_rows (τ : UpperHalfPlane) (w : ℂ)
    (hw : 0 < w.im) (hwτ : w.im < τ.im) :
    Summable (fun n : ℤ => row (w + n * (τ : ℂ))) ∧
      (∑' n : ℤ, row (w + n * (τ : ℂ))) =
        jacobianSq * annularKernel (expCoord τ) (expCoord w) := by
  let q := expCoord τ
  let a := expCoord w
  let b := expCoord ((τ : ℂ) - w)
  have hq : ‖q‖ < 1 := expCoord_norm_lt_one τ.im_pos
  have ha : ‖a‖ < 1 := expCoord_norm_lt_one hw
  have hb : ‖b‖ < 1 := expCoord_norm_lt_one (by simpa using sub_pos.mpr hwτ)
  have hp (n : ℕ) : row (w + n * (τ : ℂ)) = jacobianSq * moment (a * q ^ n) := by
    rw [row_fourier _ (by
      simp only [add_im, mul_im, natCast_re, UpperHalfPlane.coe_im, natCast_im,
        zero_mul, add_zero]
      positivity), expCoord_add, expCoord_nat_mul]
  have hn (n : ℕ) : row (w + (-(n + 1) : ℤ) * (τ : ℂ)) =
      jacobianSq * moment (b * q ^ n) := by
    have he : w + ((-(n + 1) : ℤ) : ℂ) * (τ : ℂ) =
        -(((τ : ℂ) - w) + (n : ℂ) * τ) := by push_cast; ring
    rw [he, row_neg, row_fourier _ (by
      simp only [add_im, sub_im, mul_im, natCast_re, UpperHalfPlane.coe_im,
        natCast_im, zero_mul, add_zero]
      exact add_pos_of_pos_of_nonneg (sub_pos.mpr hwτ) (by positivity)),
      expCoord_add, expCoord_nat_mul]
  have hsp : Summable (fun n : ℕ => row (w + n * (τ : ℂ))) :=
    ((moment_rows_summable hq ha).mul_left jacobianSq).congr (fun n => (hp n).symm)
  have hsn : Summable (fun n : ℕ => row (w + (-(n + 1) : ℤ) * (τ : ℂ))) :=
    ((moment_rows_summable hq hb).mul_left jacobianSq).congr (fun n => (hn n).symm)
  have hsp' : Summable (fun n : ℕ => row (w + (n : ℤ) * (τ : ℂ))) := by
    simpa only [Int.cast_natCast] using hsp
  have hs := Summable.of_nat_of_neg_add_one
    (f := fun n : ℤ => row (w + n * (τ : ℂ))) hsp' hsn
  refine ⟨hs, ?_⟩
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => row (w + n * (τ : ℂ))) hsp' hsn]
  simp only [Int.cast_natCast]
  rw [show (fun n : ℕ => row (w + n * (τ : ℂ))) =
      (fun n : ℕ => jacobianSq * moment (a * q ^ n)) from funext hp]
  rw [show (fun n : ℕ => row (w + (-(n + 1) : ℤ) * (τ : ℂ))) =
      (fun n : ℕ => jacobianSq * moment (b * q ^ n)) from funext hn]
  rw [tsum_mul_left, tsum_mul_left, moment_rows_eq_lambert hq ha,
    moment_rows_eq_lambert hq hb]
  have hba : b = q / a := (expCoord_div τ w).symm
  have hza : a ≠ 0 := Complex.exp_ne_zero _
  have hqa : ‖q / a‖ < 1 := by rw [← hba]; exact hb
  change _ = jacobianSq * annularKernel q a
  rw [annularKernel_eq_lambert hza hq ha hqa, ← hba]
  ring

private lemma constant_rows (τ : UpperHalfPlane) :
    Summable (fun n : ℤ => row (n * (τ : ℂ))) ∧
      (∑' n : ℤ, row (n * (τ : ℂ))) = -jacobianSq * EisensteinSeries.E2 τ / 12 := by
  let q := expCoord τ
  have hq : ‖q‖ < 1 := expCoord_norm_lt_one τ.im_pos
  have hp (n : ℕ+) : row ((n : ℂ) * τ) =
      jacobianSq * ∑' m : ℕ+, (m : ℂ) * q ^ ((n : ℕ) * m) := by
    rw [row_fourier _ (by simpa using mul_pos (show (0 : ℝ) < n by positivity) τ.im_pos),
      expCoord_nat_mul]
    simp only [moment, ← pow_mul]
    rfl
  have hprod : Summable (fun p : ℕ+ × ℕ+ => (p.2 : ℂ) * q ^ ((p.1 : ℕ) * p.2)) := by
    simpa using summable_prod_mul_pow 1 hq
  have hspos : Summable (fun n : ℕ+ => row ((n : ℂ) * τ)) :=
    (hprod.prod.mul_left jacobianSq).congr (fun n => (hp n).symm)
  have hsNat : Summable (fun n : ℕ => row (((n + 1 : ℕ) : ℂ) * τ)) := by
    simpa using (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => row ((n : ℂ) * τ))).mp hspos
  have hseven : (fun n : ℤ => row (n * (τ : ℂ))).Even := by
    intro n
    simpa using row_neg ((n : ℂ) * τ)
  have hsneg : Summable (fun n : ℕ => row (((-(n + 1) : ℤ) : ℂ) * τ)) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      neg_mul, row_neg, Nat.cast_add, Nat.cast_one] using hsNat
  have hs : Summable (fun n : ℤ => row (n * (τ : ℂ))) :=
    Summable.of_add_one_of_neg_add_one (f := fun n : ℤ => row (n * (τ : ℂ)))
      (by simpa using hsNat) hsneg
  refine ⟨hs, ?_⟩
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hseven hs]
  simp only [Int.cast_natCast]
  have heq : (fun n : ℕ+ => row ((n : ℂ) * τ)) =
      (fun n : ℕ+ => jacobianSq * ∑' m : ℕ+, (m : ℂ) * q ^ ((n : ℕ) * m)) := funext hp
  rw [heq, tsum_mul_left]
  have hd := tsum_prod_pow_eq_tsum_sigma 1 hq
  simp only [pow_one] at hd
  rw [hd]
  simp only [Int.cast_zero, zero_mul]
  rw [row_zero τ, EisensteinSeries.E2_eq_tsum_cexp]
  simp only [nsmul_eq_mul]
  let S : ℂ := ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) * q ^ (n : ℕ)
  change (π : ℂ) ^ 2 / 3 + 2 * (jacobianSq * S) =
    -jacobianSq * (1 - 24 * S) / 12
  have hJ : jacobianSq = -4 * (π : ℂ) ^ 2 := by
    unfold jacobianSq
    calc
      (2 * π * I : ℂ) ^ 2 = 4 * (π : ℂ) ^ 2 * I ^ 2 := by ring
      _ = _ := by rw [I_sq]; ring
  rw [hJ]
  ring

/-- The ordinary annular kernel equals the lattice-defined Weierstrass function with
its exact normalized weight-two Eisenstein correction. -/
theorem annular_kernel_eq_periodPair_weierstrassP_sub_E2
    (τ : UpperHalfPlane) (w : ℂ) (hw : 0 < w.im) (hwτ : w.im < τ.im) :
    annularKernel (expCoord τ) (expCoord w) =
      (periodPair τ).weierstrassP w / (2 * π * I) ^ 2 - EisensteinSeries.E2 τ / 12 := by
  obtain ⟨hsw, hwrow⟩ := shifted_rows τ w hw hwτ
  obtain ⟨hs0, h0row⟩ := constant_rows τ
  have hP := weierstrass_rows τ w
  rw [hsw.tsum_sub hs0, hwrow, h0row] at hP
  have hC : jacobianSq ≠ 0 := by
    unfold jacobianSq
    exact pow_ne_zero _ (by simp [Real.pi_ne_zero])
  change _ = _ / jacobianSq - _
  rw [hP]
  field_simp [hC]
  <;> ring

end D5.S3.VertexAlgebra.AnnularCurrentKernel
