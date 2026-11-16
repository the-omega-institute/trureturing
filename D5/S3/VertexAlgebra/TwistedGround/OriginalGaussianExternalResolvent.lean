/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual binomial external columns and original Gaussian external contractions. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
import D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
import D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
import Mathlib.Data.Nat.Choose.Bounds

/-! Polynomial-geometric bounds retain every original input and output mode. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent

open OriginalGaussianResolvent OriginalGaussianMatrix OriginalGaussianAllIndexResolvent

/-- False denotes the input column; true denotes the output column. -/
def externalBinomial (out : Bool) (p s : ℕ) : ℂ :=
  Ring.choose (if out then (p : ℂ) + 1 / 2 else -(p : ℂ) - 1 / 2) s

def externalColumn (out : Bool) (p : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  -(Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1) * externalBinomial out p (n + 1)

private lemma choose_recurrence (a : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * Ring.choose a (n + 1) = Ring.choose a n * (a - n) := by
  have h := Ring.choose_smul_choose a (n := n + 1) (k := n) (by omega)
  simpa only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.add_sub_cancel_left,
    Ring.choose_one_right, Nat.cast_add, Nat.cast_one] using h

lemma choose_bound (p : ℕ) {a : ℂ} (ha : ‖a‖ ≤ (p + 1 : ℝ)) (s : ℕ) :
    ‖Ring.choose a s‖ ≤ (Nat.choose (p + s) s : ℝ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h := congrArg norm (choose_recurrence a s)
    simp only [norm_mul, show ‖(s + 1 : ℂ)‖ = (s + 1 : ℝ) by
      exact_mod_cast Complex.norm_natCast (s + 1)] at h
    have hsub : ‖a - (s : ℂ)‖ ≤ (p + s + 1 : ℝ) := by
      calc
        _ ≤ ‖a‖ + ‖(s : ℂ)‖ := norm_sub_le _ _
        _ ≤ (p + 1 : ℝ) + s := add_le_add ha (by simp)
        _ = _ := by ring
    have hc : ((p + s + 1).choose (s + 1) : ℝ) * (s + 1) =
        (p + s + 1 : ℝ) * ((p + s).choose s : ℝ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq (p + s) s).symm
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < s + 1)).mp
    calc
      _ = ‖Ring.choose a s‖ * ‖a - (s : ℂ)‖ := h
      _ ≤ ((p + s).choose s : ℝ) * (p + s + 1 : ℝ) :=
        mul_le_mul ih hsub (norm_nonneg _) (by positivity)
      _ = (s + 1 : ℝ) * ((p + (s + 1)).choose (s + 1) : ℝ) := by
        simpa only [Nat.add_assoc, mul_comm] using hc.symm

private lemma binomial_polynomial_bound (out : Bool) (p s : ℕ) (hs : 1 ≤ s) :
    ‖externalBinomial out p s‖ ≤ (p + 1 : ℝ) ^ p * (s : ℝ) ^ p := by
  have ha : ‖(if out then (p : ℂ) + 1 / 2 else -(p : ℂ) - 1 / 2)‖ ≤ (p + 1 : ℝ) := by
    cases out
    · rw [if_neg (by decide), show -(p : ℂ) - 1 / 2 = ((-p - 1 / 2 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) p; linarith)]
      linarith
    · rw [if_pos rfl, show (p : ℂ) + 1 / 2 = ((p + 1 / 2 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
  calc
    _ ≤ ((p + s).choose s : ℝ) := choose_bound p ha s
    _ = ((p + s).choose p : ℝ) := by rw [Nat.choose_symm_add]
    _ ≤ ((p + s : ℕ) : ℝ) ^ p := by exact_mod_cast Nat.choose_le_pow (p + s) p
    _ ≤ ((p + 1 : ℝ) * (s : ℝ)) ^ p := by
      apply pow_le_pow_left₀ (by positivity)
      have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hpr : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      push_cast
      nlinarith
    _ = _ := mul_pow _ _ _

lemma externalColumn_bound (out : Bool) (p : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) (n : ℕ) :
    ‖externalColumn out p z n‖ ≤
      (p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1) * ρ ^ (n + 1) := by
  have hs : Real.sqrt (n + 1 : ℝ) ≤ n + 1 := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1),
      Real.sqrt_nonneg (n + 1), Nat.cast_nonneg (α := ℝ) n]
  simp only [externalColumn, norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (n + 1 : ℝ) * ρ ^ (n + 1) * ((p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ p) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using binomial_polynomial_bound out p (n + 1) (by omega)
    _ = _ := by rw [pow_succ]; ring

private lemma external_majorant_summable (p : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => (p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1) * ρ ^ (n + 1)) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (p + 1) (r := ρ)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using hρ1)
  simpa only [mul_assoc, Nat.cast_add, Nat.cast_one] using ((summable_nat_add_iff 1).mpr h).mul_left ((p + 1 : ℝ) ^ p)

/-- Every fixed original input/output mode is absolutely summable on each
smaller disk, under an explicit polynomial-geometric majorant. -/
theorem externalColumn_l1 (out : Bool) (p : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    (∀ n, ‖externalColumn out p z n‖ ≤
      (p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1) * ρ ^ (n + 1)) ∧
      Summable (fun n : ℕ => ‖externalColumn out p z n‖) := by
  exact ⟨externalColumn_bound out p hρ hz,
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (externalColumn_bound out p hρ hz) (external_majorant_summable p hρ hρ1)⟩

def externalVector (out : Bool) (p : ℕ) (z : ℂ) : H :=
  ∑' n : ℕ, lp.single 2 n (externalColumn out p z n)

private lemma external_vector_summable (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖(lp.single 2 n (externalColumn out p z n) : H)‖) := by
  simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using
    (externalColumn_l1 out p (norm_nonneg z) hz le_rfl).2

lemma externalVector_apply (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    externalVector out p z n = externalColumn out p z n := by
  change (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n)
    (∑' i : ℕ, lp.single 2 i (externalColumn out p z i)) = _
  rw [(lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).map_tsum (external_vector_summable out p hz).of_norm]
  rw [tsum_eq_single n]
  · change (lp.single (E := fun _ : ℕ => ℂ) 2 n (externalColumn out p z n)) n = _
    simp
  · intro i hi
    change (lp.single (E := fun _ : ℕ => ℂ) 2 i (externalColumn out p z i)) n = 0
    simp [lp.single_apply, hi]

def externalJ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ) (z : ℂ) : ℂ :=
  ∑' st : ℕ × ℕ, externalColumn out p z st.1 *
    explicitOddEntry z (st.1 + 1) (st.2 + 1) * externalColumn out' q z st.2

def externalT (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ) (z : ℂ) : ℂ :=
  (∑' s : ℕ, externalColumn out p z s * externalColumn out' q z s) +
    ∑' skt : (ℕ × ℕ) × ℕ, externalColumn out p z skt.1.1 *
      matrixEntry z (skt.1.1 + 1) (skt.1.2 + 1) *
        explicitOddEntry z (skt.1.2 + 1) (skt.2 + 1) * externalColumn out' q z skt.2

private lemma map_entry_bound (A : H →L[ℂ] H) (n m : ℕ) :
    ‖A (basis m) n‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖A (basis m)‖ := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ _
    _ ≤ ‖A‖ * ‖basis m‖ := A.le_opNorm _
    _ = _ := by simp [basis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

lemma external_double_summable (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) (A : H →L[ℂ] H) :
    Summable (fun st : ℕ × ℕ => ‖externalColumn out p z st.1 *
      A (basis st.2) st.1 * externalColumn out' q z st.2‖) := by
  have hu := (externalColumn_l1 out p (norm_nonneg z) hz le_rfl).2
  have hw := (externalColumn_l1 out' q (norm_nonneg z) hz le_rfl).2
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun st => ?_)
    ((hu.mul_of_nonneg hw (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left ‖A‖)
  simp only [norm_mul]
  calc
    _ ≤ ‖externalColumn out p z st.1‖ * ‖A‖ * ‖externalColumn out' q z st.2‖ := by
      gcongr
      exact map_entry_bound A st.1 st.2
    _ = _ := by ring

lemma external_bilinear_expansion (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) (A : H →L[ℂ] H) :
    innerSL ℂ (star (externalVector out p z)) (A (externalVector out' q z)) =
      ∑' st : ℕ × ℕ, externalColumn out p z st.1 *
        A (basis st.2) st.1 * externalColumn out' q z st.2 := by
  rw [innerSL_apply_apply, lp.inner_eq_tsum]
  simp only [lp.star_apply, RCLike.inner_apply', ← RCLike.star_def, star_star,
    externalVector_apply out p hz]
  have hrow (n : ℕ) : A (externalVector out' q z) n =
      ∑' m : ℕ, A (basis m) n * externalColumn out' q z m := by
    let ev := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp A
    change ev (∑' m : ℕ, lp.single 2 m (externalColumn out' q z m)) = _
    rw [ev.map_tsum (external_vector_summable out' q hz).of_norm]
    apply tsum_congr
    intro m
    have he : (lp.single 2 m (externalColumn out' q z m) : H) =
        externalColumn out' q z m • basis m := by
      ext k
      simp only [basis, lp.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply]
      split_ifs <;> simp
    rw [he, map_smul]
    change externalColumn out' q z m * A (basis m) n = _
    ring
  simp_rw [hrow, ← tsum_mul_left]
  have hs := (external_double_summable out p out' q hz A).of_norm
  rw [hs.tsum_prod]
  apply tsum_congr
  intro n
  apply tsum_congr
  intro m
  ring

private lemma externalJ_bilinear (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    innerSL ℂ (star (externalVector out p z))
      (oddResolvent z (externalVector out' q z)) = externalJ out p out' q z := by
  simpa only [externalJ, oddResolvent_entry_explicit hz] using
    external_bilinear_expansion out p out' q hz (oddResolvent z)

private lemma external_triple_summable (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun skt : (ℕ × ℕ) × ℕ => ‖externalColumn out p z skt.1.1 *
      matrixEntry z (skt.1.1 + 1) (skt.1.2 + 1) *
        explicitOddEntry z (skt.1.2 + 1) (skt.2 + 1) * externalColumn out' q z skt.2‖) := by
  have hu := (externalColumn_l1 out p (norm_nonneg z) hz le_rfl).2
  have hw := (externalColumn_l1 out' q (norm_nonneg z) hz le_rfl).2
  have hg := (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg z) hz)
  have hug := hu.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => by positivity)
  have h := (hug.mul_of_nonneg hw (fun _ => by positivity) (fun _ => norm_nonneg _)).mul_left
    ‖oddResolvent z‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun skt => ?_) h
  have hK : ‖matrixEntry z (skt.1.1 + 1) (skt.1.2 + 1)‖ ≤ ‖z‖ ^ (skt.1.2 + 1) := by
    calc
      _ ≤ ‖z‖ ^ ((skt.1.1 + 1) + (skt.1.2 + 1)) := entry_bound z _ _ (by omega) (by omega)
      _ ≤ _ := by
        rw [pow_add]
        exact mul_le_of_le_one_left (by positivity)
          (pow_le_one₀ (norm_nonneg z) hz.le)
  have hJ : ‖explicitOddEntry z (skt.1.2 + 1) (skt.2 + 1)‖ ≤ ‖oddResolvent z‖ := by
    rw [← oddResolvent_entry_explicit hz]
    exact map_entry_bound _ _ _
  simp only [norm_mul]
  calc
    _ ≤ ‖externalColumn out p z skt.1.1‖ * ‖z‖ ^ (skt.1.2 + 1) *
        ‖oddResolvent z‖ * ‖externalColumn out' q z skt.2‖ := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 800000 in
private lemma externalT_bilinear (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    innerSL ℂ (star (externalVector out p z))
      (squareResolvent z (externalVector out' q z)) = externalT out p out' q z := by
  classical
  have ht := (external_triple_summable out p out' q hz).of_norm
  rw [square_eq_one_add hz]
  change innerSL ℂ (star (externalVector out p z))
    (externalVector out' q z + (operator z * oddResolvent z) (externalVector out' q z)) = _
  rw [map_add, external_bilinear_expansion out p out' q hz (operator z * oddResolvent z)]
  have hI : innerSL ℂ (star (externalVector out p z)) (externalVector out' q z) =
      ∑' s : ℕ, externalColumn out p z s * externalColumn out' q z s := by
    rw [innerSL_apply_apply, lp.inner_eq_tsum]
    simp only [lp.star_apply, RCLike.inner_apply', ← RCLike.star_def, star_star,
      externalVector_apply out p hz, externalVector_apply out' q hz]
  rw [hI]
  unfold externalT
  congr 1
  have hst := (external_double_summable out p out' q hz (operator z * oddResolvent z)).of_norm
  rw [hst.tsum_prod, ht.tsum_prod, ht.prod.tsum_prod]
  apply tsum_congr
  intro s
  have hs : Summable (fun kt : ℕ × ℕ => externalColumn out p z s *
      matrixEntry z (s + 1) (kt.1 + 1) * explicitOddEntry z (kt.1 + 1) (kt.2 + 1) *
        externalColumn out' q z kt.2) := by
    exact ht.comp_injective (i := fun kt : ℕ × ℕ => ((s, kt.1), kt.2))
      (by
        intro a b h
        exact Prod.ext (congrArg (fun x : (ℕ × ℕ) × ℕ => x.1.2) h)
          (congrArg (fun x : (ℕ × ℕ) × ℕ => x.2) h))
  rw [← hs.tsum_comm]
  apply tsum_congr
  intro t
  change externalColumn out p z s * operator z (oddResolvent z (basis t)) s *
      externalColumn out' q z t = _
  rw [operator_apply hz]
  simp_rw [oddResolvent_entry_explicit hz]
  rw [← tsum_mul_left, ← tsum_mul_right]
  apply tsum_congr
  intro k
  ring

/-- Absolute scalar contractions of the actual input and output columns.
The square contraction retains its identity contribution. -/
theorem external_contractions_explicit (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun st : ℕ × ℕ => ‖externalColumn out p z st.1 *
      explicitOddEntry z (st.1 + 1) (st.2 + 1) * externalColumn out' q z st.2‖) ∧
    Summable (fun skt : (ℕ × ℕ) × ℕ => ‖externalColumn out p z skt.1.1 *
      matrixEntry z (skt.1.1 + 1) (skt.1.2 + 1) *
        explicitOddEntry z (skt.1.2 + 1) (skt.2 + 1) * externalColumn out' q z skt.2‖) ∧
    innerSL ℂ (star (externalVector out p z))
      (oddResolvent z (externalVector out' q z)) = externalJ out p out' q z ∧
    innerSL ℂ (star (externalVector out p z))
      (squareResolvent z (externalVector out' q z)) = externalT out p out' q z ∧
    Summable (fun s : ℕ => ‖externalColumn out p z s * externalColumn out' q z s‖) := by
  refine ⟨?_, external_triple_summable out p out' q hz,
    externalJ_bilinear out p out' q hz, externalT_bilinear out p out' q hz, ?_⟩
  · simpa only [oddResolvent_entry_explicit hz] using
      external_double_summable out p out' q hz (oddResolvent z)
  · simpa only [norm_mul, externalVector_apply out p hz, externalVector_apply out' q hz] using
      (lp.summable_mul (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two)
        (externalVector out p z) (externalVector out' q z))

def externalCutoff (N : ℕ) (out : Bool) (p : ℕ) (z : ℂ) : H :=
  ∑ n ∈ Finset.range N, lp.single 2 n (externalColumn out p z n)

/-- The original binomial external columns converge in norm uniformly on
every smaller disk, for every fixed external mode. -/
private theorem externalCutoff_tendstoUniformly {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (out : Bool) (p : ℕ) :
    TendstoUniformly
      (fun N => fun z : {z : ℂ | ‖z‖ ≤ ρ} => externalCutoff N out p z)
      (fun z : {z : ℂ | ‖z‖ ≤ ρ} => externalVector out p z) atTop := by
  exact tendstoUniformly_tsum_nat (external_majorant_summable p hρ hρ1)
    (fun n z => by
      simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using
        externalColumn_bound out p hρ z.property n)

def externalMass (p : ℕ) (ρ : ℝ) : ℝ :=
  ∑' n : ℕ, (p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1) * ρ ^ (n + 1)

/-- Uniform norm control and convergence of the actual external columns. -/
theorem externalCutoff_control {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (out : Bool) (p : ℕ) :
    (∀ (z : ℂ), ‖z‖ ≤ ρ → ‖externalVector out p z‖ ≤ externalMass p ρ ∧
      ∀ N, ‖externalCutoff N out p z‖ ≤ externalMass p ρ) ∧
    TendstoUniformly
      (fun N => fun z : {z : ℂ | ‖z‖ ≤ ρ} => externalCutoff N out p z)
      (fun z : {z : ℂ | ‖z‖ ≤ ρ} => externalVector out p z) atTop := by
  refine ⟨?_, externalCutoff_tendstoUniformly hρ hρ1 out p⟩
  intro z hz
  have hs := external_majorant_summable p hρ hρ1
  have hb (n : ℕ) : ‖(lp.single 2 n (externalColumn out p z n) : H)‖ ≤
      (p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1) * ρ ^ (n + 1) := by
    simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using
      externalColumn_bound out p hρ hz n
  constructor
  · exact (norm_tsum_le_tsum_norm (external_vector_summable out p (hz.trans_lt hρ1))).trans
      ((external_vector_summable out p (hz.trans_lt hρ1)).tsum_le_tsum hb hs)
  · intro N
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ => hb n)).trans
      (hs.sum_le_tsum (Finset.range N) (fun n _ => by positivity)))

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalNormalRowSource OriginalCorrectedRowRecompositionSource

def originalExternalIndex (D : LatticeData) (x : Bool × Index D) :
    Index D ⊕ (Index D ⊕ Index D) :=
  if x.1 then .inr (.inr x.2) else .inr (.inl x.2)

/-- The literal mixed source row has the binomial frequency column. -/
lemma actual_left_mixed (D : LatticeData) (z : ℂ)
    (i : Index D) (out : Bool) (j : Index D) :
    z ^ (i.2 + 1) * correctedMatrix D (Function.Embedding.refl (Index D))
      (.inl i) (originalExternalIndex D (out, j)) =
      (Real.sqrt (i.2 + 1 : ℝ) : ℂ) * externalColumn out j.2 z i.2 *
        (D.G i.1 j.1 : ℂ) := by
  have hs : (Real.sqrt (i.2 + 1 : ℝ) : ℂ) ^ 2 = (i.2 + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ i.2 + 1)
  have ha : -(- (j.2 : ℂ) - 1) - 1 / 2 = (j.2 : ℂ) + 1 / 2 := by ring
  cases out <;>
    simp only [originalExternalIndex, Bool.false_eq_true, ↓reduceIte, correctedMatrix,
      normalMatrix, SI, SO, Function.Embedding.refl_apply, externalColumn, externalBinomial,
      Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, ha] <;>
    simp only [← hs, pow_two] <;> ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
