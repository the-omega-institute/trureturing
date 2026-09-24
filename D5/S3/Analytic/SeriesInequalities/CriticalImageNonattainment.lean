/- GID: D5/S3/Analytic/SeriesInequalities/CriticalImageNonattainment
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/CriticalImageNonattainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A critical nearest output is excluded from the finite-source closure. -/

import D5.S3.Analytic.SeriesInequalities.NegativeBoundaryEnvelope
import Mathlib.Topology.MetricSpace.HausdorffDistance

open scoped BigOperators ENNReal
open Filter Topology Finset

set_option autoImplicit false
set_option maxRecDepth 3000

namespace D5.S3.Analytic.SeriesInequalities.CriticalImageNonattainment

open FiniteSourceCriticalTail FiniteSourceClosure NegativeBoundaryEnvelope

/-- Truncation of the source boundary, retaining its full recursive extension. -/
def negativeTruncation {K : Type*} [RCLike K] (A : ℝ) (N n : ℕ) : K :=
  if n < N then -(A : K) else 0

/-- The error on the finite antidiagonal window, in weighted coordinates. -/
noncomputable def windowError {K : Type*} [RCLike K]
    (V T : WeightedArray K) (N : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ n k : ℕ, n + k < N ∧ x = ‖(V - T) (n, k)‖}

/-- An explicit ambient target has a unique nearest actual output. Actual
negative boundary truncations approach its optimal error strictly from above,
while the norm-closed finite-source image has that infimum and no minimizer.
Every nonempty finite window nevertheless attains the same minimum. -/
theorem critical_image_nonattainment {K : Type*} [RCLike K]
    (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hcrit : A * ρ = (1 - ρ) ^ 2) :
    ∃ T U : WeightedArray K, ∃ B : ℕ → WeightedArray K,
      (∀ n, T (n, 0) = (ρ ^ n) • ((-A - (A / 2) / ρ ^ n : ℝ) : K)) ∧
      (∀ n k, T (n, k + 1) = (ρ ^ (n + (k + 1))) •
        ((-amplitude A (k + 1) / 2 : ℝ) : K)) ∧
      ‖T‖ = 3 * A / 2 ∧
      (∀ n k, U (n, k) = (ρ ^ (n + k)) •
        extension (fun _ : ℕ => -(A : K)) n k) ∧
      U ∈ actualImage A ρ ∧ ‖U - T‖ = A / 2 ∧
      Metric.infDist T (actualImage A ρ) = A / 2 ∧
      (∀ V ∈ actualImage A ρ, ‖V - T‖ ≤ A / 2 ↔ V = U) ∧
      (∀ N, B N ∈ finiteSourceImage A ρ ∧
        (∀ n k, B N (n, k) = (ρ ^ (n + k)) •
          extension (negativeTruncation (K := K) A N) n k) ∧
        ‖B N - T‖ = A / 2 + A * ρ ^ N) ∧
      StrictAnti (fun N => ‖B N - T‖) ∧
      Tendsto (fun N => ‖B N - T‖) atTop (𝓝 (A / 2)) ∧
      (closure (finiteSourceImage (K := K) A ρ)).Nonempty ∧
      IsClosed (closure (finiteSourceImage (K := K) A ρ)) ∧
      Metric.infDist T (closure (finiteSourceImage A ρ)) = A / 2 ∧
      (∀ V ∈ closure (finiteSourceImage A ρ), A / 2 < ‖V - T‖) ∧
      (∀ N, 1 ≤ N → IsLeast
        {e : ℝ | ∃ V ∈ closure (finiteSourceImage A ρ), e = windowError V T N}
        (A / 2)) := by
  classical
  obtain ⟨henv, hconst, hnegative⟩ := negative_boundary_envelope (K := K) A ρ hA hρ hρ1 hcrit
  obtain ⟨hrep, hclosed, hclosure⟩ := critical_recursive_image_closure (K := K) A ρ hA hρ hρ1 hcrit
  have hp (n : ℕ) : 0 < ρ ^ n := pow_pos hρ n
  have hp1 (n : ℕ) : ρ ^ n ≤ 1 := pow_le_one₀ hρ.le hρ1.le
  have ha0 (k : ℕ) : 0 ≤ amplitude A k := (henv k).1
  have haw (k : ℕ) : ρ ^ k * amplitude A k ≤ A := by
    rw [(henv k).2]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 1 + ρ)).mpr
    have hpow : ρ ^ (2 * k + 1) ≤ ρ := by
      simpa using pow_le_pow_of_le_one hρ.le hρ1.le (show 1 ≤ 2 * k + 1 by omega)
    nlinarith only [hA, hpow]
  have hweight (n k : ℕ) : 0 ≤ ρ ^ (n + k) * amplitude A k ∧
      ρ ^ (n + k) * amplitude A k ≤ A := by
    refine ⟨mul_nonneg (hp _).le (ha0 k), ?_⟩
    rw [pow_add, mul_assoc]
    calc
      ρ ^ n * (ρ ^ k * amplitude A k) ≤ ρ ^ n * A :=
        mul_le_mul_of_nonneg_left (haw k) (hp n).le
      _ ≤ A := by nlinarith only [hA, hp1 n]
  let f : ℕ × ℕ → K := fun p =>
    if p.2 = 0 then ((-(A * ρ ^ p.1 + A / 2) : ℝ) : K)
    else ((-(ρ ^ (p.1 + p.2) * amplitude A p.2 / 2) : ℝ) : K)
  have hf (p : ℕ × ℕ) : ‖f p‖ ≤ 3 * A / 2 := by
    dsimp [f]
    split_ifs
    · rw [RCLike.norm_ofReal, abs_neg, abs_of_nonneg (by positivity)]
      nlinarith only [hA, hp1 p.1]
    · rw [RCLike.norm_ofReal, abs_neg,
        abs_of_nonneg (div_nonneg (hweight p.1 p.2).1 (by norm_num))]
      linarith only [hA, (hweight p.1 p.2).2]
  let T : WeightedArray K := ⟨f, memℓp_infty ⟨3 * A / 2, by rintro x ⟨p, rfl⟩; exact hf p⟩⟩
  have hT0 (n : ℕ) : T (n, 0) = ((-(A * ρ ^ n + A / 2) : ℝ) : K) := by simp [T, f]
  have hTk (n k : ℕ) (hk : k ≠ 0) : T (n, k) =
      ((-(ρ ^ (n + k) * amplitude A k / 2) : ℝ) : K) := by simp [T, f, hk]
  have hTnorm : ‖T‖ = 3 * A / 2 := by
    apply le_antisymm (lp.norm_le_of_forall_le (by positivity) hf)
    have he := lp.norm_apply_le_norm ENNReal.top_ne_zero T (0, 0)
    rw [hT0, RCLike.norm_ofReal, abs_neg, pow_zero, mul_one,
      abs_of_nonneg (by positivity)] at he
    linarith only [he]
  have hbound : ∀ n : ℕ, ‖(-(A : K))‖ ≤ A := by
    intro n
    simp [norm_neg, RCLike.norm_ofReal, abs_of_pos hA]
  obtain ⟨U, hUnorm, hU⟩ := hrep (fun _ => -(A : K)) hbound
  have hUm : U ∈ actualImage A ρ := ⟨_, hbound, hU⟩
  have hUval (n k : ℕ) : U (n, k) = ((-(ρ ^ (n + k) * amplitude A k) : ℝ) : K) := by
    rw [hU, hconst, RCLike.real_smul_eq_coe_mul]
    simp only [map_neg, map_mul]
    ring
  have hcoordlower (a : K) (ha : ‖a‖ ≤ A) (n : ℕ) :
      A / 2 ≤ ‖(ρ ^ n) • a - T (n, 0)‖ ∧
      (‖(ρ ^ n) • a - T (n, 0)‖ ≤ A / 2 → a = -(A : K)) := by
    have hr : -A ≤ RCLike.re a := by
      have hh := (abs_le.mp (RCLike.abs_re_le_norm a)).1
      linarith only [ha, hh]
    have he := RCLike.re_le_norm ((ρ ^ n) • a - T (n, 0))
    rw [hT0] at he
    simp only [map_sub, RCLike.smul_re, RCLike.ofReal_re] at he
    rw [hT0]
    constructor
    · nlinarith only [he, mul_nonneg (hp n).le (by linarith only [hr] : 0 ≤ RCLike.re a + A)]
    · intro hle
      have hre : RCLike.re a = -A := by nlinarith only [he, hle, hr, hp n]
      have hn : ‖a‖ = A := by
        have hh := (abs_le.mp (RCLike.abs_re_le_norm a)).1
        linarith only [hre, hh, ha]
      have hz := RCLike.re_le_neg_norm_iff_eq_neg_norm.mp (show RCLike.re a ≤ -‖a‖ by rw [hre, hn])
      simpa [hn] using hz
  have hlower (V : WeightedArray K) (hV : V ∈ actualImage A ρ) : A / 2 ≤ ‖V - T‖ := by
    obtain ⟨a, ha, hv⟩ := hV
    have hl := (hcoordlower (a 0) (ha 0) 0).1
    have he := lp.norm_apply_le_norm ENNReal.top_ne_zero (V - T) (0, 0)
    simp only [lp.coeFn_sub, Pi.sub_apply, hv, extension, Nat.add_zero] at he
    exact hl.trans he
  have hrigid (V : WeightedArray K) (hV : V ∈ actualImage A ρ)
      (hd : ‖V - T‖ ≤ A / 2) : V = U := by
    obtain ⟨a, ha, hv⟩ := hV
    have heq : a = fun _ => -(A : K) := by
      funext n
      apply (hcoordlower (a n) (ha n) n).2
      have he := (lp.norm_apply_le_norm ENNReal.top_ne_zero (V - T) (n, 0)).trans hd
      simpa only [lp.coeFn_sub, Pi.sub_apply, hv, extension, Nat.add_zero] using he
    apply lp.ext
    funext ⟨n, k⟩
    rw [hv, heq, hU]
  have hUerror : ‖U - T‖ = A / 2 := by
    apply le_antisymm _ (hlower U hUm)
    apply lp.norm_le_of_forall_le (by positivity)
    rintro ⟨n, k⟩
    change ‖U (n, k) - T (n, k)‖ ≤ A / 2
    by_cases hk : k = 0
    · subst k
      rw [hUval, hT0]
      simp only [amplitude, Nat.add_zero]
      rw [← map_sub (algebraMap ℝ K), RCLike.norm_ofReal]
      have heq : -(ρ ^ n * A) - -(A * ρ ^ n + A / 2) = A / 2 := by ring
      rw [heq, abs_of_pos (half_pos hA)]
    · rw [hUval, hTk n k hk, ← map_sub (algebraMap ℝ K), RCLike.norm_ofReal]
      have heq : -(ρ ^ (n + k) * amplitude A k) -
          -(ρ ^ (n + k) * amplitude A k / 2) = -(ρ ^ (n + k) * amplitude A k / 2) := by ring
      rw [heq, abs_neg, abs_of_nonneg (div_nonneg (hweight n k).1 (by norm_num))]
      linarith only [(hweight n k).2]
  have hb (N n : ℕ) : ‖negativeTruncation (K := K) A N n‖ ≤ A := by
    unfold negativeTruncation
    split_ifs
    · exact hbound n
    · simpa using hA.le
  choose B hBnorm hB using (fun N => hrep (negativeTruncation (K := K) A N) (hb N))
  have hBm (N : ℕ) : B N ∈ finiteSourceImage A ρ := by
    refine ⟨_, hb N, ⟨N, ?_⟩, hB N⟩
    intro n hn
    simp [negativeTruncation, show ¬ n < N by omega]
  have hBclosure (N : ℕ) : B N ∈ closure (finiteSourceImage A ρ) := subset_closure (hBm N)
  have hB0 (N n : ℕ) : ‖(B N - T) (n, 0)‖ =
      if n < N then A / 2 else A / 2 + A * ρ ^ n := by
    change ‖B N (n, 0) - T (n, 0)‖ = _
    rw [hB, hT0]
    simp only [extension, Nat.add_zero, negativeTruncation]
    split_ifs with hn
    · rw [RCLike.real_smul_eq_coe_mul]
      simp only [← map_mul (algebraMap ℝ K), ← map_neg (algebraMap ℝ K),
        ← map_sub (algebraMap ℝ K), RCLike.norm_ofReal]
      have heq : ρ ^ n * -A - -(A * ρ ^ n + A / 2) = A / 2 := by ring
      rw [heq, abs_of_pos (half_pos hA)]
    · simp only [smul_zero, zero_sub, norm_neg, RCLike.norm_ofReal, abs_neg]
      rw [abs_of_nonneg (by positivity)]
      ring
  have hBk (N n k : ℕ) (hk : k ≠ 0) : ‖(B N - T) (n, k)‖ ≤ A / 2 := by
    let x : ℕ → ℝ := fun j => if j < N then A else 0
    have hx (j : ℕ) : 0 ≤ x j ∧ x j ≤ A := by dsimp [x]; split_ifs <;> constructor <;> linarith only [hA]
    obtain ⟨q, hq0, hqA, hq⟩ := hnegative x hx n k
    have hxb : (fun j => -(x j : K)) = negativeTruncation (K := K) A N := by
      funext j
      simp only [x, negativeTruncation]
      split_ifs <;> simp
    rw [hxb] at hq
    change ‖B N (n, k) - T (n, k)‖ ≤ A / 2
    rw [hB, hq, hTk n k hk, RCLike.real_smul_eq_coe_mul]
    simp only [← map_neg (algebraMap ℝ K), ← map_mul (algebraMap ℝ K),
      ← map_sub (algebraMap ℝ K), RCLike.norm_ofReal]
    apply le_trans (abs_le.mpr ?_) (by linarith only [(hweight n k).2] :
      ρ ^ (n + k) * amplitude A k / 2 ≤ A / 2)
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_left hqA (hp (n + k)).le,
      mul_nonneg (hp (n + k)).le hq0]
  have hBerror (N : ℕ) : ‖B N - T‖ = A / 2 + A * ρ ^ N := by
    apply le_antisymm
    · apply lp.norm_le_of_forall_le (by positivity)
      rintro ⟨n, k⟩
      by_cases hk : k = 0
      · subst k
        rw [hB0]
        split_ifs with hn
        · nlinarith only [hA, hp N]
        · have hpow := pow_le_pow_of_le_one hρ.le hρ1.le (show N ≤ n by omega)
          nlinarith only [hA, hpow]
      · exact (hBk N n k hk).trans (by nlinarith only [hA, hp N])
    · have he := lp.norm_apply_le_norm ENNReal.top_ne_zero (B N - T) (N, 0)
      simpa only [hB0, lt_self_iff_false, if_false] using he
  have hlim : Tendsto (fun N => ‖B N - T‖) atTop (𝓝 (A / 2)) := by
    simp_rw [hBerror]
    convert tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul A) using 1 <;> simp
  have hanti : StrictAnti (fun N => ‖B N - T‖) := by
    apply strictAnti_nat_of_succ_lt
    intro n
    rw [hBerror, hBerror, pow_succ]
    nlinarith only [hρ1, mul_pos hA (hp n)]
  have hne : (closure (finiteSourceImage (K := K) A ρ)).Nonempty := ⟨B 0, hBclosure 0⟩
  have hfullinf : Metric.infDist T (actualImage A ρ) = A / 2 := by
    apply le_antisymm
    · have he := Metric.infDist_le_dist_of_mem hUm (x := T)
      simpa only [dist_eq_norm, norm_sub_rev, hUerror] using he
    · apply (Metric.le_infDist ⟨U, hUm⟩).mpr
      intro V hV
      simpa only [dist_eq_norm, norm_sub_rev] using hlower V hV
  have hinf : Metric.infDist T (closure (finiteSourceImage A ρ)) = A / 2 := by
    apply le_antisymm
    · have hbnd (N : ℕ) : Metric.infDist T (closure (finiteSourceImage A ρ)) ≤
          ‖B N - T‖ := by
        have he := Metric.infDist_le_dist_of_mem (hBclosure N) (x := T)
        rwa [dist_eq_norm, norm_sub_rev] at he
      exact ge_of_tendsto hlim (Filter.Eventually.of_forall hbnd)
    · apply (Metric.le_infDist hne).mpr
      intro V hV
      simpa only [dist_eq_norm, norm_sub_rev] using hlower V (hclosure hV).1
  have hUnot : U ∉ closure (finiteSourceImage A ρ) := by
    intro hu
    have ht := (hclosure hu).2
    have hcpos : 0 < A / (1 + ρ) := div_pos hA (by positivity)
    obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp ht (A / (1 + ρ)) hcpos
    have hsmall := hL L le_rfl
    rw [Real.dist_eq, sub_zero] at hsmall
    have hbdd : BddAbove {x : ℝ | ∃ n k : ℕ, L ≤ n + k ∧ x = ‖U (n, k)‖} := by
      refine ⟨‖U‖, ?_⟩
      rintro x ⟨n, k, hn, rfl⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero U (n, k)
    have hentry : ‖U (0, L)‖ ≤ tail U L := le_csSup hbdd ⟨0, L, by omega, rfl⟩
    rw [hUval, RCLike.norm_ofReal, abs_neg, Nat.zero_add,
      abs_of_nonneg (mul_nonneg (hp L).le (ha0 L)), (henv L).2] at hentry
    have hnonneg : 0 ≤ ρ ^ (2 * L + 1) := (hp _).le
    have habs := le_abs_self (tail U L)
    nlinarith only [hcpos, hsmall, hentry, hnonneg, habs]
  have hno (V : WeightedArray K) (hV : V ∈ closure (finiteSourceImage A ρ)) :
      A / 2 < ‖V - T‖ := by
    by_contra hh
    have heq := hrigid V (hclosure hV).1 (le_of_not_gt hh)
    exact hUnot (heq ▸ hV)
  have hwindow (N : ℕ) (hN : 1 ≤ N) : IsLeast
      {e : ℝ | ∃ V ∈ closure (finiteSourceImage A ρ), e = windowError V T N} (A / 2) := by
    have hbdd (V : WeightedArray K) : BddAbove
        {x : ℝ | ∃ n k : ℕ, n + k < N ∧ x = ‖(V - T) (n, k)‖} := by
      refine ⟨‖V - T‖, ?_⟩
      rintro x ⟨n, k, hn, rfl⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (V - T) (n, k)
    have hzero (V : WeightedArray K) : ‖(V - T) (0, 0)‖ ≤ windowError V T N :=
      le_csSup (hbdd V) ⟨0, 0, by omega, rfl⟩
    have hwlow (V : WeightedArray K) (hV : V ∈ closure (finiteSourceImage A ρ)) :
        A / 2 ≤ windowError V T N := by
      obtain ⟨a, ha, hv⟩ := (hclosure hV).1
      have hl := (hcoordlower (a 0) (ha 0) 0).1
      have hz := hzero V
      simp only [lp.coeFn_sub, Pi.sub_apply, hv, extension, Nat.add_zero] at hz
      exact hl.trans hz
    constructor
    · refine ⟨B N, hBclosure N, le_antisymm (hwlow _ (hBclosure N)) ?_⟩
      unfold windowError
      apply csSup_le (show Set.Nonempty
        {x : ℝ | ∃ n k : ℕ, n + k < N ∧ x = ‖(B N - T) (n, k)‖} from
          ⟨‖(B N - T) (0, 0)‖, 0, 0, by omega, rfl⟩)
      rintro x ⟨n, k, hnk, rfl⟩
      by_cases hk : k = 0
      · subst k
        rw [hB0, if_pos (by omega)]
      · exact hBk N n k hk
    · rintro e ⟨V, hV, rfl⟩
      exact hwlow V hV
  refine ⟨T, U, B, ?_, ?_, hTnorm, hU, hUm, hUerror, hfullinf, ?_,
    fun N => ⟨hBm N, hB N, hBerror N⟩, hanti, hlim, hne, isClosed_closure, hinf, hno, hwindow⟩
  · intro n
    rw [hT0, RCLike.real_smul_eq_coe_mul, ← map_mul (algebraMap ℝ K)]
    congr 1
    field_simp [(hp n).ne']
    <;> ring
  · intro n k
    rw [hTk n (k + 1) (by omega), RCLike.real_smul_eq_coe_mul,
      ← map_mul (algebraMap ℝ K)]
    congr 1
    ring
  · intro V hV
    exact ⟨hrigid V hV, fun h => h ▸ hUerror.le⟩

#print axioms critical_image_nonattainment
end D5.S3.Analytic.SeriesInequalities.CriticalImageNonattainment
