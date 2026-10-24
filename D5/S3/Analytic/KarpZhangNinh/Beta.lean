/- GID: D5/S3/Analytic/KarpZhangNinh/Beta
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangNinh/Beta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Algebra.Polynomial]
   utility: none
   digest: Symmetric homogeneous polynomials retain balancing monotonicity after beta lifting. -/

import D5.S3.Analytic.IncompleteBeta.Comparison
import D5.S3.Analytic.KummerRatio.BetaIntegral
import Mathlib.Topology.Algebra.Polynomial

/-!
The beta moment transform replaces the two monomial factors by rising
factorials. The coefficient signs are unrestricted. The comparison of beta
means supplies the ordering for positive shape parameters; continuity of the
lifted polynomial supplies the closed boundary.
admission_basis: escape-witness; witness: betaMean_antiOn.
utility none: all statements concern arbitrary coefficient families and degrees,
without finite enumeration, numerical certificates or numerical reduction.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

namespace D5.S3.Analytic.KarpZhangNinh.Beta

open D5.S3.Analytic.KummerRatio.BetaIntegral
open D5.S3.Analytic.IncompleteBeta.Comparison

/- proof_shape: bind-only definition; escape_witness: none;
consumer: polynomial_continuous, lift_eq_betaMean, lift_monotoneOn. -/
/-- A homogeneous polynomial written in its degree-`N` monomial basis. -/
def polynomial (c : ℕ → ℝ) (N : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), c k * x ^ k * y ^ (N - k)

/- proof_shape: bind-only definition; escape_witness: none;
consumer: lift_continuous, lift_eq_betaMean, lift_monotoneOn, Result.lift_normalization. -/
/-- The rising-factorial lift of a homogeneous polynomial. -/
def lift (c : ℕ → ℝ) (N : ℕ) (u v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    c k * (ascPochhammer ℝ k).eval u * (ascPochhammer ℝ (N - k)).eval v

/- proof_shape: bind-only; escape_witness: none;
consumer: lift_eq_betaMean, lift_monotoneOn. -/
theorem polynomial_continuous (c : ℕ → ℝ) (N : ℕ) :
    Continuous (fun t : ℝ => polynomial c N t (1 - t)) := by
  unfold polynomial
  fun_prop

/- proof_shape: bind-only; escape_witness: none;
consumer: lift_monotoneOn. -/
theorem lift_continuous (c : ℕ → ℝ) (N : ℕ) (S : ℝ) :
    Continuous (fun s : ℝ => lift c N s (S - s)) := by
  unfold lift
  fun_prop

/- proof_shape: bind-only; escape_witness: none;
consumer: lift_monotoneOn. -/
theorem polynomial_symm (c : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k ≤ N, c (N - k) = c k) (x y : ℝ) :
    polynomial c N x y = polynomial c N y x := by
  unfold polynomial
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkN, hc k hkN]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: lift_monotoneOn. -/
theorem lift_symm (c : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k ≤ N, c (N - k) = c k) (u v : ℝ) :
    lift c N u v = lift c N v u := by
  unfold lift
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkN, hc k hkN]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: lift_eq_betaMean. -/
private lemma beta_monomial {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (k l : ℕ) :
    (∫ t in (0 : ℝ)..1,
      t ^ (u - 1) * (1 - t) ^ (v - 1) * (t ^ k * (1 - t) ^ l)) =
      (ascPochhammer ℝ k).eval u * (ascPochhammer ℝ l).eval v *
        (Real.Gamma u * Real.Gamma v / Real.Gamma (u + v + (k + l : ℕ))) := by
  have heq (t : ℝ) (ht : t ∈ Ioo 0 1) :
      t ^ (u - 1) * (1 - t) ^ (v - 1) * (t ^ k * (1 - t) ^ l) =
        t ^ (u + k - 1) * (1 - t) ^ (v + l - 1) := by
    rw [show u + (k : ℝ) - 1 = u - 1 + k by ring,
      show v + (l : ℝ) - 1 = v - 1 + l by ring,
      Real.rpow_add ht.1, Real.rpow_add (sub_pos.mpr ht.2),
      Real.rpow_natCast, Real.rpow_natCast]
    ring
  rw [intervalIntegral.integral_congr_Ioo_of_le zero_le_one heq,
    integral_beta (by positivity : 0 < u + k) (by positivity : 0 < v + l),
    gamma_pochhammer hu, gamma_pochhammer hv]
  push_cast
  rw [show u + k + (v + l) = u + v + ((k : ℝ) + l) by ring]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: lift_monotoneOn. -/
theorem lift_eq_betaMean (c : ℕ → ℝ) (N : ℕ) {m d : ℝ}
    (hp : 0 < m + d) (hq : 0 < m - d) :
    lift c N (m + d) (m - d) =
      (ascPochhammer ℝ N).eval (2 * m) *
        betaMean (fun t => polynomial c N t (1 - t)) m d := by
  have hm : 0 < 2 * m := by linarith
  let w : ℝ → ℝ := fun t => t ^ (m + d - 1) * (1 - t) ^ (m - d - 1)
  have hi := intervalIntegrable_beta hp hq
  have hterm (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      IntervalIntegrable (fun t : ℝ => w t * (c k * t ^ k * (1 - t) ^ (N - k)))
        volume 0 1 := by
    exact hi.mul_continuousOn (by fun_prop)
  have hsum : (∫ t in (0 : ℝ)..1, w t * polynomial c N t (1 - t)) =
      ∑ k ∈ Finset.range (N + 1), c k *
        ((ascPochhammer ℝ k).eval (m + d) *
          (ascPochhammer ℝ (N - k)).eval (m - d) *
            (Real.Gamma (m + d) * Real.Gamma (m - d) / Real.Gamma (2 * m + N))) := by
    simp_rw [polynomial, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum hterm]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    calc
      _ = c k * ∫ t in (0 : ℝ)..1,
          t ^ (m + d - 1) * (1 - t) ^ (m - d - 1) *
            (t ^ k * (1 - t) ^ (N - k)) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext t
        dsimp [w]
        ring
      _ = _ := by
        rw [beta_monomial hp hq, Nat.add_sub_of_le hkN,
          show m + d + (m - d) = 2 * m by ring]
  unfold betaMean
  change lift c N (m + d) (m - d) =
    (ascPochhammer ℝ N).eval (2 * m) *
      ((Real.Gamma (m + d) * Real.Gamma (m - d) / Real.Gamma (2 * m))⁻¹ *
        (∫ t in (0 : ℝ)..1, w t * polynomial c N t (1 - t)))
  rw [hsum, gamma_pochhammer hm]
  have hgp := (Real.Gamma_pos_of_pos hp).ne'
  have hgq := (Real.Gamma_pos_of_pos hq).ne'
  have hgm := (Real.Gamma_pos_of_pos hm).ne'
  have hpm := (ascPochhammer_pos N (2 * m) hm).ne'
  simp only [mul_comm 2 m] at hgm hpm
  unfold lift
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp

/- proof_shape: bind-only; escape_witness: none;
consumer: betaMean_antiOn. -/
private lemma betaMean_perturb {W : ℝ → ℝ}
    (hW : ContinuousOn W (Icc 0 1)) {m d : ℝ}
    (hp : 0 < m + d) (hq : 0 < m - d) (e : ℝ) :
    betaMean (fun t => W t + e * (t * (1 - t))) m d =
      betaMean W m d + e * betaMean (fun t => t * (1 - t)) m d := by
  have hi := intervalIntegrable_beta hp hq
  have hWi := hi.mul_continuousOn (by simpa only [uIcc_of_le zero_le_one] using hW)
  have hBi : IntervalIntegrable
      (fun t : ℝ => (t ^ (m + d - 1) * (1 - t) ^ (m - d - 1)) *
        (e * (t * (1 - t)))) volume 0 1 :=
    hi.mul_continuousOn (by fun_prop)
  unfold betaMean
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add hWi hBi]
  have heq : (fun t : ℝ => t ^ (m + d - 1) * (1 - t) ^ (m - d - 1) *
      (e * (t * (1 - t)))) =
      (fun t => e * (t ^ (m + d - 1) * (1 - t) ^ (m - d - 1) *
        (t * (1 - t)))) := by funext t; ring
  rw [heq, intervalIntegral.integral_const_mul]
  ring

/- proof_shape: content; escape_witness: betaMean_antiOn (a strictly increasing
quadratic perturbation and its zero-perturbation limit extend strict comparison
to every nondecreasing symmetric continuous integrand);
consumer: lift_monotoneOn. -/
/-- The symmetric beta mean is nonincreasing with shape imbalance for every
continuous integrand nondecreasing toward the midpoint. -/
theorem betaMean_antiOn {W : ℝ → ℝ}
    (hW : ContinuousOn W (Icc 0 1))
    (hsymm : ∀ t ∈ Icc 0 1, W (1 - t) = W t)
    (hmono : MonotoneOn W (Ioc 0 (1 / 2))) {m : ℝ} (hm : 0 < m) :
    AntitoneOn (betaMean W m) (Ico 0 m) := by
  intro d hd e he hde
  rcases hde.eq_or_lt with rfl | hde
  · exact le_rfl
  have hperturb (a : ℝ) (ha : 0 < a) :
      betaMean W m e + a * betaMean (fun t => t * (1 - t)) m e ≤
        betaMean W m d + a * betaMean (fun t => t * (1 - t)) m d := by
    have hc : ContinuousOn (fun t => W t + a * (t * (1 - t))) (Icc 0 1) :=
      hW.add (by fun_prop)
    have hs : ∀ t ∈ Icc 0 1,
        W (1 - t) + a * ((1 - t) * (1 - (1 - t))) = W t + a * (t * (1 - t)) := by
      intro t ht
      rw [hsymm t ht]
      ring
    have hstrict : StrictMonoOn (fun t => W t + a * (t * (1 - t))) (Ioc 0 (1 / 2)) := by
      intro x hx y hy hxy
      have hWxy := hmono hx hy hxy.le
      have hquad : x * (1 - x) < y * (1 - y) := by
        have hpos : 0 < (y - x) * (1 - x - y) :=
          mul_pos (sub_pos.mpr hxy) (by linarith [hx.2, hy.2])
        nlinarith
      have := mul_lt_mul_of_pos_left hquad ha
      linarith
    have H := (betaMean_strictAntiOn hc hs hstrict hm hd he hde).le
    rw [betaMean_perturb hW (by linarith [he.1]) (by linarith [he.2]),
      betaMean_perturb hW (by linarith [hd.1]) (by linarith [hd.2])] at H
    exact H
  have hlimit (b : ℝ) : Filter.Tendsto
      (fun a : ℝ => betaMean W m b + a * betaMean (fun t => t * (1 - t)) m b)
      (𝓝[>] 0) (𝓝 (betaMean W m b)) := by
    have H : ContinuousAt
        (fun a : ℝ => betaMean W m b + a * betaMean (fun t => t * (1 - t)) m b) 0 :=
      by fun_prop
    simpa only [zero_mul, add_zero] using H.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  exact le_of_tendsto_of_tendsto (hlimit e) (hlimit d)
    (Filter.mem_of_superset self_mem_nhdsWithin fun a ha => hperturb a ha)

/- proof_shape: content; escape_witness: betaMean_antiOn;
consumer: Result.Z_monotoneOn. -/
/-- Beta lifting preserves balancing monotonicity, including both closed
endpoints and the degenerate zero-total slice. -/
theorem lift_monotoneOn (c : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k ≤ N, c (N - k) = c k)
    (hmono : MonotoneOn (fun t => polynomial c N t (1 - t)) (Ioc 0 (1 / 2)))
    {S : ℝ} (hS : 0 ≤ S) :
    MonotoneOn (fun s => lift c N s (S - s)) (Icc 0 (S / 2)) := by
  have hWsymm : ∀ t ∈ Icc (0 : ℝ) 1,
      polynomial c N (1 - t) (1 - (1 - t)) = polynomial c N t (1 - t) := by
    intro t ht
    simpa only [sub_sub_cancel] using polynomial_symm c N hc (1 - t) t
  have hanti := betaMean_antiOn (polynomial_continuous c N).continuousOn hWsymm hmono
    (m := S / 2)
  have hinterior : MonotoneOn (fun s => lift c N s (S - s)) (Ioc 0 (S / 2)) := by
    intro x hx y hy hxy
    have hm : 0 < S / 2 := hx.1.trans_le hx.2
    have hdx : S / 2 - x ∈ Ico 0 (S / 2) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hdy : S / 2 - y ∈ Ico 0 (S / 2) := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have H := hanti hm hdy hdx (by linarith : S / 2 - y ≤ S / 2 - x)
    have heq (z : ℝ) (hz : 0 < z) (hzS : z ≤ S / 2) :
        lift c N z (S - z) =
          (ascPochhammer ℝ N).eval S *
            betaMean (fun t => polynomial c N t (1 - t)) (S / 2) (S / 2 - z) := by
      have h := lift_eq_betaMean c N (m := S / 2) (d := S / 2 - z)
        (by linarith) (by linarith)
      rw [show S / 2 + (S / 2 - z) = S - z by ring,
        show S / 2 - (S / 2 - z) = z by ring,
        show 2 * (S / 2) = S by ring] at h
      exact (lift_symm c N hc z (S - z)).trans h
    change lift c N x (S - x) ≤ lift c N y (S - y)
    rw [heq x hx.1 hx.2, heq y hy.1 hy.2]
    exact mul_le_mul_of_nonneg_left H (ascPochhammer_pos N S (by linarith)).le
  rcases hS.eq_or_lt with rfl | hS
  · intro x hx y hy hxy
    have hx0 : x = 0 := by linarith [hx.1, hx.2]
    have hy0 : y = 0 := by linarith [hy.1, hy.2]
    simp only [hx0, hy0, le_refl]
  · intro x hx y hy hxy
    rcases hx.1.eq_or_lt with rfl | hx0
    · rcases hy.1.eq_or_lt with rfl | hy0
      · exact le_rfl
      · have hlim : Filter.Tendsto (fun s : ℝ => lift c N s (S - s))
            (𝓝[>] 0) (𝓝 (lift c N 0 (S - 0))) :=
          (lift_continuous c N S).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        apply le_of_tendsto hlim
        filter_upwards [Ioo_mem_nhdsGT hy0] with z hz
        exact hinterior ⟨hz.1, hz.2.le.trans hy.2⟩ ⟨hy0, hy.2⟩ hz.2.le
    · exact hinterior ⟨hx0, hx.2⟩ ⟨hx0.trans_le hxy, hy.2⟩ hxy

end D5.S3.Analytic.KarpZhangNinh.Beta
