/- GID: D5/S3/Analytic/KarpZhangNinh/Beta
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangNinh/Beta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Algebra.Polynomial]
   utility: none
   digest: Trisection balancing and symmetric homogeneous beta lifting. -/

import D5.S3.Analytic.IncompleteBeta.Comparison
import Mathlib.Topology.Algebra.Polynomial

/-!
The beta moment transform replaces the two monomial factors by rising
factorials. The coefficient signs are unrestricted. The comparison of beta
means supplies the ordering for positive shape parameters; continuity of the
lifted polynomial supplies the closed boundary.
admission_basis: escape-witness; witness: betaMean_antiOn.
The homogeneous trisection identities and inequalities are consumed bind-only
helpers: the cubic root-of-unity filter, binomial theorem, marked moments,
Bernoulli bounds and derivative criterion give a normalization bypass.
utility none: all statements concern arbitrary coefficient families and degrees,
without finite enumeration, numerical certificates or numerical reduction.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators Topology

namespace D5.S3.Analytic.KarpZhangNinh.Beta

open Set MeasureTheory

open D5.S3.Analytic.KummerRatio.BetaIntegral
open D5.S3.Analytic.IncompleteBeta.Comparison

/-- A homogeneous polynomial written in its degree-`N` monomial basis. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_eq_betaMean; D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn; D5.S3.Analytic.KarpZhangNinh.Beta.polynomial_continuous; D5.S3.Analytic.KarpZhangNinh.Beta.polynomial_symm; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def polynomial (c : ℕ → ℝ) (N : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), c k * x ^ k * y ^ (N - k)

/-- The rising-factorial lift of a homogeneous polynomial. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_continuous; D5.S3.Analytic.KarpZhangNinh.Beta.lift_eq_betaMean; D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn; D5.S3.Analytic.KarpZhangNinh.Beta.lift_symm; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.lift_normalization;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def lift (c : ℕ → ℝ) (N : ℕ) (u v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    c k * (ascPochhammer ℝ k).eval u * (ascPochhammer ℝ (N - k)).eval v

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem polynomial_continuous (c : ℕ → ℝ) (N : ℕ) :
    Continuous (fun t : ℝ => polynomial c N t (1 - t)) := by
  unfold polynomial
  fun_prop

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem lift_continuous (c : ℕ → ℝ) (N : ℕ) (S : ℝ) :
    Continuous (fun s : ℝ => lift c N s (S - s)) := by
  unfold lift
  fun_prop

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
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
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
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
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_eq_betaMean;
direct_frozen_dependencies: D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45;
stacked_dependencies: none. -/
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
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986;
stacked_dependencies: none. -/
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
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.betaMean_antiOn;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986;
stacked_dependencies: none. -/
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

/-- The symmetric beta mean is nonincreasing with shape imbalance for every
continuous integrand nondecreasing toward the midpoint. -/
/- proof_shape: content; escape_witness: betaMean_antiOn (a strictly increasing quadratic perturbation and its zero-perturbation limit extend strict comparison to every nondecreasing symmetric continuous integrand);
consumers: D5.S3.Analytic.KarpZhangNinh.Beta.lift_monotoneOn;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn) statement_id=sha256:8e5cc3dcb0b903667c4ed8ac30429217f113e1e1e09d26451dfd2b0252bacacc; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986;
stacked_dependencies: none. -/
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

/-- Beta lifting preserves balancing monotonicity, including both closed
endpoints and the degenerate zero-total slice. -/
/- proof_shape: content; escape_witness: betaMean_antiOn;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn) statement_id=sha256:8e5cc3dcb0b903667c4ed8ac30429217f113e1e1e09d26451dfd2b0252bacacc; D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986;
stacked_dependencies: none. -/
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

noncomputable section
set_option maxHeartbeats 400000
open Finset
namespace D5.S3.Analytic.KarpZhangNinh.Homogeneous

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.residue_filter; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.residue_succ; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.weighted_succ;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def residue (n r : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (n.choose k : ℤ) * if k % 3 = r then 1 else 0

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.residue_filter;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma residue_succ (n r : ℕ) (hr : r < 3) :
    residue (n+1) r = residue n r + residue n ((r+2)%3) := by
  unfold residue
  rw [show n + 1 + 1 = n + 2 by omega,
    Finset.sum_choose_succ_mul (fun k _ => if k % 3 = r then (1:ℤ) else 0) n]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hm : (k+1)%3=r ↔ k%3=(r+2)%3 := by omega
  simp only [hm]

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.residue_filter;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def periodic (q : ℕ) : ℤ :=
  match q % 6 with
  | 0 => 2
  | 1 => 1
  | 2 => -1
  | 3 => -2
  | 4 => -1
  | _ => 1

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem residue_filter (n : ℕ) :
    (3 * residue n 0 = 2^n + periodic n) ∧
    (3 * residue n 1 = 2^n + periodic (n+4)) ∧
    (3 * residue n 2 = 2^n + periodic (n+2)) := by
  induction n with
  | zero => norm_num [residue, periodic]
  | succ n ih =>
    rw [residue_succ n 0 (by omega), residue_succ n 1 (by omega),
      residue_succ n 2 (by omega)]
    norm_num only [Nat.reduceAdd, Nat.reduceMod]
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases h : n % 6 <;>
      simp only [periodic, Nat.add_mod, Nat.mod_mod, h] at * <;>
      norm_num at * <;> simp only [pow_succ] <;> omega

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A; D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_nonneg; D5.S3.Analytic.KarpZhangNinh.Homogeneous.B; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.K_pos; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_coeff; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.moment_sum; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.second_succ; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.shear; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.weighted_succ;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def weighted (n r : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (n.choose k : ℤ) * k * if k % 3 = r then 1 else 0

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma weighted_succ (n r : ℕ) (hr : r < 3) :
    weighted (n+1) r = (n+1) * residue n ((r+2)%3) := by
  unfold weighted residue
  rw [show n + 1 + 1 = (n+1)+1 by omega, sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hc : ((n+1).choose (k+1) : ℤ) * (k+1) =
      (n+1) * (n.choose k : ℤ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hc]
  have hm : (k+1)%3=r ↔ k%3=(r+2)%3 := by omega
  simp only [hm]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.B; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.K_pos; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_coeff; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.moment_sum; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.second_succ; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.shear;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def second (n r : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (n.choose k : ℤ) * k * ((k:ℤ)-1) *
    if k % 3 = r then 1 else 0

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma second_succ (n r : ℕ) (hr : r < 3) :
    second (n+1) r = (n+1) * weighted n ((r+2)%3) := by
  unfold second weighted
  rw [sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hc : ((n+1).choose (k+1) : ℤ) * (k+1) =
      (n+1) * (n.choose k : ℤ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hc]
  have hm : (k+1)%3=r ↔ k%3=(r+2)%3 := by omega
  simp only [hm]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_nonneg; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.K_pos; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_coeff;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def A (n : ℕ) : ℤ := weighted n 0 - 2 * weighted (n-1) 0

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.D; D5.S3.Analytic.KarpZhangNinh.Homogeneous.K; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg; D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_expansion; D5.S3.Analytic.KarpZhangNinh.Homogeneous.hasDerivAt_slice; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.K_pos; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_coeff;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def T (n N : ℕ) : ℤ :=
  ((N:ℤ)-1) * A n - (second n 0 - 2 * second (n-1) 0)

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_nonneg; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def alpha (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => -3*n+4
  | 1 => -3*n+2
  | 2 => -2
  | 3 => 3*n-4
  | 4 => 3*n-2
  | _ => 2

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def beta (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => -3*n+4
  | 1 => -4
  | 2 => 3*n-8
  | 3 => 3*n-4
  | 4 => 4
  | _ => -3*n+8

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_nonneg; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_formula; D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem A_formula (n : ℕ) (hn : 1 ≤ n) :
    3 * A n = 2^(n-1) + alpha n := by
  rcases n with _|_|n
  · omega
  · norm_num [A, weighted, alpha, sum_range_succ]
  · simp only [A, Nat.add_one_sub_one, weighted_succ _ 0 (by omega)]
    have h₁ := (residue_filter (n+1)).2.2
    have h₂ := (residue_filter n).2.2
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases h : n % 6 <;>
      simp [alpha, periodic, Nat.add_mod, h, pow_succ] at * <;>
      linear_combination ((n:ℤ)+2)*h₁ - 2*((n:ℤ)+1)*h₂

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem T_formula (n N : ℕ) (hn : 1 ≤ n) :
    3 * T n N = ((N:ℤ)-n)*2^(n-1) + ((N:ℤ)-1)*alpha n -
      ((n:ℤ)-1)*beta n := by
  rw [T, mul_sub, mul_left_comm 3, A_formula n hn]
  suffices h : 3 * (second n 0 - 2 * second (n-1) 0) =
      ((n:ℤ)-1)*(2^(n-1)+beta n) by rw [h]; ring
  rcases n with _|_|_|n
  · omega
  · norm_num [second, beta, sum_range_succ]
  · norm_num [second, beta, sum_range_succ]
  · simp only [Nat.add_one_sub_one, second_succ _ 0 (by omega),
      weighted_succ _ 2 (by omega)]
    norm_num only [Nat.reduceAdd, Nat.reduceMod]
    have h₁ := (residue_filter (n+1)).2.1
    have h₂ := (residue_filter n).2.1
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases h : n % 6 <;>
      simp [beta, periodic, Nat.add_mod, h, pow_succ] at * <;>
      linear_combination ((n:ℤ)+3)*((n:ℤ)+2)*h₁ -
        2*((n:ℤ)+2)*((n:ℤ)+1)*h₂

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.A_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma power_linear (n : ℕ) (hn : 5 ≤ n) : (3:ℤ)*n-2 ≤ 2^(n-1) := by
  have hb : (1 : ℤ) + (n - 5 : ℕ) ≤ (2 : ℤ) ^ (n - 5) := by
    simpa using (one_add_mul_le_pow (a := (1 : ℤ)) (by norm_num) (n - 5))
  have hp : (2 : ℤ) ^ (n - 1) = 16 * (2 : ℤ) ^ (n - 5) := by
    calc
      _ = (2 : ℤ) ^ ((n - 5) + 4) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hc : (n : ℤ) = (n - 5 : ℕ) + 5 := by
    exact_mod_cast (show n = (n - 5) + 5 by omega)
  rw [hp, hc]
  nlinarith [(show (0 : ℤ) ≤ (n - 5 : ℕ) by positivity)]

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.power_quadratic_two;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma power_quadratic_one (n : ℕ) (hn : 7 ≤ n) :
    (3:ℤ)*n^2-3*n+2 ≤ 2^n := by
  have hbase (q : ℕ) :
      (3 : ℤ) * q ^ 2 + 39 * q + 128 ≤ 128 * 2 ^ q := by
    have hBernHalf : (1 : ℤ) + (q / 2 : ℕ) ≤ (2 : ℤ) ^ (q / 2) := by
      simpa using (one_add_mul_le_pow (a := (1 : ℤ)) (by norm_num) (q / 2))
    have hsq : ((1 : ℤ) + (q / 2 : ℕ)) ^ 2 ≤ ((2 : ℤ) ^ (q / 2)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hBernHalf
    have hp : (2 : ℤ) ^ q =
        ((2 : ℤ) ^ (q / 2)) ^ 2 * (2 : ℤ) ^ (q % 2) := by
      calc
        _ = (2 : ℤ) ^ (q / 2 * 2 + q % 2) := by congr 1; omega
        _ = _ := by rw [pow_add, pow_mul]
    have ht : q % 2 = 0 ∨ q % 2 = 1 := Nat.mod_two_eq_zero_or_one q
    rcases ht with ht | ht
    · rw [hp, ht, pow_zero, mul_one]
      have hc : (q : ℤ) = 2 * (q / 2 : ℕ) := by
        exact_mod_cast (show q = 2 * (q / 2) by omega)
      rw [hc]
      nlinarith [sq_nonneg ((q / 2 : ℕ) : ℤ), (show (0 : ℤ) ≤ (q / 2 : ℕ) by positivity)]
    · rw [hp, ht, pow_one]
      have hc : (q : ℤ) = 2 * (q / 2 : ℕ) + 1 := by
        exact_mod_cast (show q = 2 * (q / 2) + 1 by omega)
      rw [hc]
      nlinarith [sq_nonneg ((q / 2 : ℕ) : ℤ), (show (0 : ℤ) ≤ (q / 2 : ℕ) by positivity)]
  have hp : (2 : ℤ) ^ n = 128 * (2 : ℤ) ^ (n - 7) := by
    calc
      _ = (2 : ℤ) ^ ((n - 7) + 7) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hc : (n : ℤ) = (n - 7 : ℕ) + 7 := by
    exact_mod_cast (show n = (n - 7) + 7 by omega)
  have hb := hbase (n - 7)
  rw [hp, hc]
  nlinarith

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma power_quadratic_two (n : ℕ) (hn : 8 ≤ n) :
    (3:ℤ)*n^2-9*n+8 ≤ 2^(n-1) := by
  have h := power_quadratic_one (n - 1) (Nat.sub_le_sub_right hn 1)
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 :=
    Nat.cast_sub (le_trans (Nat.le_add_right 1 7) hn)
  rw [hcast] at h
  nlinarith

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem A_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ A n := by
  have hf := A_formula n hn
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [A, weighted, sum_range_succ] at *
  · have hpow := power_linear n (by omega)
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    have hl : -3*(n:ℤ)+2 ≤ alpha n := by
      interval_cases h : n % 6 <;> simp [alpha, h] <;> omega
    omega

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.K_pos;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem T_nonneg (n N : ℕ) (hn : 1 ≤ n) (hN : N % 3 = 0) (hnN : n < N) :
    0 ≤ T n N := by
  have hf := T_formula n N hn
  have ha : 0 ≤ 2^(n-1) + alpha n := by
    rw [← A_formula n hn]
    exact mul_nonneg (by norm_num) (A_nonneg n hn)
  have ha0 := ha
  have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
  have hn' : (1:ℤ) ≤ n := by exact Int.toNat_le.mp hn
  have hgap : (1:ℤ) ≤ (N:ℤ)-n := by omega
  interval_cases h : n % 6 <;> simp only [alpha, h] at ha0
  · simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]
  · by_cases he : n=1
    · subst n; norm_num [alpha, beta] at hf; omega
    · have h7 : 7 ≤ n := by omega
      have hpow := power_quadratic_one n h7
      have hg : (2:ℤ) ≤ (N:ℤ)-n := by omega
      have hepow : (2:ℤ)^n=2*2^(n-1) :=
        (mul_pow_sub_one (by omega : n ≠ 0) (2:ℤ)).symm
      simp [alpha, beta, h] at hf ha
      rw [hepow] at hpow
      nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n-2) ha0]
  · by_cases he : n=2
    · subst n; norm_num [alpha, beta] at hf; omega
    · have h8 : 8 ≤ n := by omega
      have hpow := power_quadratic_two n h8
      simp [alpha, beta, h] at hf ha
      nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n-1) ha0]
  · simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]
  · have hn4 : (4:ℤ) ≤ n := by omega
    simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]
  · have hn5 : (5:ℤ) ≤ n := by omega
    simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.P; D5.S3.Analytic.KarpZhangNinh.Homogeneous.coeff_symm; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.shear; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.lift_normalization; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.normalization_term;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def coeff (N k : ℕ) : ℝ :=
  if k % 3 = 0 then (k:ℝ) * (N-k) * N.choose k else 0

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.hasDerivAt_slice; D5.S3.Analytic.KarpZhangNinh.Homogeneous.strictMonoOn_slice; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.shear; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def P (N : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ range (N+1), coeff N k * x^k * y^(N-k)

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem coeff_symm (N k : ℕ) (hN : N % 3 = 0) (hk : k ≤ N) :
    coeff N (N-k) = coeff N k := by
  have hm : (N-k)%3=0 ↔ k%3=0 := by omega
  simp only [coeff, Nat.choose_symm hk, hm]
  rw [Nat.cast_sub hk]
  split_ifs <;> ring

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.hasDerivAt_slice; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.collect_derivative; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_coeff; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.shear;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def B (N t : ℕ) : ℝ :=
  (N.choose t : ℝ) * ((((N:ℤ)-1)*weighted (N-t) 0-second (N-t) 0 : ℤ):ℝ)

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.shear;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma choose_exchange (N k t : ℕ) (hk : k ≤ N) (ht : t ≤ N-k) :
    (N.choose k : ℝ) * (N-k).choose t =
      (N.choose t : ℝ) * (N-t).choose k := by
  have h := Nat.choose_mul (n:=N) (k:=N-k) (s:=t) ht
  rw [Nat.choose_symm hk] at h
  have he : N-k-t=N-t-k := by exact Nat.sub_right_comm N k t
  rw [he, Nat.choose_symm (by omega : k ≤ N-t)] at h
  exact_mod_cast h

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.shear;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma moment_sum (N n : ℕ) (hn : n ≤ N) :
    (∑ k ∈ range (n+1),
      (if k%3=0 then (k:ℝ)*(N-k) else 0)*(n.choose k : ℝ)) =
    ((((N:ℤ)-1)*weighted n 0-second n 0 : ℤ):ℝ) := by
  simp only [weighted, second, Int.cast_sub, Int.cast_mul, Int.cast_sum,
    Int.cast_ofNat, Int.cast_natCast, Int.cast_one, mul_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  have hkN : k ≤ N := (Nat.le_of_lt_succ (mem_range.mp hk)).trans hn
  split_ifs <;> simp <;> ring

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.hasDerivAt_slice;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private theorem shear (N : ℕ) (x d : ℝ) :
    P N x (x+d) = ∑ t ∈ range (N+1), B N t*x^(N-t)*d^t := by
  unfold P
  calc
    _ = ∑ k ∈ range (N+1), ∑ t ∈ range (N+1),
        coeff N k * ((N-k).choose t : ℝ) * x^(N-t)*d^t := by
      apply sum_congr rfl
      intro k hk
      have hkN : k ≤ N := Nat.le_of_lt_succ (mem_range.mp hk)
      rw [add_comm x d, add_pow, mul_sum]
      calc
        _ = ∑ t ∈ range (N-k+1),
            coeff N k*((N-k).choose t : ℝ)*x^(N-t)*d^t := by
          apply sum_congr rfl
          intro t ht
          have htN : t ≤ N-k := Nat.le_of_lt_succ (mem_range.mp ht)
          have he : k+(N-k-t)=N-t := by omega
          rw [show coeff N k * x^k *
              (d^t*x^(N-k-t)*((N-k).choose t:ℝ)) =
              coeff N k*((N-k).choose t:ℝ)*(x^k*x^(N-k-t))*d^t by ring,
            ← pow_add, he]
        _ = _ := by
          apply sum_subset (range_mono (by omega))
          intro t ht hnot
          have ht' : N-k < t := by simp only [mem_range] at hnot; omega
          rw [Nat.choose_eq_zero_of_lt ht', Nat.cast_zero]
          ring
    _ = ∑ t ∈ range (N+1), ∑ k ∈ range (N+1),
        coeff N k*((N-k).choose t:ℝ)*x^(N-t)*d^t := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t ht
      have htN : t ≤ N := Nat.le_of_lt_succ (mem_range.mp ht)
      rw [← sum_mul, ← sum_mul]
      congr 2
      calc
        _ = ∑ k ∈ range (N-t+1), coeff N k*((N-k).choose t:ℝ) := by
          symm
          apply sum_subset (range_mono (by omega))
          intro k hk hnot
          have hk' : N-t < k := by simp only [mem_range] at hnot; omega
          have hkN : k ≤ N := Nat.le_of_lt_succ (mem_range.mp hk)
          rw [Nat.choose_eq_zero_of_lt (by omega : N-k < t), Nat.cast_zero, mul_zero]
        _ = (N.choose t:ℝ) * ∑ k ∈ range (N-t+1),
            (if k%3=0 then (k:ℝ)*(N-k) else 0)*((N-t).choose k:ℝ) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro k hk
          have hkN : k ≤ N := by simp only [mem_range] at hk; omega
          have htk : t ≤ N-k := by simp only [mem_range] at hk; omega
          unfold coeff
          have he := choose_exchange N k t hkN htk
          split_ifs
          · linear_combination (k:ℝ)*((N:ℝ)-k)*he
          · simp
        _ = B N t := by rw [moment_sum N (N-t) (by omega)]; rfl

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.hasDerivAt_slice;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma derivative_coeff (N t : ℕ) (ht : t < N) :
    (N-t:ℕ)*B N t - 2*(t+1:ℕ)*B N (t+1) =
      (N-t:ℕ)*(N.choose t:ℝ)*(T (N-t) N:ℝ) := by
  have hc : (N.choose (t+1):ℝ)*((t+1:ℕ):ℝ) =
      (N.choose t:ℝ)*((N-t:ℕ):ℝ) := by
    exact_mod_cast (Nat.choose_succ_right_eq N t)
  have he : N-(t+1)=N-t-1 := by exact Nat.sub_add_eq N t 1
  unfold B T A
  rw [he]
  push_cast at hc ⊢
  linear_combination -2 * (((N:ℝ)-1)*(weighted (N-t-1) 0:ℝ)-(second (N-t-1) 0:ℝ)) * hc

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.hasDerivAt_slice;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma collect_derivative (N : ℕ) (x d : ℝ) :
    (∑ t ∈ range (N+1), B N t *
      (((N-t:ℕ):ℝ)*x^(N-t-1)*d^t - 2*(t:ℝ)*x^(N-t)*d^(t-1))) =
    ∑ t ∈ range N, (((N-t:ℕ):ℝ)*B N t - 2*((t+1:ℕ):ℝ)*B N (t+1))*
      x^(N-t-1)*d^t := by
  simp_rw [mul_sub]
  rw [sum_sub_distrib, sum_range_succ, sum_range_succ']
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero,
    Nat.add_one_sub_one]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro t ht
  have he : N-(t+1)=N-t-1 := by exact Nat.sub_add_eq N t 1
  rw [he]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_expansion; D5.S3.Analytic.KarpZhangNinh.Homogeneous.hasDerivAt_slice; D5.S3.Analytic.KarpZhangNinh.Homogeneous.strictMonoOn_slice; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def D (N : ℕ) (x d : ℝ) : ℝ :=
  ∑ t ∈ range N, ((N-t:ℕ):ℝ)*(N.choose t:ℝ)*(T (N-t) N:ℝ)*x^(N-t-1)*d^t

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.strictMonoOn_slice; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.T_diagonal;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem hasDerivAt_slice (N : ℕ) (S x : ℝ) :
    HasDerivAt (fun s => P N s (S-s)) (D N x (S-2*x)) x := by
  have hfun : (fun s => P N s (S-s)) =
      (fun s => ∑ t ∈ range (N+1), B N t*s^(N-t)*(S-2*s)^t) := by
    funext s
    rw [show S-s=s+(S-2*s) by ring, shear]
  rw [hfun]
  have hder := HasDerivAt.fun_sum (u:=range (N+1)) (fun t _ =>
    (((hasDerivAt_id x).pow (N-t)).const_mul (B N t)).mul
      (((hasDerivAt_const x S).sub ((hasDerivAt_id x).const_mul 2)).pow t))
  convert hder using 1
  · funext s
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
  · have hD : D N x (S-2*x) =
        ∑ t ∈ range (N+1), B N t *
          (((N-t:ℕ):ℝ)*x^(N-t-1)*(S-2*x)^t -
            2*(t:ℝ)*x^(N-t)*(S-2*x)^(t-1)) := by
      rw [collect_derivative]
      unfold D
      apply sum_congr rfl
      intro t ht
      rw [derivative_coeff N t (mem_range.mp ht)]
    rw [hD]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq, mul_one, zero_sub]
    apply sum_congr rfl
    intro t ht
    ring

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_expansion;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private lemma T_diagonal (N : ℕ) (hN : N%3=0) : T N N = 0 := by
  by_cases hzero : N=0
  · subst N; norm_num [T, A, weighted, second]
  have hsym (x y : ℝ) : P N x y = P N y x := by
    unfold P
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkN, coeff_symm N k hN hkN]
    ring
  have h : HasDerivAt (fun s => P N s (2-s)) (D N 1 0) 1 := by
    simpa using hasDerivAt_slice N 2 1
  have hout : HasDerivAt (fun s => P N s (2-s)) (D N 1 0) (2-(1:ℝ)) := by
    norm_num
    exact h
  have hr := hout.comp 1 ((hasDerivAt_const (1:ℝ) (2:ℝ)).sub (hasDerivAt_id 1))
  have hr' : HasDerivAt (fun s => P N s (2-s)) (-D N 1 0) 1 := by
    convert hr using 1
    · funext s
      change P N s (2-s) = P N (2-s) (2-(2-s))
      rw [show 2-(2-s)=s by ring, hsym]
    · ring
  have hzD : D N 1 0 = 0 := by
    have hz := h.unique hr'
    linarith
  have hD : D N 1 0 = (N:ℝ)*(T N N:ℝ) := by
    unfold D
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b hb hb0
      simp [hb0]
    · intro h0
      exact False.elim (h0 (by simp only [Finset.mem_range]; omega))
  have hNz : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
  have hzT : (T N N:ℝ) = 0 :=
    (mul_eq_zero.mp (hD.symm.trans hzD)).resolve_left hNz
  exact_mod_cast hzT

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.derivative_expansion; D5.S3.Analytic.KarpZhangNinh.Homogeneous.strictMonoOn_slice; _private.D5.S3.Analytic.KarpZhangNinh.Beta.0.D5.S3.Analytic.KarpZhangNinh.Homogeneous.K_pos;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def K (N : ℕ) (x d : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 (N-1), (n:ℝ)*(N.choose n:ℝ)*(T n N:ℝ)*x^(n-1)*d^(N-n-1)

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.strictMonoOn_slice;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem derivative_expansion (N : ℕ) (hN : N%3=0) (x d : ℝ) :
    D N x d = d*K N x d := by
  unfold D K
  calc
    _ = ∑ t ∈ Icc 1 (N-1),
        ((N-t:ℕ):ℝ)*(N.choose t:ℝ)*(T (N-t) N:ℝ)*x^(N-t-1)*d^t := by
      symm
      apply sum_subset
      · intro t ht; simp only [mem_Icc, mem_range] at *; omega
      · intro t ht hnot
        have hz : t=0 := by simp only [mem_Icc, mem_range] at *; omega
        subst t
        rw [Nat.sub_zero, T_diagonal N hN, Int.cast_zero]
        ring
    _ = ∑ n ∈ Icc 1 (N-1),
        (n:ℝ)*(N.choose n:ℝ)*(T n N:ℝ)*x^(n-1)*d^(N-n) := by
      refine sum_nbij' (fun t => N-t) (fun n => N-n) ?_ ?_ ?_ ?_ ?_
      · intro t ht; simp only [mem_Icc] at *; omega
      · intro n hn; simp only [mem_Icc] at *; omega
      · intro t ht; simp only [mem_Icc] at *; omega
      · intro n hn; simp only [mem_Icc] at *; omega
      · intro t ht
        have htN : t ≤ N := by simp only [mem_Icc] at ht; omega
        rw [Nat.sub_sub_self htN, Nat.choose_symm htN]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [← pow_sub_one_mul (by simp only [mem_Icc] at hn; omega : N-n ≠ 0) d]
      ring

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Homogeneous.strictMonoOn_slice;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private theorem K_pos (N : ℕ) (hN : N%3=0) (h6 : 6 ≤ N) {x d : ℝ}
    (hx : 0 < x) (hd : 0 < d) : 0 < K N x d := by
  apply sum_pos'
  · intro n hn
    have hns := mem_Icc.mp hn
    have hT : (0:ℝ) ≤ (T n N:ℝ) :=
      Int.cast_nonneg (T_nonneg n N hns.1 hN (by omega))
    positivity
  · refine ⟨3, by simp only [mem_Icc]; omega, ?_⟩
    have hT : T 3 N = 3*((N:ℤ)-3) := by norm_num [T, A, weighted, second, sum_range_succ]; ring
    have hTpZ : (0:ℤ) < T 3 N := by rw [hT]; omega
    have hTp : (0:ℝ) < (T 3 N:ℝ) := Int.cast_pos.mpr hTpZ
    have hc : (0:ℝ) < (N.choose 3:ℝ) := by exact_mod_cast Nat.choose_pos (by omega : 3≤N)
    positivity

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
theorem strictMonoOn_slice (m : ℕ) (hm : 2 ≤ m) :
    StrictMonoOn (fun t => P (3*m) t (1-t)) (Set.Ioc 0 (1/2:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (1/2:ℝ))
  · intro x hx
    exact (hasDerivAt_slice (3*m) 1 x).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Ioc, Set.mem_Ioo] at hx
    rw [(hasDerivAt_slice (3*m) 1 x).deriv, derivative_expansion (3*m) (by omega)]
    exact mul_pos (by linarith) (K_pos (3*m) (by omega) (by omega) hx.1 (by linarith))


end D5.S3.Analytic.KarpZhangNinh.Homogeneous
