/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionBoundary
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Admissible strict multiple-zeta convergence and the actual normalized radial limit. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionDisk
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionBoundary

open CompositionDisk

/-- The full strict positive tuple has largest entry n+1 and all remaining entries below it. -/
def Indices (tail : List ℕ+) := (n : ℕ) × StrictIndices tail.length n

/-- The largest index carries the head exponent, in the source's order. -/
def weight (head : ℕ+) (tail : List ℕ+) (i : Indices tail) : ℝ :=
  strictWeight tail i.1 i.2 / ((i.1 + 1 : ℕ) : ℝ) ^ (head : ℕ)

/-- The independently indexed strict multiple-zeta sum. -/
def zeta (head : ℕ+) (tail : List ℕ+) : ℝ := ∑' i : Indices tail, weight head tail i

set_option maxHeartbeats 800000 in
/-- Admissible compositions have a finite, positive strict MZV total, equal to both
the normalized coefficient sum and its radial boundary value. The nested harmonic
estimate is proved here; no boundary convergence premise is assumed. -/
theorem result (head : ℕ+) (tail : List ℕ+) (hh : 1 < (head : ℕ)) :
    Summable (coefficient head tail) ∧
    Summable (weight head tail) ∧
    (∑' n, coefficient head tail n) = zeta head tail ∧
    0 < zeta head tail ∧
    (∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
      normalized head tail z = source (head :: tail) z / z ^ depth tail) ∧
    Tendsto (fun r : ℝ => normalized head tail (r : ℂ)) (𝓝[<] 1)
      (𝓝 (zeta head tail : ℂ)) := by
  have hhar : ∀ N, (harmonic N : ℝ) = ∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℝ)⁻¹ := by
    intro N
    simp [harmonic]
  have hnonneg : ∀ N, 0 ≤ (harmonic N : ℝ) := by
    intro N
    rw [hhar]
    positivity
  have hmono : Monotone (fun N => (harmonic N : ℝ)) := by
    intro m n hmn
    dsimp only
    rw [hhar, hhar]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
      (fun _ _ _ => by positivity)
  have hH : ∀ (ks : List ℕ+) (N : ℕ), H ks N ≤ (harmonic N : ℝ) ^ ks.length := by
    intro ks
    induction ks with
    | nil => intro N; simp [H]
    | cons k ks ih =>
      intro N
      calc
        H (k :: ks) N ≤ ∑ m ∈ Finset.range N,
            (harmonic N : ℝ) ^ ks.length * ((m + 1 : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro m hm
          have hmN := (Finset.mem_range.mp hm).le
          have hd : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (k : ℕ) := by
            simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)) k.pos
          calc
            H ks m / ((m + 1 : ℕ) : ℝ) ^ (k : ℕ) ≤
                (harmonic N : ℝ) ^ ks.length / ((m + 1 : ℕ) : ℝ) := by
              exact div_le_div₀ (pow_nonneg (hnonneg N) _)
                ((ih m).trans (pow_le_pow_left₀ (hnonneg m) (hmono hmN) _))
                (by positivity) hd
            _ = _ := div_eq_mul_inv _ _
        _ = (harmonic N : ℝ) ^ (k :: ks).length := by
          rw [← Finset.mul_sum, ← hhar]
          simp [pow_succ]
  let b : ℕ → ℝ := fun n => H tail n / ((n + 1 : ℕ) : ℝ) ^ (head : ℕ)
  have hb0 : ∀ n, 0 ≤ b n := fun n =>
    div_nonneg (source_coefficient_control tail n).1 (by positivity)
  have hlog : ∀ᶠ x : ℝ in atTop,
      (1 + Real.log x) ^ tail.length ≤ 2 ^ tail.length * x ^ (1 / 2 : ℝ) := by
    have he := (isLittleO_log_rpow_rpow_atTop (tail.length : ℝ)
      (show (0 : ℝ) < 1 / 2 by norm_num)).def (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [he, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (0 : ℝ)] with x hx hl hx0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg hx0 _), Real.rpow_natCast] at hx
    calc
      (1 + Real.log x) ^ tail.length ≤ (2 * Real.log x) ^ tail.length := by
        gcongr
        linarith
      _ = 2 ^ tail.length * Real.log x ^ tail.length := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  have hsmajor : Summable (fun n : ℕ => 2 ^ tail.length *
      ((n + 1 : ℕ) : ℝ) ^ (- (3 / 2 : ℝ))) := by
    exact ((summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show -(3 / 2 : ℝ) < -1 by norm_num))).mul_left _
  have hbs : Summable b := by
    apply hsmajor.of_norm_bounded_eventually_nat
    have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    filter_upwards [hn.eventually hlog] with n hnlog
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 n)]
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hnum : H tail n ≤ 2 ^ tail.length * ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
      apply (hH tail n).trans
      apply (pow_le_pow_left₀ (hnonneg n) (hmono (Nat.le_succ n)) _).trans
      exact (pow_le_pow_left₀ (hnonneg (n + 1)) (harmonic_le_one_add_log (n + 1)) _).trans hnlog
    have hden : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ (head : ℕ) :=
      pow_le_pow_right₀ hn1 hh
    calc
      b n ≤ (2 ^ tail.length * ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) /
          ((n + 1 : ℕ) : ℝ) ^ 2 :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 2 ^ tail.length * ((n + 1 : ℕ) : ℝ) ^ (- (3 / 2 : ℝ)) := by
        rw [mul_div_assoc, ← Real.rpow_natCast (((n + 1 : ℕ) : ℝ)) 2,
          ← Real.rpow_sub hn0]
        norm_num
  have hc : Summable (coefficient head tail) := by
    apply ((summable_nat_add_iff tail.length).mpr hbs).congr
    intro n
    simp [b, coefficient, depth, add_assoc]
  have hfinite : ∀ (ks : List ℕ+) (N : ℕ),
      H ks N = ∑ i : StrictIndices ks.length N, strictWeight ks N i := by
    intro ks
    induction ks with
    | nil =>
      intro N
      change (1 : ℝ) = ∑ _i : PUnit, (1 : ℝ)
      simp
    | cons k ks ih =>
      intro N
      change (∑ m ∈ Finset.range N, H ks m / ((m + 1 : ℕ) : ℝ) ^ (k : ℕ)) =
        ∑ p : (m : Fin N) × StrictIndices ks.length m.val,
          strictWeight ks p.1.val p.2 / ((p.1.val + 1 : ℕ) : ℝ) ^ (k : ℕ)
      rw [Fintype.sum_sigma]
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul, ← ih]
      exact (Fin.sum_univ_eq_sum_range _ N).symm
  have hw0 : ∀ (ks : List ℕ+) (N : ℕ) (i : StrictIndices ks.length N),
      0 ≤ strictWeight ks N i := by
    intro ks
    induction ks with
    | nil => intros; exact zero_le_one
    | cons k ks ih =>
      intro N i
      exact div_nonneg (ih i.1.val i.2) (by positivity)
  have hgroup : ∀ n, (∑' i : StrictIndices tail.length n,
      weight head tail ⟨n, i⟩) = b n := by
    intro n
    simp only [tsum_fintype, weight, b, ← Finset.sum_div, ← hfinite]
  have hw : Summable (weight head tail) := by
    apply (summable_sigma_of_nonneg (f := weight head tail) (fun i =>
      div_nonneg (hw0 tail i.1 i.2) (by positivity))).mpr
    refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
    simpa only [hgroup] using hbs
  have hz : zeta head tail = ∑' n, b n := by
    exact hw.tsum_sigma.trans (tsum_congr hgroup)
  have hprefix : ∑ n ∈ Finset.range tail.length, b n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [b, (source_coefficient_control tail n).2.2.1 (Finset.mem_range.mp hn)]
  have htotal : (∑' n, coefficient head tail n) = zeta head tail := by
    rw [hz]
    have heq := hbs.sum_add_tsum_nat_add tail.length
    rw [hprefix, zero_add] at heq
    rw [← heq]
    apply tsum_congr
    intro n
    simp [b, coefficient, depth, add_assoc]
  have hpos : 0 < zeta head tail := by
    rw [← htotal]
    exact hc.tsum_pos (fun n => ((source_series head tail).1 n).le) 0
      ((source_series head tail).1 0)
  have hsource : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
      normalized head tail z = source (head :: tail) z / z ^ depth tail := by
    intro z hz hn
    apply (eq_div_iff (pow_ne_zero _ hn)).mpr
    rw [mul_comm]
    exact (source_series head tail).2.2.2.2.1 z hz
  refine ⟨hc, hw, htotal, hpos, hsource, ?_⟩
  have hlimit : Tendsto (fun r : ℝ => ∑' n, (coefficient head tail n : ℂ) * (r : ℂ) ^ n)
      (𝓝[<] 1) (𝓝 (∑' n, (coefficient head tail n : ℂ))) := by
    apply tendsto_tsum_of_dominated_convergence hc
    · intro n
      have hcont : Continuous (fun r : ℝ =>
          (coefficient head tail n : ℂ) * (r : ℂ) ^ n) := by fun_prop
      simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    · have hi : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
        (nhdsLT_basis 1).mem_of_mem (show (0 : ℝ) < 1 by norm_num)
      filter_upwards [hi] with r hr
      intro n
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ((source_series head tail).1 n), Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr.1]
      exact mul_le_of_le_one_right ((source_series head tail).1 n).le
        (pow_le_one₀ hr.1.le hr.2.le)
  simpa only [normalized, ← Complex.ofReal_tsum, htotal] using hlimit

#print axioms result

end D5.S3.AnalyticClosure.Polylogarithm.CompositionBoundary
