/- GID: D5/S3/Arith/Robin/PriceRecord/OwnClockUniqueMinimum
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/OwnClockUniqueMinimum
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Genuine boundary KKT and unique minimum of the actual fixed-support Robin interpolation. -/

/- Implementation candidate. Read OwnClockAttainment first: its compact
sublevel argument proves existence without KKT. Here the derivative is
calculated for that SAME phi, the boundary conditions are consequences
of an actual minimum, and the scalar fixed point is CONSTRUCTED by the
preceding IVT/right-derivative argument. No stationarity-sufficiency assumption is used.
No affine convexity is claimed. No numerical instance is used.
Literature status: repo-derived synthesis of the supplied paper argument;
classical mean-value/IVT/extreme-value/Fermat/KKT tools remain Mathlib
providers, not claimed as new mathematical results. -/

import D5.S3.Arith.Robin.PriceRecord.OwnClockAttainment
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.OwnClockUniqueMinimum

open Real Set Finset
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open D5.S3.Arith.Robin.PriceRecord.OwnClockContraction
open D5.S3.Arith.Robin.PriceRecord.OwnClockAttainment
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open D5.S3.Arith.GoldenResource.ContinuousPrimeMaximum

/-- Literal coordinate derivative, including at a_p=1. Differentiation
is ambient (an open neighborhood exists by the strictly positive log
and Euler-factor arguments), while minimization remains constrained. -/
lemma coordinate_hasDerivAt {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) {a : S → ℝ} (ha : a ∈ orthant S) (p : S) :
    HasDerivAt (fun t : ℝ => phi S (extend (Function.update a p t)))
      (log (p : ℝ) * (1 / (clock S (extend a) * log (clock S (extend a))) -
        1 / ((p : ℝ) ^ (a p + 1) - 1))) (a p) := by
  classical
  have hp : (1 : ℝ) < (p : ℕ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p p.property)
  have hc : HasDerivAt (fun t : ℝ => clock S (extend (Function.update a p t)))
      (log (p : ℝ)) (a p) := by
    have hs : HasDerivAt
        (fun t : ℝ => ∑ q : S, Function.update a p t q * log (q : ℝ))
        (∑ q : S, if q = p then log (q : ℝ) else 0) (a p) := by
      apply HasDerivAt.fun_sum
      intro q _
      by_cases hqp : q = p
      · subst q
        simpa using
          (hasDerivAt_id (a p)).mul_const (log (p : ℝ))
      · simpa only [Function.update_of_ne hqp, if_false, hqp] using
          hasDerivAt_const (a p) (a q * log (q : ℝ))
    simpa only [clock_coordinates, sum_ite_eq', Finset.mem_univ, ite_true] using hs
  have hb : HasDerivAt
      (fun t : ℝ => ∑ q : S, benefit q (Function.update a p t q))
      (log (p : ℝ) / ((p : ℝ) ^ (a p + 1) - 1)) (a p) := by
    have hs : HasDerivAt
        (fun t : ℝ => ∑ q : S, benefit q (Function.update a p t q))
        (∑ q : S, if q = p then log (q : ℝ) / ((q : ℝ) ^ (a q + 1) - 1) else 0)
        (a p) := by
      apply HasDerivAt.fun_sum
      intro q _
      by_cases hqp : q = p
      · subst q
        simpa [benefit] using
          continuous_prime_hasDerivAt (x := a p) hp (by linarith [ha p])
      · simpa only [Function.update_of_ne hqp, if_false, hqp] using
          hasDerivAt_const (a p) (benefit q (a q))
    simpa only [sum_ite_eq', Finset.mem_univ, ite_true] using hs
  have hL := ray_bounds hS hθ (theta_le_clock_of_naturalSupport hS (extend_admissible ha))
  have hL0 : clock S (extend a) ≠ 0 := ne_of_gt (by linarith [hL.2.1])
  have hl0 : log (clock S (extend a)) ≠ 0 := ne_of_gt (by linarith [hL.2.2])
  have hcost := (hc.log (by simpa only [Function.update_eq_self] using hL0)).log
    (by simpa only [Function.update_eq_self] using hl0)
  have hd := (hcost.const_add eulerMascheroniConstant).sub hb
  have hfun : (fun t : ℝ => phi S (extend (Function.update a p t))) =
      (fun t : ℝ => eulerMascheroniConstant +
        log (log (clock S (extend (Function.update a p t)))) -
          ∑ q : S, benefit q (Function.update a p t q)) := by
    funext t
    simp only [phi_coordinates, clock_coordinates]
  rw [hfun]
  convert hd using 1 <;>
    simp only [Function.update_eq_self, div_eq_mul_inv, mul_inv_rev] <;> ring

private lemma update_feasible {S : Finset ℕ} {a : S → ℝ} (ha : a ∈ orthant S)
    (p : S) {t : ℝ} (ht : 1 ≤ t) : Function.update a p t ∈ orthant S := by
  classical
  intro q
  by_cases hqp : q = p
  · subst q
    simpa using ht
  · simpa only [Function.update_of_ne hqp] using ha q

/-- These are derived first-order conditions for EVERY genuine minimizer.
At a supported boundary coordinate the right derivative is nonnegative;
in the interior the two-sided derivative vanishes. The tie case is kept. -/
theorem minimizer_kkt {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) {a : S → ℝ} (ha : a ∈ orthant S)
    (hmin : IsMinOn (fun b : S → ℝ => phi S (extend b)) (orthant S) a) (p : S) :
    let d := log (p : ℝ) * (1 / (clock S (extend a) * log (clock S (extend a))) -
      1 / ((p : ℝ) ^ (a p + 1) - 1))
    0 ≤ d ∧ (1 < a p → d = 0) := by
  classical
  dsimp only
  let f : ℝ → ℝ := fun t => phi S (extend (Function.update a p t))
  have hf : IsMinOn f (Ici 1) (a p) := by
    apply isMinOn_iff.mpr
    intro t ht
    simpa only [f, Function.update_eq_self] using
      (isMinOn_iff.mp hmin) (Function.update a p t) (update_feasible ha p ht)
  have hd := coordinate_hasDerivAt hS hθ ha p
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici 1) (a p) := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [segment_eq_Icc (by linarith : a p ≤ a p + 1)]
    intro t ht
    exact (ha p).trans ht.1
  constructor
  · have hnonneg := hf.isLocalMinOn.hasFDerivWithinAt_nonneg
      hd.hasDerivWithinAt.hasFDerivWithinAt hcone
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hnonneg
  · intro hinterior
    exact (hf.isLocalMin (Ici_mem_nhds hinterior)).hasDerivAt_eq_zero hd

private lemma solve_coordinate {p L a : ℝ} (hp : 1 < p) (hL : 1 < L)
    (ha : 1 ≤ a)
    (hnonneg : 0 ≤ log p * (1 / (L * log L) - 1 / (p ^ (a + 1) - 1)))
    (hzero : 1 < a → log p * (1 / (L * log L) - 1 / (p ^ (a + 1) - 1)) = 0) :
    a = max 1 (logCutoff L / log p - 1) := by
  have hp0 : 0 < p := by linarith
  have hw : 0 < log p := log_pos hp
  have hL1 : 1 < L := by linarith
  have hden : 0 < L * log L := mul_pos (by linarith) (log_pos hL1)
  have ht : 1 < p ^ (a + 1) := one_lt_rpow hp (by linarith)
  have htden : 0 < p ^ (a + 1) - 1 := by linarith
  have hC : 0 < 1 + L * log L := by linarith
  by_cases hinterior : 1 < a
  · have hsub : 1 / (L * log L) - 1 / (p ^ (a + 1) - 1) = 0 :=
      (mul_eq_zero.mp (hzero hinterior)).resolve_left hw.ne'
    have heq : 1 / (L * log L) = 1 / (p ^ (a + 1) - 1) := sub_eq_zero.mp hsub
    have hdeneq : L * log L = p ^ (a + 1) - 1 := by
      have h := congrArg (fun x : ℝ => x⁻¹) heq
      simpa only [one_div, inv_inv] using h
    have hpow : p ^ (a + 1) = 1 + L * log L := by linarith
    have hlog : logCutoff L = (a + 1) * log p := by
      rw [logCutoff, ← hpow, log_rpow hp0]
    have hratio : logCutoff L / log p = a + 1 :=
      (div_eq_iff hw.ne').mpr hlog
    rw [hratio, add_sub_cancel_right, max_eq_right ha]
  · have haeq : a = 1 := le_antisymm (le_of_not_gt hinterior) ha
    have hsub : 0 ≤ 1 / (L * log L) - 1 / (p ^ (a + 1) - 1) :=
      nonneg_of_mul_nonneg_right hnonneg hw
    have hinv : 1 / (p ^ (a + 1) - 1) ≤ 1 / (L * log L) := sub_nonneg.mp hsub
    have hcross := (div_le_div_iff₀ htden hden).mp hinv
    have hpow : 1 + L * log L ≤ p ^ (2 : ℕ) := by
      norm_num [haeq, rpow_two] at hcross
      linarith
    have hlog : logCutoff L ≤ 2 * log p := by
      have h := log_le_log hC hpow
      simpa only [logCutoff, log_pow, Nat.cast_ofNat] using h
    have hcritical : logCutoff L / log p - 1 ≤ 1 := by
      have h := (div_le_iff₀ hw).mpr hlog
      linarith
    rw [haeq, max_eq_left hcritical]

/-- Solving the actual boundary conditions, with positive denominators,
forces the max formula. Inactive equality gives exponent exactly one. -/
theorem minimizer_response {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) {a : S → ℝ} (ha : a ∈ orthant S)
    (hmin : IsMinOn (fun b : S → ℝ => phi S (extend b)) (orthant S) a) :
    ∀ p : S, a p = max 1 (logCutoff (clock S (extend a)) / log (p : ℝ) - 1) := by
  intro p
  have hkkt := minimizer_kkt hS hθ ha hmin p
  have hp : (1 : ℝ) < (p : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p p.property))
  exact solve_coordinate hp
    (ray_bounds hS hθ (theta_le_clock_of_naturalSupport hS (extend_admissible ha))).2.1 (ha p) hkkt.1 hkkt.2

lemma response_clock_identity {S : Finset ℕ} (hS : naturalSupport S)
    {a : S → ℝ}
    (hresponse : ∀ p : S, a p = max 1 (logCutoff (clock S (extend a)) / log (p : ℝ) - 1)) :
    responseClock S (clock S (extend a)) = clock S (extend a) := by
  symm
  calc
    clock S (extend a) = ∑ p : S, a p * log (p : ℝ) := clock_coordinates a
    _ = ∑ p : S, max (log (p : ℝ))
        (logCutoff (clock S (extend a)) - log (p : ℝ)) := by
      apply sum_congr rfl
      intro p _
      have hp : (1 : ℝ) < (p : ℕ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p p.property))
      have hw : 0 < log (p : ℝ) := log_pos hp
      rw [hresponse p, max_mul_of_nonneg _ _ hw.le, one_mul]
      congr 1
      field_simp [hw.ne']
      <;> ring
    _ = responseClock S (clock S (extend a)) := (sum_coe_sort S _).trans rfl

/-- General, non-numeric unique-minimum theorem for the SAME literal Phi.
The scalar clock is obtained by the IVT and the kink-safe right-derivative fence; the vector minimum is first
obtained by compact sublevels, then identified by its genuine KKT.
The last equality uses the original realInfimum definition unchanged.
Uniqueness is in real^S; natural-indexed representatives are equal on S.
There is deliberately no assertion that the attained value is positive. -/
theorem unique_real_minimum {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) :
    ∃ Lstar : ℝ, theta S ≤ Lstar ∧ responseClock S Lstar = Lstar ∧
      (∀ M : ℝ, theta S ≤ M → responseClock S M = M → M = Lstar) ∧
      let astar : S → ℝ := fun p => max 1 (logCutoff Lstar / log (p : ℝ) - 1)
      astar ∈ orthant S ∧
      IsMinOn (fun b : S → ℝ => phi S (extend b)) (orthant S) astar ∧
      (∀ a : S → ℝ, a ∈ orthant S →
        IsMinOn (fun b : S → ℝ => phi S (extend b)) (orthant S) a → a = astar) ∧
      realInfimum S = phi S (extend astar) := by
  obtain ⟨Lstar, hstar, hunique⟩ := exists_unique_clock hS hθ
  -- This is the independent existence step; no KKT point is assumed to exist.
  obtain ⟨a, ha, hmin⟩ := minimum_attained hS hθ
  have hidentify (b : S → ℝ) (hb : b ∈ orthant S)
      (hbmin : IsMinOn (fun c : S → ℝ => phi S (extend c)) (orthant S) b) :
      b = (fun p : S => max 1 (logCutoff Lstar / log (p : ℝ) - 1)) := by
    have hresponse := minimizer_response hS hθ hb hbmin
    have hclock : clock S (extend b) = Lstar := hunique _
      ⟨theta_le_clock_of_naturalSupport hS (extend_admissible hb), response_clock_identity hS hresponse⟩
    funext p
    simpa only [hclock] using hresponse p
  have haeq := hidentify a ha hmin
  refine ⟨Lstar, hstar.1, hstar.2, (fun M hM hfix => hunique M ⟨hM, hfix⟩), ?_⟩
  dsimp only
  refine ⟨?_, ?_, (fun b hb hbmin => hidentify b hb hbmin), ?_⟩
  · rw [← haeq]
    exact ha
  · rw [← haeq]
    exact hmin
  · rw [← haeq]
    exact infimum_of_minimum ha hmin

end D5.S3.Arith.Robin.PriceRecord.OwnClockUniqueMinimum
