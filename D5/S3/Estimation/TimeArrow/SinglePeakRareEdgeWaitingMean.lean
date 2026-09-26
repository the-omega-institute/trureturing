/- GID: D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeWaitingMean
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SinglePeakRareEdgeWaitingMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rare-edge survival decays geometrically and has an exact mean and generating function. -/

import D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeSurvival
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean

open Filter Finset
open scoped Topology
open D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeSurvival

/-- **Waiting time and generating function for the rare edge.** The survival masses are nonnegative,
nonincreasing, and converge to zero. Their sum is the tail-sum expectation `E tau`, and their
probability generating series is the rational function of Theorem 6.4. -/
theorem survival_waiting_mean {X : Type*} [Fintype X]
    (chi : X -> Real) (hchi : ∀ x, chi x = 1 ∨ chi x = -1)
    (z : X) (hz : chi z = 1) (r q : Real) (M : Nat)
    (hcard : Fintype.card X = 2 * M)
    (hplus : ((univ.filter fun x => chi x = 1).card) = M)
    (hM : 2 <= M) (hq : q = r / ((M : Real) - 1))
    (hr0 : 0 < r) (hr1 : r < 1) :
    (∀ T : Nat, 0 <= survival chi z r q T) ∧
      Antitone (survival chi z r q) ∧
      Tendsto (survival chi z r q) atTop (nhds 0) ∧
      HasSum (fun T : Nat => survival chi z r q T)
        (2 * (Fintype.card X : Real) - 1 - r) ∧
      ∀ u : Real, 0 <= u -> u <= 1 ->
        HasSum (fun T : Nat => survival chi z r q T * u ^ T)
          ((1 - (1 / (2 * (Fintype.card X : Real))) * u -
              (1 / (2 * (Fintype.card X : Real))) * r * u ^ 2) /
            (1 - u + (1 / (2 * (Fintype.card X : Real))) * (1 - r) * u ^ 2 +
              (1 / (2 * (Fintype.card X : Real))) * r * u ^ 3)) := by
  have kernel_nonneg : ∀ (chi : X -> Real) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1) (r q : Real) (M : Nat) (hcard : Fintype.card X = 2 * M) (hM : 2 <= M) (hq : q = r / ((M : Real) - 1)) (hr0 : 0 < r) (hr1 : r < 1) (x y : X), 0 <= kernel chi z r q (Fintype.card X) x y := by
    intro chi hchi z hz r q M hcard hM hq hr0 hr1 x y
    have hN : (0 : Real) < Fintype.card X := by rw [hcard]; positivity
    have hMcast : (2 : Real) <= M := by exact_mod_cast hM
    have hden : (1 : Real) <= (M : Real) - 1 := by linarith
    have hq0 : 0 < q := by rw [hq]; positivity
    have hq1 : q < 1 := by
      rw [hq]
      exact (div_lt_one (by linarith)).2 (by linarith)
    rcases hchi x with hx | hx <;> rcases hchi y with hy | hy
    all_goals by_cases hxz : x = z
    all_goals simp [kernel, profile, region, hxz, hx, hy, hz]
    all_goals norm_num at *
    all_goals apply div_nonneg <;> nlinarith
  have survival_nonneg : ∀ (chi : X -> Real) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1) (r q : Real) (M : Nat) (hcard : Fintype.card X = 2 * M) (hM : 2 <= M) (hq : q = r / ((M : Real) - 1)) (hr0 : 0 < r) (hr1 : r < 1) (T : Nat), 0 <= survival chi z r q T := by
    intro chi hchi z hz r q M hcard hM hq hr0 hr1 T
    classical
    unfold survival
    apply sum_nonneg
    intro x _
    apply mul_nonneg
    · apply mul_nonneg (by positivity)
      exact prod_nonneg fun t _ =>
        kernel_nonneg chi hchi z hz r q M hcard hM hq hr0 hr1 _ _
    · split_ifs <;> norm_num
  let s : Nat -> Real := survival chi z r q
  let p : Real := 1 / (2 * (Fintype.card X : Real))
  have hN : (0 : Real) < Fintype.card X := by rw [hcard]; positivity
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1 := by
    dsimp [p]
    have : (2 : Real) <= Fintype.card X := by rw [hcard]; exact_mod_cast (by omega : 2 <= 2 * M)
    exact (div_lt_one (by positivity)).2 (by nlinarith)
  have hsnonneg : ∀ T, 0 <= s T := fun T =>
    survival_nonneg chi hchi z hz r q M hcard hM hq hr0 hr1 T
  have hrec := survival_recurrence chi hchi z hz r q M hcard hplus hM hq
  change s 0 = 1 ∧ s 1 = 1 - p ∧ s 2 = 1 - 2 * p ∧
    ∀ T, s (T + 3) = s (T + 2) - p * (1 - r) * s (T + 1) - p * r * s T at hrec
  have hsmono : Antitone s := by
    apply antitone_nat_of_succ_le
    intro n
    rcases n with _ | n
    · rw [hrec.1, hrec.2.1]
      linarith
    rcases n with _ | T
    · rw [hrec.2.1, hrec.2.2.1]
      linarith
    rw [show T + 2 + 1 = T + 3 by omega, hrec.2.2.2 T]
    have h1 := hsnonneg (T + 1)
    have h0 := hsnonneg T
    have ha : 0 <= p * (1 - r) * s (T + 1) := by positivity
    have hb : 0 <= p * r * s T := by positivity
    linarith
  let c : Real := 1 - p
  have hc0 : 0 <= c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hcontract (T : Nat) : s (T + 3) <= c * s (T + 2) := by
    rw [hrec.2.2.2 T]
    have h21 : s (T + 2) <= s (T + 1) := hsmono (by omega)
    have h20 : s (T + 2) <= s T := hsmono (by omega)
    have ha : p * (1 - r) * s (T + 2) <= p * (1 - r) * s (T + 1) :=
      mul_le_mul_of_nonneg_left h21 (mul_nonneg hp0.le (sub_nonneg.mpr hr1.le))
    have hb : p * r * s (T + 2) <= p * r * s T :=
      mul_le_mul_of_nonneg_left h20 (mul_nonneg hp0.le hr0.le)
    dsimp [c]
    nlinarith
  have hbound : ∀ n : Nat, s (n + 2) <= s 2 * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          s (n + 1 + 2) = s (n + 3) := by congr 1 <;> omega
          _ <= c * s (n + 2) := hcontract n
          _ <= c * (s 2 * c ^ n) := mul_le_mul_of_nonneg_left ih hc0
          _ = s 2 * c ^ (n + 1) := by rw [pow_succ]; ring
  have hshiftLimit : Tendsto (fun n => s (n + 2)) atTop (nhds 0) := by
    apply squeeze_zero (fun n => hsnonneg (n + 2)) hbound
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1))
  have hlimit : Tendsto s atTop (nhds 0) := (tendsto_add_atTop_iff_nat 2).mp hshiftLimit
  have hgeom : Summable (fun n : Nat => s 2 * c ^ n) :=
    (summable_geometric_of_lt_one hc0 hc1).mul_left (s 2)
  have hshiftSummable : Summable (fun n => s (n + 2)) :=
    Summable.of_nonneg_of_le (fun n => hsnonneg (n + 2)) hbound hgeom
  have hsummable : Summable s := (summable_nat_add_iff 2).mp hshiftSummable
  have hgen : ∀ u : Real, 0 <= u -> u <= 1 ->
      HasSum (fun T : Nat => s T * u ^ T)
        ((1 - p * u - p * r * u ^ 2) /
          (1 - u + p * (1 - r) * u ^ 2 + p * r * u ^ 3)) := by
    intro u hu0 hu1
    let a : Nat -> Real := fun T => s T * u ^ T
    have hanonneg : ∀ T, 0 <= a T := fun T => mul_nonneg (hsnonneg T) (pow_nonneg hu0 T)
    have hale : ∀ T, a T <= s T := by
      intro T
      exact mul_le_of_le_one_right (hsnonneg T) (pow_le_one₀ hu0 hu1)
    have hasum : Summable a := Summable.of_nonneg_of_le hanonneg hale hsummable
    let A : Real := tsum a
    have hA : HasSum a A := hasum.hasSum
    have htail1 : HasSum (fun T => a (T + 1)) (A - a 0) := by
      simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 1).2 hA
    have htail2 : HasSum (fun T => a (T + 2)) (A - (a 0 + a 1)) := by
      simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).2 hA
    have htail3 : HasSum (fun T => a (T + 3)) (A - (a 0 + a 1 + a 2)) := by
      simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 3).2 hA
    have hright : HasSum (fun T =>
        u * a (T + 2) - p * (1 - r) * u ^ 2 * a (T + 1) - p * r * u ^ 3 * a T)
        (u * (A - (a 0 + a 1)) - p * (1 - r) * u ^ 2 * (A - a 0) -
          p * r * u ^ 3 * A) :=
      ((htail2.mul_left u).sub (htail1.mul_left (p * (1 - r) * u ^ 2))).sub
        (hA.mul_left (p * r * u ^ 3))
    have hright' : HasSum (fun T => a (T + 3))
        (u * (A - (a 0 + a 1)) - p * (1 - r) * u ^ 2 * (A - a 0) -
          p * r * u ^ 3 * A) := by
      apply hright.congr_fun
      intro T
      dsimp [a]
      rw [hrec.2.2.2 T]
      ring
    have heq := htail3.unique hright'
    have ha0 : a 0 = 1 := by simp [a, hrec.1]
    have ha1 : a 1 = (1 - p) * u := by simp [a, hrec.2.1]
    have ha2 : a 2 = (1 - 2 * p) * u ^ 2 := by simp [a, hrec.2.2.1]
    rw [ha0, ha1, ha2] at heq
    have hden : 0 < 1 - u + p * (1 - r) * u ^ 2 + p * r * u ^ 3 := by
      by_cases hu : u = 1
      · subst u
        norm_num
        nlinarith
      · have hult : u < 1 := lt_of_le_of_ne hu1 hu
        have hu2 : 0 <= u ^ 2 := pow_nonneg hu0 2
        have hu3 : 0 <= u ^ 3 := pow_nonneg hu0 3
        positivity
    have hAeq : A = (1 - p * u - p * r * u ^ 2) /
        (1 - u + p * (1 - r) * u ^ 2 + p * r * u ^ 3) := by
      apply (eq_div_iff hden.ne').2
      nlinarith
    rw [hAeq] at hA
    exact hA
  have htotal : HasSum s (2 * (Fintype.card X : Real) - 1 - r) := by
    have h := hgen 1 (by norm_num) (by norm_num)
    convert h using 1
    · ext T
      simp
    · dsimp [p]
      field_simp
      nlinarith
  refine ⟨?_, hsmono, hlimit, htotal, ?_⟩
  · exact hsnonneg
  · intro u hu0 hu1
    simpa [s, p] using hgen u hu0 hu1

#print axioms survival_waiting_mean

end D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeWaitingMean
