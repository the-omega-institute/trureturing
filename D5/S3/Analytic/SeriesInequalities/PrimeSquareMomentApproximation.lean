/- GID: D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform real-moment approximation for the prime-square local factor in MO516091. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation

open scoped BigOperators
open scoped Topology
open Filter

noncomputable section

def factor (p : ℝ) (a : ℕ) : ℝ :=
  if a = 0 then 1 else
    (p + 3 * (a : ℝ) * (p - 1)) / (2 * (p + (a : ℝ) * (p - 1)))

def localMoment (p s : ℝ) : ℝ :=
  (1 - p⁻¹) * ∑' a : ℕ, (factor p a) ^ s / p ^ a

def c : ℝ := Real.log (7 / 6) / 2

def c3 : ℝ := Real.log (5 / 4) / 3

def originalClaim : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 - c3 / c →
  ∀ B : ℝ, 2 < B →
  ∀ ε : ℝ, 0 < ε →
  ∃ S : ℝ, ∀ s : ℝ, S ≤ s →
    ∀ p : ℕ, p.Prime → p % 4 = 1 →
      Real.exp ((1 - δ) * c * s) < p →
      (p : ℝ) ≤ B * Real.exp (c * s) →
      |Real.log (localMoment p s) -
        Real.log (1 + Real.exp (2 * c * s) / (p : ℝ) ^ 2)| < ε

private lemma factor_nonneg {p : ℝ} (hp : 1 ≤ p) (a : ℕ) :
    0 ≤ factor p a := by
  by_cases ha : a = 0
  · norm_num [factor, ha]
  · simp only [factor, ha, ↓reduceIte]
    have hden : 0 < 2 * (p + (a : ℝ) * (p - 1)) := by
      have haR : 0 < (a : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ha)
      positivity
    positivity

private lemma factor_nonzero_formula (p : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    factor p a = (p + 3 * (a : ℝ) * (p - 1)) /
      (2 * (p + (a : ℝ) * (p - 1))) := by
  simp [factor, Nat.ne_of_gt ha]

private lemma factor_pos {p : ℝ} (hp : 1 < p) (a : ℕ) :
    0 < factor p a := by
  by_cases ha : a = 0
  · simp [factor, ha]
  · simp only [factor, ha, ↓reduceIte]
    have haR : 0 < (a : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ha)
    positivity

private lemma factor_le_three_halves {p : ℝ} (hp : 1 ≤ p) (a : ℕ) :
    factor p a ≤ (3 / 2 : ℝ) := by
  by_cases ha : a = 0
  · norm_num [factor, ha]
  · simp only [factor, ha, ↓reduceIte]
    have haR : 0 < (a : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ha)
    have hden : 0 < 2 * (p + (a : ℝ) * (p - 1)) := by positivity
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr (by norm_num : (0 : ℝ) ≤ a))]

private lemma factor_le_g {p : ℝ} (hp : 1 ≤ p) {a : ℕ} (ha : 1 ≤ a) :
    factor p a ≤ (3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1)) := by
  rw [factor_nonzero_formula p ha]
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hden : 0 < 2 * (p + (a : ℝ) * (p - 1)) := by positivity
  apply (div_le_iff₀ hden).2
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr (by positivity : (0 : ℝ) ≤ a))]

private lemma g_cube_le_pow (a : ℕ) (ha : 3 ≤ a) :
    ((3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1))) ^ (3 : ℕ) ≤ (5 / 4 : ℝ) ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
      have haR : 0 < (a : ℝ) := by positivity
      have hden : 0 < 2 * ((a : ℝ) + 1) := by positivity
      have hden' : 0 < 2 * ((a : ℝ) + 2) := by positivity
      have hratio :
          ((3 * ((a + 1 : ℕ) : ℝ) + 1) /
              (2 * (((a + 1 : ℕ) : ℝ) + 1))) ^ (3 : ℕ) ≤
            (5 / 4 : ℝ) *
              ((3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1))) ^ (3 : ℕ) := by
        let y : ℝ := (a : ℝ) - 3
        have hy : 0 ≤ y := by
          dsimp [y]
          have hyNat : 0 ≤ a - 3 := by omega
          exact_mod_cast hyNat
        have hpoly : 0 ≤
            27 * y ^ 6 + 675 * y ^ 5 + 6759 * y ^ 4 + 34525 * y ^ 3 +
              93906 * y ^ 2 + 126300 * y + 62568 := by positivity
        have hpoly' : 0 ≤
            5 * (3 * (a : ℝ) + 1) ^ 3 * ((a : ℝ) + 2) ^ 3 -
              4 * (3 * (a : ℝ) + 4) ^ 3 * ((a : ℝ) + 1) ^ 3 := by
          calc
            0 ≤ 27 * y ^ 6 + 675 * y ^ 5 + 6759 * y ^ 4 + 34525 * y ^ 3 +
                93906 * y ^ 2 + 126300 * y + 62568 := hpoly
            _ = 5 * (3 * (a : ℝ) + 1) ^ 3 * ((a : ℝ) + 2) ^ 3 -
                4 * (3 * (a : ℝ) + 4) ^ 3 * ((a : ℝ) + 1) ^ 3 := by
              dsimp [y]
              ring
        norm_num [Nat.cast_add]
        field_simp
        nlinarith [hpoly']
      calc
        ((3 * ((a + 1 : ℕ) : ℝ) + 1) /
              (2 * (((a + 1 : ℕ) : ℝ) + 1))) ^ (3 : ℕ) ≤
            (5 / 4 : ℝ) *
              ((3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1))) ^ (3 : ℕ) := hratio
        _ ≤ (5 / 4 : ℝ) * (5 / 4 : ℝ) ^ a :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (5 / 4 : ℝ) ^ (a + 1) := by rw [pow_succ]; ring

private lemma g_log_le (a : ℕ) (ha : 3 ≤ a) :
    Real.log ((3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1))) ≤ c3 * (a : ℝ) := by
  have hpos : 0 < (3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1)) := by positivity
  have hpow := g_cube_le_pow a ha
  have hlog : Real.log (((3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1))) ^ (3 : ℕ)) ≤
      Real.log ((5 / 4 : ℝ) ^ a) := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  rw [show c3 = Real.log (5 / 4) / 3 by rfl]
  nlinarith

private lemma factor_rpow_le_exp_c3 {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s)
    {a : ℕ} (ha : 3 ≤ a) :
    (factor p a) ^ s ≤ Real.exp (c3 * s * (a : ℝ)) := by
  have hfactor : 0 < factor p a := factor_pos hp a
  have hg : 0 < (3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1)) := by positivity
  have hfg : factor p a ≤ (3 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1)) :=
    factor_le_g hp.le (by omega)
  have hlog : Real.log (factor p a) ≤ c3 * (a : ℝ) := by
    exact (Real.log_le_log hfactor (hfg)).trans (g_log_le a ha)
  rw [Real.rpow_def_of_pos hfactor]
  apply Real.exp_le_exp.mpr
  nlinarith

private def tailTerm (p s : ℝ) (k : ℕ) : ℝ :=
  (factor p (k + 3)) ^ s / p ^ (k + 3)

private lemma tailTerm_le_geometric {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s)
    (hq : 0 ≤ Real.exp (c3 * s) / p) (hq1 : Real.exp (c3 * s) / p < 1)
    (k : ℕ) :
    tailTerm p s k ≤ (Real.exp (c3 * s) / p) ^ (k + 3) := by
  unfold tailTerm
  have hfac := factor_rpow_le_exp_c3 hp hs (a := k + 3) (by omega)
  have hden : 0 < p ^ (k + 3) := by positivity
  have hexp : Real.exp (c3 * s * ((k + 3 : ℕ) : ℝ)) =
      (Real.exp (c3 * s)) ^ (k + 3) := by
    rw [show c3 * s * ((k + 3 : ℕ) : ℝ) = (k + 3 : ℕ) * (c3 * s) by ring,
      Real.exp_nat_mul]
  calc
    (factor p (k + 3)) ^ s / p ^ (k + 3) ≤
        Real.exp (c3 * s * ((k + 3 : ℕ) : ℝ)) / p ^ (k + 3) :=
      div_le_div_of_nonneg_right hfac hden.le
    _ = (Real.exp (c3 * s) / p) ^ (k + 3) := by
      rw [hexp, div_pow]

private lemma tailTerm_summable {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s)
    (hq : 0 ≤ Real.exp (c3 * s) / p) (hq1 : Real.exp (c3 * s) / p < 1) :
    Summable (tailTerm p s) := by
  apply Summable.of_nonneg_of_le (fun k => by
      unfold tailTerm
      exact div_nonneg (Real.rpow_nonneg (factor_nonneg hp.le (k + 3)) s) (by positivity)) _
    (by simpa [pow_add] using
      ((summable_geometric_of_lt_one hq hq1).mul_left
        ((Real.exp (c3 * s) / p) ^ 3)))
  intro k
  simpa [pow_add, mul_comm] using tailTerm_le_geometric hp hs hq hq1 k

private lemma tail_tsum_le_geometric {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s)
    (hq : 0 ≤ Real.exp (c3 * s) / p) (hq1 : Real.exp (c3 * s) / p < 1) :
    (∑' k : ℕ, tailTerm p s k) ≤
      (Real.exp (c3 * s) / p) ^ 3 /
        (1 - Real.exp (c3 * s) / p) := by
  have ht := tailTerm_summable hp hs hq hq1
  let q : ℝ := Real.exp (c3 * s) / p
  have hg := (summable_geometric_of_lt_one hq hq1).mul_left (q ^ 3)
  have hle : (∑' k : ℕ, tailTerm p s k) ≤ ∑' k : ℕ, q ^ 3 * q ^ k := by
    apply ht.tsum_le_tsum
    · intro k
      simpa [q, pow_add, mul_comm] using tailTerm_le_geometric hp hs hq hq1 k
    · exact hg
  calc
    (∑' k : ℕ, tailTerm p s k) ≤ ∑' k : ℕ, q ^ 3 * q ^ k := hle
    _ = q ^ 3 * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
    _ = q ^ 3 / (1 - q) := by rw [div_eq_mul_inv]
    _ = (Real.exp (c3 * s) / p) ^ 3 /
        (1 - Real.exp (c3 * s) / p) := by rfl

private lemma factor_rpow_nonneg {p s : ℝ} (hp : 1 ≤ p) (a : ℕ) :
    0 ≤ (factor p a) ^ s :=
  (Real.rpow_nonneg (factor_nonneg hp a) s)

private lemma factor_rpow_le_three_halves {p s : ℝ} (hp : 1 ≤ p) (hs : 0 ≤ s) (a : ℕ) :
    (factor p a) ^ s ≤ (3 / 2 : ℝ) ^ s := by
  exact Real.rpow_le_rpow (factor_nonneg hp a) (factor_le_three_halves hp a) hs

private lemma localMoment_summable {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s) :
    Summable (fun a : ℕ => (factor p a) ^ s / p ^ a) := by
  have hq : 0 ≤ p⁻¹ := by positivity
  have hq1 : p⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity)]
    exact hp
  have hg : Summable (fun a : ℕ => ((3 / 2 : ℝ) ^ s) * (p⁻¹) ^ a) :=
    (summable_geometric_of_lt_one hq hq1).mul_left _
  apply Summable.of_nonneg_of_le
    (fun a => div_nonneg (factor_rpow_nonneg hp.le a) (by positivity)) _ hg
  intro a
  have hpow : (factor p a) ^ s ≤ (3 / 2 : ℝ) ^ s :=
    factor_rpow_le_three_halves hp.le hs a
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul_of_nonneg_right hpow (by positivity)

private lemma localMoment_pos {p s : ℝ} (hp : 1 < p) (hs : 0 < s) :
    0 < localMoment p s := by
  unfold localMoment
  have hsum := localMoment_summable hp hs.le
  have hterm : 0 < (factor p 0) ^ s / p ^ (0 : ℕ) := by simp [factor]
  have htsum : 0 < ∑' a : ℕ, (factor p a) ^ s / p ^ a :=
    hsum.tsum_pos (fun a => div_nonneg (factor_rpow_nonneg hp.le a) (by positivity)) 0 hterm
  have hpref : 0 < 1 - p⁻¹ := by
    have : p⁻¹ < 1 := by rw [inv_lt_one₀ (by positivity)]; exact hp
    linarith
  positivity

private lemma c3_pos : 0 < c3 := by
  unfold c3
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

lemma c3_lt_c : c3 < c := by
  have h : (5 / 4 : ℝ) ^ (2 : ℕ) < (7 / 6 : ℝ) ^ (3 : ℕ) := by norm_num
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  unfold c3 c
  norm_num at hl
  linarith

lemma c_pos : 0 < c := c3_pos.trans c3_lt_c

private lemma log_one_sub_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -(2 * x) ≤ Real.log (1 - x) := by
  have ht : 0 < 1 - x := by linarith
  have heq : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by
    field_simp
    ring
  have hb : x / (1 - x) ≤ 2 * x := by
    apply (div_le_iff₀ ht).2
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.one_sub_inv_le_log_of_pos ht
  rw [heq] at hl
  linarith

private lemma factor_one_le {p : ℝ} (hp : 2 ≤ p) : factor p 1 ≤ 1 := by
  norm_num [factor]
  apply (div_le_iff₀ (show 0 < 2 * (p + (p - 1)) by linarith)).2
  linarith

private lemma factor_two_log_lower {p : ℝ} (hp : 2 ≤ p) :
    2 * c - 2 * p⁻¹ ≤ Real.log (factor p 2) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := by positivity
  have hr1 : p⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hd : 0 < 21 * p - 14 := by linarith
  have hf : factor p 2 = (7 / 6 : ℝ) * (1 - 4 / (21 * p - 14)) := by
    simp only [factor, show (2 : ℕ) ≠ 0 by decide, if_false, Nat.cast_ofNat]
    ring_nf
    field_simp [show -4 + p * 6 ≠ 0 by linarith, show -14 + p * 21 ≠ 0 by linarith]
    ring
  have hdp : 4 / (21 * p - 14) ≤ p⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hd hp0]
    linarith
  have ht : 0 < 1 - 4 / (21 * p - 14) := by linarith
  have hl : Real.log (1 - p⁻¹) ≤ Real.log (1 - 4 / (21 * p - 14)) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [hf, Real.log_mul (by norm_num) ht.ne']
  have hb := log_one_sub_lower hr hr1
  unfold c
  linarith

private lemma moment_decomposition {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s) :
    localMoment p s = (1 - p⁻¹) *
      (1 + (factor p 1) ^ s / p + (factor p 2) ^ s / p ^ (2 : ℕ) +
        ∑' k : ℕ, tailTerm p s k) := by
  have hsum := localMoment_summable hp hs
  have heq := hsum.sum_add_tsum_nat_add 3
  simpa [localMoment, tailTerm, Finset.sum_range_succ, factor, add_assoc] using
    congrArg (fun z : ℝ => (1 - p⁻¹) * z) heq.symm

private lemma moment_log_bound {p s : ℝ} (hp : 2 ≤ p) (hs : 0 < s)
    (hq1 : Real.exp (c3 * s) / p < 1) :
    |Real.log (localMoment p s) -
      Real.log (1 + Real.exp (2 * c * s) / p ^ (2 : ℕ))| ≤
      2 * p⁻¹ + 2 * s * p⁻¹ +
        (Real.exp (c3 * s) / p) ^ (3 : ℕ) / (1 - Real.exp (c3 * s) / p) := by
  have hp' : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := by positivity
  have hr1 : p⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hpref : 0 < 1 - p⁻¹ := by linarith
  let X : ℝ := Real.exp (2 * c * s) / p ^ (2 : ℕ)
  let R : ℝ := Real.exp (-(2 * s * p⁻¹))
  let T : ℝ := ∑' k : ℕ, tailTerm p s k
  let U : ℝ := (factor p 1) ^ s / p + T
  let A : ℝ := 1 + X
  let A0 : ℝ := 1 + (factor p 2) ^ s / p ^ (2 : ℕ)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hA0 : 1 ≤ A0 := by
    exact le_add_of_nonneg_right (div_nonneg (factor_rpow_nonneg hp'.le 2) (by positivity))
  have hA0pos : 0 < A0 := by linarith
  have hT : 0 ≤ T := by
    apply tsum_nonneg
    intro k
    unfold tailTerm
    exact div_nonneg (factor_rpow_nonneg hp'.le (k + 3)) (by positivity)
  have hU : 0 ≤ U := by
    dsimp [U]
    exact add_nonneg (div_nonneg (factor_rpow_nonneg hp'.le 1) hp0.le) hT
  have hUbound : U ≤ p⁻¹ + T := by
    dsimp [U]
    have h1 := Real.rpow_le_one (factor_nonneg hp'.le 1) (factor_one_le hp) hs.le
    have hd := div_le_div_of_nonneg_right h1 hp0.le
    simpa [one_div] using add_le_add_right hd T
  have hR : 0 < R := Real.exp_pos _
  have hR1 : R ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have h2upper : (factor p 2) ^ s ≤ Real.exp (2 * c * s) := by
    have hg := factor_le_g hp'.le (a := 2) (by omega)
    norm_num at hg
    rw [Real.rpow_def_of_pos (factor_pos hp' 2)]
    apply Real.exp_le_exp.mpr
    have hl := Real.log_le_log (factor_pos hp' 2) hg
    unfold c
    nlinarith
  have h2lower : Real.exp (2 * c * s) * R ≤ (factor p 2) ^ s := by
    rw [Real.rpow_def_of_pos (factor_pos hp' 2), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := factor_two_log_lower hp
    nlinarith
  have hA0upper : A0 ≤ A := by
    dsimp [A0, A, X]
    have hd : (factor p 2) ^ s / p ^ (2 : ℕ) ≤
        Real.exp (2 * c * s) / p ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right h2upper (by positivity)
    linarith
  have hA0lower : A * R ≤ A0 := by
    have hd := div_le_div_of_nonneg_right h2lower (show 0 ≤ p ^ (2 : ℕ) by positivity)
    rw [← div_mul_eq_mul_div] at hd
    dsimp [A, A0, X]
    nlinarith
  have hm : localMoment p s = (1 - p⁻¹) * (A0 + U) := by
    rw [moment_decomposition hp' hs.le]
    dsimp [A0, U, T]
    ring
  have hmpos := localMoment_pos hp' hs
  have hsumpos : 0 < A0 + U := by
    rw [hm] at hmpos
    exact (mul_pos_iff_of_pos_left hpref).mp hmpos
  have hlower : Real.log A - (2 * p⁻¹ + 2 * s * p⁻¹) ≤
      Real.log (localMoment p s) := by
    have hl := Real.log_le_log (mul_pos hA hR) hA0lower
    rw [Real.log_mul hA.ne' hR.ne', show Real.log R = -(2 * s * p⁻¹) by
      dsimp [R]; rw [Real.log_exp]] at hl
    have hplus := Real.log_le_log hA0pos (le_add_of_nonneg_right hU)
    rw [hm, Real.log_mul hpref.ne' hsumpos.ne']
    have hprefbound := log_one_sub_lower hr hr1
    linarith
  have hupper : Real.log (localMoment p s) ≤ Real.log A + p⁻¹ + T := by
    have hsum : A0 + U ≤ A * (1 + p⁻¹ + T) := by
      have hAt : 1 ≤ A := by dsimp [A]; linarith
      have hpos : 0 ≤ p⁻¹ + T := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hAt hpos]
    have hl := Real.log_le_log hsumpos hsum
    have hpluspos : 0 < 1 + p⁻¹ + T := by positivity
    rw [Real.log_mul hA.ne' hpluspos.ne'] at hl
    have hlogplus := Real.log_le_sub_one_of_pos hpluspos
    have hprefneg : Real.log (1 - p⁻¹) ≤ 0 :=
      Real.log_nonpos hpref.le (by linarith)
    rw [hm, Real.log_mul hpref.ne' hsumpos.ne']
    linarith
  have htbound := tail_tsum_le_geometric hp' hs.le (by positivity) hq1
  have htailpos : 0 ≤ (Real.exp (c3 * s) / p) ^ (3 : ℕ) /
      (1 - Real.exp (c3 * s) / p) := by positivity
  dsimp [T] at hupper
  dsimp [A, X] at hlower hupper
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hs.le hr]

private lemma uniform_bound {α p s : ℝ} (hα : c3 < α) (hp : 2 ≤ p) (hs : 0 < s)
    (hplower : Real.exp (α * s) < p)
    (hv : Real.exp (-((α - c3) * s)) ≤ 1 / 2) :
    |Real.log (localMoment p s) -
      Real.log (1 + Real.exp (2 * c * s) / p ^ (2 : ℕ))| ≤
      2 * Real.exp (-(α * s)) + 2 * s * Real.exp (-(α * s)) +
        2 * Real.exp (-((α - c3) * s)) := by
  have hp0 : 0 < p := by linarith
  have hr : p⁻¹ ≤ Real.exp (-(α * s)) := by
    have hi := one_div_le_one_div_of_le (Real.exp_pos (α * s)) hplower.le
    simpa [one_div, Real.exp_neg] using hi
  let q : ℝ := Real.exp (c3 * s) / p
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqv : q ≤ Real.exp (-((α - c3) * s)) := by
    calc
      q ≤ Real.exp (c3 * s) * Real.exp (-(α * s)) := by
        dsimp [q]
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
      _ = Real.exp (-((α - c3) * s)) := by rw [← Real.exp_add]; congr 1; ring
  have hqhalf : q ≤ 1 / 2 := hqv.trans hv
  have hq1 : q < 1 := by linarith
  have hq3 : q ^ (3 : ℕ) ≤ q := by
    have hsq : q ^ (2 : ℕ) ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hq]
  have ht : q ^ (3 : ℕ) / (1 - q) ≤ 2 * q := by
    calc
      q ^ (3 : ℕ) / (1 - q) ≤ q / (1 - q) :=
        div_le_div_of_nonneg_right hq3 (by linarith)
      _ ≤ 2 * q := by
        apply (div_le_iff₀ (show 0 < 1 - q by linarith)).2
        nlinarith [mul_nonneg hq (show 0 ≤ 1 - 2 * q by linarith)]
  have he := moment_log_bound hp hs hq1
  change _ ≤ 2 * p⁻¹ + 2 * s * p⁻¹ + q ^ (3 : ℕ) / (1 - q) at he
  have hrs := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * s by positivity)
  linarith

theorem result : originalClaim := by
  intro δ hδ hδtop B hB ε hε
  let α : ℝ := (1 - δ) * c
  have hα : c3 < α := by
    have hd := (lt_sub_iff_add_lt).mp hδtop
    have hc := c_pos
    have he := (div_lt_iff₀ hc).mp (show c3 / c < 1 - δ by linarith)
    dsimp [α]
    nlinarith
  have hαpos : 0 < α := c3_pos.trans hα
  have hk : 0 < α - c3 := sub_pos.mpr hα
  have hscale : Tendsto (fun s : ℝ => α * s) atTop atTop :=
    tendsto_id.const_mul_atTop hαpos
  have hscale' : Tendsto (fun s : ℝ => (α - c3) * s) atTop atTop :=
    tendsto_id.const_mul_atTop hk
  have hu : Tendsto (fun s : ℝ => Real.exp (-(α * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hv : Tendsto (fun s : ℝ => Real.exp (-((α - c3) * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale'
  have hsu : Tendsto (fun s : ℝ => s * Real.exp (-(α * s))) atTop (𝓝 0) := by
    have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).div_const α
    convert hh using 1 <;> simp only [pow_one, zero_div]
    ext s
    field_simp
    simp [Function.comp_apply, mul_comm]
  have hmajor : Tendsto (fun s : ℝ =>
      2 * Real.exp (-(α * s)) + 2 * s * Real.exp (-(α * s)) +
        2 * Real.exp (-((α - c3) * s))) atTop (𝓝 0) := by
    convert ((hu.const_mul 2).add (hsu.const_mul 2)).add (hv.const_mul 2) using 1 <;>
      simp [mul_assoc]
  have hevent : ∀ᶠ s : ℝ in atTop,
      1 ≤ s ∧ Real.exp (-((α - c3) * s)) ≤ 1 / 2 ∧
        2 * Real.exp (-(α * s)) + 2 * s * Real.exp (-(α * s)) +
          2 * Real.exp (-((α - c3) * s)) < ε := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hv.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
      hmajor.eventually_lt_const hε] with s hs hv' hm
    exact ⟨hs, hv'.le, hm⟩
  obtain ⟨S, hS⟩ := eventually_atTop.mp hevent
  refine ⟨S, ?_⟩
  intro s hs p hp hp4 hplower hpupper
  obtain ⟨hs1, hv', hm⟩ := hS s hs
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (uniform_bound hα hp2 (by linarith) hplower hv').trans_lt hm

end

end D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
