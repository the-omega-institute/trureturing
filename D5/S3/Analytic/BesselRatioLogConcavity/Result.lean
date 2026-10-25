/- GID: D5/S3/Analytic/BesselRatioLogConcavity/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/BesselRatioLogConcavity/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed, mathlib/module/Mathlib.Analysis.Convex.Function]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/BesselRatioLogConcavity/Result.claim; result=D5/S3/Analytic/BesselRatioLogConcavity/Result.result; claim=D5/S3/Analytic/BesselRatioLogConcavity/Result.claim
   digest: A rational series certificate refutes positive-order Bessel-ratio log-concavity. -/

/-
admission_basis: open-problem-resolution (#21440; Refuted)
escape_witness: none
Gamma recurrence, ratio summability, geometric comparison and rational
normalization instantiate frozen D5 and pinned Mathlib results.
The designated result is the only public theorem.
Per-declaration judgement: name | proof_shape | direct consumers | frozen dependencies.
All escape_witness fields are none. Helpers are expanded for frozen dependencies.
The frozen declaration alias gamma_pochhammer below means exactly:
  GID D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer
  Lean D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer
  DECLARATION statement_id sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797
Identity source: .lake/build/stratalint/scoped-lean-report.json.
  besselI | bind-only (definition) | claim, bessel_eq, bessel_ratio, bessel_pos, witness, result | none
  claim | bind-only (definition) | result | none
  term | bind-only (definition) | term_nonneg, term_step, term_summable, bessel_term_eq, bessel_summable, bessel_eq, series, series_pos, term_cast, series_lower, tail_ratio, series_upper, bessel_ratio | none
  term_nonneg | bind-only | series_pos, series_lower, tail_ratio | none
  term_step | bind-only | term_summable, term_cast, tail_ratio | none
  term_summable | bind-only | bessel_summable, series_pos, series_lower, series_upper | none
  bessel_term_eq | bind-only | bessel_summable, bessel_eq | gamma_pochhammer
  bessel_summable | bind-only | bessel_pos | gamma_pochhammer
  bessel_eq | bind-only | bessel_ratio | gamma_pochhammer
  series | bind-only (definition) | series_pos, series_lower, series_upper, series_product, witness | none
  series_pos | bind-only | series_product, witness | none
  qterm | bind-only (definition) | qlower, qupper, term_cast, series_lower, series_upper, numeric_certificate | none
  qlower | bind-only (definition) | qupper, series_lower, series_upper, numeric_certificate, series_product | none
  qratio | bind-only (definition) | qupper, tail_ratio, series_upper, numeric_certificate, series_product | none
  qupper | bind-only (definition) | series_upper, numeric_certificate, series_product | none
  term_cast | bind-only | series_lower, series_upper | none
  series_lower | bind-only | series_product | none
  tail_ratio | bind-only | series_upper | none
  series_upper | bind-only | series_product | none
  bessel_ratio | bind-only | witness | gamma_pochhammer
  bessel_pos | bind-only | result | gamma_pochhammer
  numeric_certificate | bind-only | series_product | none
  series_product | bind-only | witness | none
  witness | bind-only | result | gamma_pochhammer
  result | bind-only | settling result | gamma_pochhammer
-/

import D5.S3.Analytic.KummerRatio.BetaIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Convex.Function

noncomputable section
open Filter Topology
open scoped BigOperators
namespace D5.S3.Analytic.BesselRatioLogConcavity.Result

def besselI (ν z : ℝ) : ℝ :=
  ∑' k : ℕ, (z / 2) ^ ((2 * k : ℕ) + ν) /
    ((k.factorial : ℝ) * Real.Gamma (k + ν + 1))

def claim : Prop :=
  ∀ ν1 ν2 a1 a2 : ℝ, 0 < ν2 → ν2 ≤ ν1 → 0 < a1 → a1 ≤ a2 →
    ConcaveOn ℝ (Set.Ioi 0)
      (fun x => Real.log (besselI ν1 (a1 * x) / besselI ν2 (a2 * x)))

private def term (ν w : ℝ) (k : ℕ) : ℝ :=
  w ^ k / ((k.factorial : ℝ) * (ascPochhammer ℝ k).eval (ν + 1))

private lemma term_nonneg {ν w : ℝ} (hν : -1 < ν) (hw : 0 ≤ w) (k : ℕ) :
    0 ≤ term ν w k := by
  exact div_nonneg (pow_nonneg hw _) (mul_nonneg (Nat.cast_nonneg _)
    (ascPochhammer_pos k (ν+1) (by linarith)).le)

private lemma term_step {ν : ℝ} (hν : -1 < ν) (w : ℝ) (k : ℕ) :
    term ν w (k+1) = (w / ((k+1) * (ν+1+k))) * term ν w k := by
  have hp := (ascPochhammer_pos k (ν+1) (by linarith)).ne'
  have hνk : ν+1+(k:ℝ) ≠ 0 := ne_of_gt (by have h := Nat.cast_nonneg' (α := ℝ) k; linarith)
  have hk : (k:ℝ)+1 ≠ 0 := Nat.cast_add_one_ne_zero k
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  simp only [term, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

private lemma term_summable {ν : ℝ} (hν : -1 < ν) (w : ℝ) :
    Summable (term ν w) := by
  have hi : Tendsto (fun n : ℕ => 1 / (ν+1+(n:ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop (ν+1) tendsto_natCast_atTop_atTop)
  have hq : Tendsto (fun n : ℕ => w / ((n+1)*(ν+1+n))) atTop (𝓝 0) := by
    convert ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul hi).const_mul w using 1
    · ext n; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    · ring
  apply summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num)
  have hqn : Tendsto (fun n : ℕ => ‖w / ((n+1)*(ν+1+n))‖) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mp hq
  filter_upwards [hqn.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with n hn
  rw [term_step hν, norm_mul]
  exact mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

private lemma bessel_term_eq {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) (k : ℕ) :
    (z/2) ^ ((2*k:ℕ)+ν) / ((k.factorial:ℝ) * Real.Gamma (k+ν+1)) =
      ((z/2)^ν / Real.Gamma (ν+1)) * term ν (z^2/4) k := by
  rw [show (k:ℝ)+ν+1 = (ν+1)+k by ring,
    D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer (by linarith)]
  rw [Real.rpow_add (by positivity : 0 < z/2), Real.rpow_natCast]
  have he : (z/2)^(2*k) = (z^2/4)^k := by
    rw [pow_mul]; congr 1; ring
  rw [he]
  unfold term
  ring

private lemma bessel_summable {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    Summable (fun k : ℕ => (z/2)^((2*k:ℕ)+ν) /
      ((k.factorial:ℝ)*Real.Gamma (k+ν+1))) := by
  simp_rw [bessel_term_eq hν hz]
  exact (term_summable hν (z^2/4)).mul_left _

private lemma bessel_eq {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    besselI ν z = (z/2)^ν / Real.Gamma (ν+1) * ∑' k, term ν (z^2/4) k := by
  unfold besselI
  simp_rw [bessel_term_eq hν hz]
  rw [tsum_mul_left]

private def series (w : ℝ) : ℝ := ∑' k, term (1/10) w k

private lemma series_pos {w : ℝ} (hw : 0 ≤ w) : 0 < series w := by
  have h := (term_summable (by norm_num : -1 < (1/10:ℝ)) w).sum_le_tsum
    ({0} : Finset ℕ) (fun n _ => term_nonneg (by norm_num) hw n)
  exact lt_of_lt_of_le (by norm_num [term]) h

private def qterm (w : ℚ) : ℕ → ℚ
  | 0 => 1
  | k+1 => w / ((k+1)*(11/10+k)) * qterm w k
private def qlower (w : ℚ) : ℚ := ∑ k ∈ Finset.range 60, qterm w k
private def qratio (w : ℚ) : ℚ := w / (61*(611/10))
private def qupper (w : ℚ) : ℚ := qlower w + qterm w 60 / (1-qratio w)

private lemma term_cast (w : ℚ) (k : ℕ) :
    term (1/10) (w:ℝ) k = (qterm w k : ℝ) := by
  induction k with
  | zero => norm_num [term, qterm]
  | succ k ih =>
    rw [term_step (by norm_num), qterm, Rat.cast_mul, Rat.cast_div, ih]
    push_cast
    norm_num

private lemma series_lower (w : ℚ) (hw : 0 ≤ w) : (qlower w:ℝ) ≤ series w := by
  have h := (term_summable (by norm_num : -1 < (1/10:ℝ)) (w:ℝ)).sum_le_tsum
    (Finset.range 60) (fun n _ => term_nonneg (by norm_num) (by exact_mod_cast hw) n)
  simpa only [qlower, Rat.cast_sum, term_cast, series] using h

private lemma tail_ratio (w : ℚ) (hw : 0 ≤ w) (k : ℕ) (hk : 60 ≤ k) :
    term (1/10) (w:ℝ) (k+1) ≤ (qratio w:ℝ) * term (1/10) (w:ℝ) k := by
  rw [term_step (by norm_num)]
  apply mul_le_mul_of_nonneg_right _ (term_nonneg (by norm_num) (by exact_mod_cast hw) k)
  have hk' : (60:ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
  have hd : (61:ℝ)*(611/10) ≤ (k+1)*((1/10)+1+k) := by nlinarith
  dsimp only [qratio]
  push_cast
  norm_num at hd ⊢
  exact div_le_div_of_nonneg_left (by exact_mod_cast hw) (by norm_num) hd

private lemma series_upper (w : ℚ) (hw : 0 ≤ w) (hr : qratio w < 1) :
    series w ≤ (qupper w:ℝ) := by
  have hr0 : (0:ℝ) ≤ (qratio w:ℝ) := by
    dsimp [qratio]; push_cast; positivity
  have hr1 : (qratio w:ℝ) < 1 := by exact_mod_cast hr
  have hm (n : ℕ) : term (1/10) (w:ℝ) (n+60) ≤
      (qratio w:ℝ)^n * term (1/10) (w:ℝ) 60 := by
    simpa only [zero_add] using le_geom (u := fun n => term (1/10) (w:ℝ) (n+60))
      hr0 n (fun k _ => tail_ratio w hw (k+60) (by omega))
  have ht := Summable.tsum_le_tsum hm
    ((summable_nat_add_iff 60).2 (term_summable (by norm_num) (w:ℝ)))
    ((summable_geometric_of_lt_one hr0 hr1).mul_right (term (1/10) (w:ℝ) 60))
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1] at ht
  have he := Summable.sum_add_tsum_nat_add 60 (term_summable (ν := 1/10) (by norm_num) (w:ℝ))
  unfold series
  rw [← he]
  simp_rw [term_cast]
  unfold qupper qlower
  push_cast
  simp_rw [term_cast] at ht
  exact add_le_add le_rfl (by simpa [div_eq_mul_inv, mul_comm] using ht)

private lemma bessel_ratio {ν t : ℝ} (hν : -1 < ν) (ht : 0 < t) :
    besselI ν t / besselI ν (2*t) =
      (2:ℝ)^(-ν) * ((∑' k, term ν (t^2/4) k) / (∑' k, term ν (t^2) k)) := by
  rw [bessel_eq hν ht, bessel_eq hν (by positivity)]
  rw [show (2*t)^2/4 = t^2 by ring, show 2*t/2 = t by ring,
    Real.div_rpow (by positivity : 0 ≤ t) (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_neg (by norm_num)]
  have hg := (Real.Gamma_pos_of_pos (by linarith : 0 < ν+1)).ne'
  have hp := (Real.rpow_pos_of_pos ht ν).ne'
  field_simp

private lemma bessel_pos {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    0 < besselI ν z := by
  have hp (k : ℕ) : 0 < (z/2)^((2*k:ℕ)+ν) /
      ((k.factorial:ℝ)*Real.Gamma (k+ν+1)) := by
    have hg := Real.Gamma_pos_of_pos (show 0 < (k:ℝ)+ν+1 by
      have h := Nat.cast_nonneg' (α := ℝ) k; linarith)
    positivity
  have hh := (bessel_summable hν hz).sum_le_tsum ({0} : Finset ℕ)
    (fun k _ => (hp k).le)
  exact lt_of_lt_of_le (by simpa only [Finset.sum_singleton] using hp 0) hh

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private lemma numeric_certificate :
    (1584/1000:ℚ) ≤ qlower (9/16) ∧
    (223368/1000:ℚ) ≤ qlower (225/16) ∧
    (894574/1000:ℚ) ≤ qlower (81/4) ∧
    qupper (81/16) ≤ (15316/1000:ℚ) ∧
    qupper (9/4) ≤ (4447/1000:ℚ) ∧
    qupper (225/4) ≤ (264068:ℚ) := by
  norm_num [qlower, qupper, qratio, qterm, Finset.sum_range_succ]

private lemma series_product :
    series (81/16)^2 * series (9/4) * series (225/4) <
      series (9/16) * series (225/16) * series (81/4)^2 := by
  obtain ⟨c1,c2,c3,c4,c5,c6⟩ := numeric_certificate
  have l1 : (1584/1000:ℝ) ≤ series (9/16) := by
    refine le_trans (b := (qlower (9/16):ℝ)) ?_ ?_
    · convert (Rat.cast_le (K := ℝ)).mpr c1 using 1 ; norm_num
    · convert series_lower (9/16) (by norm_num) using 1 ; norm_num
  have l2 : (223368/1000:ℝ) ≤ series (225/16) := by
    refine le_trans (b := (qlower (225/16):ℝ)) ?_ ?_
    · convert (Rat.cast_le (K := ℝ)).mpr c2 using 1 ; norm_num
    · convert series_lower (225/16) (by norm_num) using 1 ; norm_num
  have l3 : (894574/1000:ℝ) ≤ series (81/4) := by
    refine le_trans (b := (qlower (81/4):ℝ)) ?_ ?_
    · convert (Rat.cast_le (K := ℝ)).mpr c3 using 1 ; norm_num
    · convert series_lower (81/4) (by norm_num) using 1 ; norm_num
  have u1 : series (81/16) ≤ (15316/1000:ℝ) := by
    refine le_trans (b := (qupper (81/16):ℝ)) ?_ ?_
    · convert series_upper (81/16) (by norm_num) (by norm_num [qratio]) using 1 ; norm_num
    · convert (Rat.cast_le (K := ℝ)).mpr c4 using 1 ; norm_num
  have u2 : series (9/4) ≤ (4447/1000:ℝ) := by
    refine le_trans (b := (qupper (9/4):ℝ)) ?_ ?_
    · convert series_upper (9/4) (by norm_num) (by norm_num [qratio]) using 1 ; norm_num
    · convert (Rat.cast_le (K := ℝ)).mpr c5 using 1 ; norm_num
  have u3 : series (225/4) ≤ (264068:ℝ) := by
    refine le_trans (b := (qupper (225/4):ℝ)) ?_ ?_
    · convert series_upper (225/4) (by norm_num) (by norm_num [qratio]) using 1 ; norm_num
    · convert (Rat.cast_le (K := ℝ)).mpr c6 using 1 ; norm_num
  have p1 := (series_pos (w := 81/16) (by norm_num)).le
  have p2 := (series_pos (w := 9/4) (by norm_num)).le
  have p3 := (series_pos (w := 225/4) (by norm_num)).le
  have p4 := (series_pos (w := 9/16) (by norm_num)).le
  have p5 := (series_pos (w := 225/16) (by norm_num)).le
  calc
    _ ≤ (15316/1000:ℝ)^2 * (4447/1000) * 264068 := by gcongr
    _ < (1584/1000:ℝ) * (223368/1000) * (894574/1000)^2 := by norm_num
    _ ≤ _ := by gcongr

private lemma witness :
    (besselI (1/10) (9/2) / besselI (1/10) 9)^2 <
      (besselI (1/10) (3/2) / besselI (1/10) 3) *
      (besselI (1/10) (15/2) / besselI (1/10) 15) := by
  have he (t : ℝ) (ht : 0 < t) :
      besselI (1/10) t / besselI (1/10) (2*t) =
        (2:ℝ)^(-(1/10:ℝ)) * (series (t^2/4) / series (t^2)) :=
    bessel_ratio (by norm_num) ht
  have e1 := he (3/2) (by norm_num)
  have e2 := he (9/2) (by norm_num)
  have e3 := he (15/2) (by norm_num)
  norm_num only [show (3/2:ℝ)^2=9/4 by norm_num,
    show (9/2:ℝ)^2=81/4 by norm_num,
    show (15/2:ℝ)^2=225/4 by norm_num] at e1 e2 e3
  rw [e1, e2, e3]
  have hp (w : ℝ) (hw : 0 ≤ w) : 0 < series w := series_pos hw
  have hd : (series (81/16) / series (81/4))^2 <
      (series (9/16) / series (9/4)) * (series (225/16) / series (225/4)) := by
    rw [div_pow, div_mul_div_comm]
    apply (div_lt_div_iff₀ (pow_pos (hp _ (by norm_num)) _)
      (mul_pos (hp _ (by norm_num)) (hp _ (by norm_num)))).2
    convert series_product using 1; ring
  have hc : 0 < (2:ℝ)^(-(1/10:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ = ((2:ℝ)^(-(1/10:ℝ)))^2 * (series (81/16) / series (81/4))^2 := by ring
    _ < ((2:ℝ)^(-(1/10:ℝ)))^2 *
        ((series (9/16) / series (9/4)) * (series (225/16) / series (225/4))) :=
      mul_lt_mul_of_pos_left hd (pow_pos hc _)
    _ = _ := by ring

theorem result : ¬ claim := by
  intro hclaim
  have hc := hclaim (1/10) (1/10) 1 2 (by norm_num) (le_refl _) zero_lt_one (by norm_num)
  have hcc := hc.2
  have hm := hcc (x := (3/2:ℝ)) (by norm_num : (3/2:ℝ) ∈ Set.Ioi 0)
    (y := (15/2:ℝ)) (by norm_num : (15/2:ℝ) ∈ Set.Ioi 0)
    (a := (1/2:ℝ)) (b := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [smul_eq_mul] at hm
  have p1 := div_pos (bessel_pos (ν := 1/10) (z := 3/2) (by norm_num) (by norm_num))
    (bessel_pos (ν := 1/10) (z := 3) (by norm_num) (by norm_num))
  have p2 := div_pos (bessel_pos (ν := 1/10) (z := 9/2) (by norm_num) (by norm_num))
    (bessel_pos (ν := 1/10) (z := 9) (by norm_num) (by norm_num))
  have p3 := div_pos (bessel_pos (ν := 1/10) (z := 15/2) (by norm_num) (by norm_num))
    (bessel_pos (ν := 1/10) (z := 15) (by norm_num) (by norm_num))
  have hl := Real.log_lt_log (pow_pos p2 2) witness
  rw [Real.log_pow, Real.log_mul p1.ne' p3.ne'] at hl
  norm_num at hl
  linarith

end D5.S3.Analytic.BesselRatioLogConcavity.Result
