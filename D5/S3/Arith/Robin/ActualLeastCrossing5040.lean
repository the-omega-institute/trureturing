/- GID: D5/S3/Arith/Robin/ActualLeastCrossing5040
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualLeastCrossing5040
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A uniform actual least-height crossing is a strict abundancy record divisible by 5040. -/

import D5.S3.Arith.Robin.ActualIntegerHeightJump
import D5.S3.Arith.ExponentExchange.AbundancyRecord5040

/-! One positive threshold works simultaneously for every original 0 < eta < 1/2.
The statement applies to every actual least crossing. It does not construct a crossing
without the explicit height-unboundedness hypothesis of first_crossing_calibration. -/

noncomputable section
namespace D5.S3.Arith.Robin.ActualLeastCrossing5040

open Finset Filter
open scoped Topology
open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.ActualIntegerHeightJump
open D5.S3.Arith.Robin.ActualIntegerLogEnvelope
open D5.S3.Arith.ExponentExchange.AbundancyRecord5040

private theorem strict_scalar {l beta eta : ℝ} (hl : 2 ≤ l) (hb : 0 < beta)
    (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2) :
    (2 / l) * (1 - Real.exp (-eta * beta)) < Real.log (1 + beta / l) := by
  let G : ℝ → ℝ := fun u =>
    Real.log (l + u) - Real.log l - (2 / l) * (1 - Real.exp (-u / 2))
  have hl0 : 0 < l := by linarith
  have hd (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt G (1 / (l + u) - Real.exp (-u / 2) / l) u := by
    have hlog := ((hasDerivAt_id u).const_add l).log (by linarith : l + u ≠ 0)
    have hexp := (Real.hasDerivAt_exp (-u / 2)).comp u
      ((hasDerivAt_id u).neg.div_const 2)
    convert (hlog.sub_const (Real.log l)).sub
      (((hasDerivAt_const u 1).sub hexp).const_mul (2 / l)) using 1 <;>
      (try funext x) <;> dsimp [G] <;> ring
  have hmono : StrictMonoOn G (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici, Set.mem_Ioi] at hu
      rw [(hd u hu.le).deriv]
      have he := Real.add_one_lt_exp (show u / 2 ≠ 0 by positivity)
      have hmul : l + u < l * Real.exp (u / 2) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ l - 2) (by positivity : 0 ≤ u / 2)]
      have hprod : Real.exp (-u / 2) * (l + u) < l := by
        rw [show -u / 2 = -(u / 2) by ring, Real.exp_neg, inv_mul_eq_div]
        exact (div_lt_iff₀ (Real.exp_pos _)).mpr hmul
      have hh : Real.exp (-u / 2) / l < 1 / (l + u) :=
        (div_lt_div_iff₀ hl0 (by linarith)).mpr (by simpa using hprod)
      linarith
  have hg := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show beta ∈ Set.Ici 0 from hb.le) hb
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0] at hg
  have hid : Real.log (l + beta) - Real.log l = Real.log (1 + beta / l) := by
    rw [← Real.log_div (by linarith : l + beta ≠ 0) hl0.ne']
    congr 1
    field_simp
  change 0 < Real.log (l + beta) - Real.log l -
    (2 / l) * (1 - Real.exp (-beta / 2)) at hg
  rw [hid] at hg
  have he : Real.exp (-beta / 2) ≤ Real.exp (-eta * beta) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hbound : (2 / l) * (1 - Real.exp (-eta * beta)) ≤
      (2 / l) * (1 - Real.exp (-beta / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

private theorem strict_height_comparison {eta X Y E delta : ℝ}
    (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hY : 1 < Y) (hYX : Y < X) (hl : 2 ≤ Real.log Y)
    (hE : E ≤ 2 / Real.log Y) (hdelta : delta ≤ 0) :
    X ^ eta * (delta + E - (Real.log (Real.log X) - Real.log (Real.log Y))) <
      Y ^ eta * E := by
  have hY0 : 0 < Y := by linarith
  have hX0 : 0 < X := hY0.trans hYX
  have hl0 : 0 < Real.log Y := by linarith
  let beta := Real.log X - Real.log Y
  have hb : 0 < beta := sub_pos.mpr (Real.log_lt_log hY0 hYX)
  let r := (Y / X) ^ eta
  have hr1 : r ≤ 1 := Real.rpow_le_one (div_pos hY0 hX0).le
    ((div_le_one hX0).mpr hYX.le) heta.le
  have hr : r = Real.exp (-eta * beta) := by
    dsimp [r]
    rw [Real.rpow_def_of_pos (div_pos hY0 hX0), Real.log_div hY0.ne' hX0.ne']
    congr 1
    dsimp [beta]
    ring
  have hid : Real.log (Real.log X) - Real.log (Real.log Y) =
      Real.log (1 + beta / Real.log Y) := by
    rw [← Real.log_div (by linarith [Real.log_lt_log hY0 hYX] : Real.log X ≠ 0) hl0.ne']
    congr 1
    dsimp [beta]
    field_simp
    ring
  have hterm : E * (1 - r) < Real.log (Real.log X) - Real.log (Real.log Y) := by
    calc
      _ ≤ (2 / Real.log Y) * (1 - r) :=
        mul_le_mul_of_nonneg_right hE (sub_nonneg.mpr hr1)
      _ < _ := by rw [hr, hid]; exact strict_scalar hl hb heta hetaHalf
  have hpow : Y ^ eta = X ^ eta * r := by
    dsimp [r]
    rw [Real.div_rpow hY0.le hX0.le]
    field_simp
  rw [hpow]
  have hxpow : 0 < X ^ eta := Real.rpow_pos_of_pos hX0 _
  nlinarith [mul_pos hxpow (sub_pos.mpr hterm), mul_nonpos_of_nonneg_of_nonpos hxpow.le hdelta]

/-- A single positive threshold, independent of eta, forces every actual least
height crossing to be a strict abundancy record on all positive predecessors,
with abundancy above thirty and the literal divisibility 5040 | m. -/
theorem uniform_actual_least_crossing_record_5040 :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ eta : ℝ, 0 < eta → eta < 1 / 2 →
      ∀ T : ℝ, T0 ≤ T → ∀ m : ℕ, 3 ≤ m → T ≤ actualHeight eta m →
        (∀ n : ℕ, 3 ≤ n → n < m → actualHeight eta n < T) →
        30 < (ArithmeticFunction.sigma 1 m : ℝ) / m ∧
        (∀ n : ℕ, 0 < n → n < m →
          (ArithmeticFunction.sigma 1 n : ℝ) / n < (ArithmeticFunction.sigma 1 m : ℝ) / m) ∧
        5040 ∣ m := by
  obtain ⟨A, hA, hupper⟩ := eventual_actual_integer_envelope
  let R := max A (max (Real.exp 2) (Real.log 30))
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htriple := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hlog)
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp
    ((htriple.eventually_ge_atTop (R - Real.eulerMascheroniConstant)).and
      (hlog.eventually_ge_atTop (Real.exp 2)))
  let M := max M0 4
  let B : ℕ → ℝ := fun j =>
    max 1 ((Real.log (j : ℝ)) ^ (1 / 2 : ℝ)) *
      max (originalObjective j - Real.eulerMascheroniConstant) 0
  have hB (j : ℕ) : 0 ≤ B j :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _)) (le_max_right _ _)
  let T0 := 1 + ∑ j ∈ range M, B j
  have hT0 : 0 < T0 := by
    dsimp [T0]
    linarith [sum_nonneg (fun j (_ : j ∈ range M) => hB j)]
  refine ⟨T0, hT0, ?_⟩
  intro eta heta hetaHalf T hT m hm hcross hleast
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hXm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hHpos : 0 < actualHeight eta m := hT0.trans_le (hT.trans hcross)
  have hF : Real.eulerMascheroniConstant < originalObjective m := by
    have hp := Real.rpow_pos_of_pos hXm eta
    unfold actualHeight at hHpos
    have := (mul_pos_iff_of_pos_left hp).mp hHpos
    linarith
  have hmM : M ≤ m := by
    by_contra h
    have hmrange : m ∈ range M := mem_range.mpr (by omega)
    have hpow : (Real.log (m : ℝ)) ^ eta ≤
        max 1 ((Real.log (m : ℝ)) ^ (1 / 2 : ℝ)) := by
      by_cases hx : 1 ≤ Real.log (m : ℝ)
      · exact (Real.rpow_le_rpow_of_exponent_le hx hetaHalf.le).trans (le_max_right _ _)
      · exact (Real.rpow_le_one hXm.le (by linarith) heta.le).trans (le_max_left _ _)
    have hbound : actualHeight eta m ≤ B m := by
      unfold actualHeight B
      exact mul_le_mul hpow (le_max_left _ _) (by linarith) (by positivity)
    have hsum : B m ≤ ∑ j ∈ range M, B j := single_le_sum (fun j _ => hB j) hmrange
    dsimp [T0] at hT
    linarith
  have hlarge := hM0 m ((le_max_left M0 4).trans hmM)
  simp only [Function.comp_apply] at hlarge
  have hWm : R < divisorLog m := by
    change Real.eulerMascheroniConstant < divisorLog m -
      Real.log (Real.log (Real.log (m : ℝ))) at hF
    linarith [hlarge.1]
  have hAm : 0 < (ArithmeticFunction.sigma 1 m : ℝ) / m :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 m hm0.ne') hmR
  have h30 : 30 < (ArithmeticFunction.sigma 1 m : ℝ) / m := by
    apply (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 30) hAm).mp
    exact ((le_max_right (Real.exp 2) (Real.log 30)).trans (le_max_right A _)).trans_lt hWm
  have hrecord : ∀ n : ℕ, 0 < n → n < m →
      (ArithmeticFunction.sigma 1 n : ℝ) / n < (ArithmeticFunction.sigma 1 m : ℝ) / m := by
    intro n hn hnm
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hAn : 0 < (ArithmeticFunction.sigma 1 n : ℝ) / n :=
      div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne') hnR
    by_contra h
    have hW : divisorLog m ≤ divisorLog n := Real.log_le_log hAm (le_of_not_gt h)
    have hWn : divisorLog n ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log hAn
      apply (div_le_iff₀ hnR).mpr
      exact_mod_cast (by simpa [pow_two] using ArithmeticFunction.sigma_le_pow_succ 1 n)
    have hRA : A < Real.log (n : ℝ) := (le_max_left A _).trans_lt (hWm.trans_le (hW.trans hWn))
    have hYexp : Real.exp 2 < Real.log (n : ℝ) :=
      ((le_max_left (Real.exp 2) (Real.log 30)).trans (le_max_right A _)).trans_lt
        (hWm.trans_le (hW.trans hWn))
    have hY : 1 < Real.log (n : ℝ) :=
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans hYexp
    have hl : 2 ≤ Real.log (Real.log (n : ℝ)) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hYexp.le
    have hn3 : 3 ≤ n := by
      by_contra hsmall
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      linarith [Real.log_le_sub_one_of_pos hnR]
    have hYX : Real.log (n : ℝ) < Real.log (m : ℝ) :=
      Real.log_lt_log hnR (by exact_mod_cast hnm)
    have hE := hupper n hn hRA.le
    have hcomp := strict_height_comparison heta hetaHalf.le hY hYX hl hE
      (sub_nonpos.mpr hW)
    have hid : originalObjective m - Real.eulerMascheroniConstant =
        (divisorLog m - divisorLog n) + (originalObjective n - Real.eulerMascheroniConstant) -
          (Real.log (Real.log (Real.log (m : ℝ))) -
            Real.log (Real.log (Real.log (n : ℝ)))) := by
      unfold originalObjective divisorLog
      ring
    have hheight : actualHeight eta m < actualHeight eta n := by
      unfold actualHeight
      rw [hid]
      exact hcomp
    linarith [hleast n hn3 hnm]
  exact ⟨h30, hrecord, strict_abundancy_record_divisible_5040 hm0 h30 hrecord⟩

#print axioms uniform_actual_least_crossing_record_5040

end D5.S3.Arith.Robin.ActualLeastCrossing5040
