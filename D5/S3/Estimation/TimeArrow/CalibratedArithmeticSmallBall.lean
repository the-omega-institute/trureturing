/- GID: D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A monotone moving center has a finite arithmetic small-ball bound. -/

import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
import D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
import D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
import Mathlib.Analysis.SpecialFunctions.Stirling
import D5.S3.DivergenceSupport.LogSumInequality
import Mathlib.Data.Finset.Max
open scoped BigOperators Topology
open Finset Filter
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
noncomputable section
/-- Finite conditional mass for an integer-valued count variable. -/
def eventMass (p : ℤ → ℝ) (S : Finset ℤ) : ℝ := ∑ t ∈ S, p t
/-- A lattice band uses the same center for every integer target. -/
def latticeBand (g : ℤ → ℝ) (h : ℝ) (z : ℤ) (I : Finset ℤ) : Finset ℤ :=
  I.filter (fun t => |g t - z| ≤ h)
/-- The finite central small-ball event. The outer set contains the full
integer range attainable by the moving center on the central interval. -/
def arithmeticEvent (g : ℤ → ℝ) (h : ℝ) (I Z : Finset ℤ) : Finset ℤ :=
  I.filter (fun t => ∃ z ∈ Z, |g t - z| ≤ h)
private theorem integer_set_card_le_width (S : Finset ℤ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ x ∈ S, ∀ y ∈ S, ((y - x : ℤ) : ℝ) ≤ W) :
    (S.card : ℝ) ≤ W + 1 := by
  classical
  by_cases hn : S.Nonempty
  · let a := S.min' hn
    let b := S.max' hn
    have ha : a ∈ S := S.min'_mem hn
    have hb : b ∈ S := S.max'_mem hn
    have hab : a ≤ b := S.min'_le b hb
    have hsub : S ⊆ Icc a b := by
      intro t ht
      exact mem_Icc.mpr ⟨S.min'_le t ht, S.le_max' t ht⟩
    have hc : (S.card : ℝ) ≤ ((Icc a b).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have hi : ((Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by
      exact_mod_cast Int.card_Icc_of_le a b (by omega : a ≤ b + 1)
    rw [hi] at hc
    have hd := hw a ha b hb
    push_cast at hd
    linarith
  · simp only [not_nonempty_iff_eq_empty.mp hn, card_empty, Nat.cast_zero]
    linarith
private theorem lattice_band_card_le (g : ℤ → ℝ) (s h : ℝ) (I : Finset ℤ)
    (hs : 0 < s) (hh : 0 ≤ h)
    (hg : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x)
    (z : ℤ) :
    ((latticeBand g h z I).card : ℝ) ≤ 2 * h / s + 1 := by
  apply integer_set_card_le_width _ _ (by positivity)
  intro x hx y hy
  have hx' := mem_filter.mp hx
  have hy' := mem_filter.mp hy
  by_cases hxy : x ≤ y
  · have hd := hg x hx'.1 y hy'.1 hxy
    have hxlo := (abs_le.mp hx'.2).1
    have hyhi := (abs_le.mp hy'.2).2
    apply (le_div_iff₀ hs).mpr
    nlinarith
  · have hn : ((y - x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega : y - x ≤ 0)
    exact hn.trans (by positivity)
/-- The central event is covered by the individual integer bands. This
retains the same count realization and never replaces it by independent phases. -/
theorem arithmetic_central_mass_bound (p g : ℤ → ℝ) (I Z : Finset ℤ)
    (s h a : ℝ) (hs : 0 < s) (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hmax : ∀ t ∈ I, p t ≤ a)
    (hg : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x) :
    eventMass p (arithmeticEvent g h I Z) ≤
      a * (Z.card : ℝ) * (2 * h / s + 1) := by
  classical
  have he : arithmeticEvent g h I Z = Z.biUnion (fun z => latticeBand g h z I) := by
    ext t
    simp only [arithmeticEvent, latticeBand, mem_filter, mem_biUnion]
    aesop
  calc
    eventMass p (arithmeticEvent g h I Z) ≤
        ((arithmeticEvent g h I Z).card : ℝ) * a := by
      unfold eventMass
      exact (sum_le_sum fun t ht => hmax t (mem_filter.mp ht).1).trans_eq
        (by simp only [sum_const, nsmul_eq_mul]; rfl)
    _ ≤ (∑ z ∈ Z, ((latticeBand g h z I).card : ℝ)) * a := by
      apply mul_le_mul_of_nonneg_right _ ha
      rw [he]
      exact_mod_cast card_biUnion_le
    _ = ∑ z ∈ Z, ((latticeBand g h z I).card : ℝ) * a := by rw [sum_mul]
    _ ≤ ∑ _z ∈ Z, (2 * h / s + 1) * a := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right (lattice_band_card_le g s h I hs hh hg z) ha
    _ = a * (Z.card : ℝ) * (2 * h / s + 1) := by simp; ring
/-- A closed real band restricts its integer targets to this exact interval. -/
def integerTargets (a b : ℝ) : Finset ℤ := Icc ⌈a⌉ ⌊b⌋
private theorem integer_targets_card_le (a b : ℝ) (hab : a ≤ b) :
    ((integerTargets a b).card : ℝ) ≤ b - a + 1 := by
  apply integer_set_card_le_width _ _ (by linarith)
  intro x hx y hy
  have hxa : a ≤ (x : ℝ) := (Int.le_ceil a).trans (by exact_mod_cast (mem_Icc.mp hx).1)
  have hycast : (y : ℝ) ≤ (⌊b⌋ : ℤ) := by exact_mod_cast (mem_Icc.mp hy).2
  have hyb : (y : ℝ) ≤ b :=
    hycast.trans (Int.floor_le b)
  push_cast
  linarith
open scoped Classical in
/-- The same moving center gives both the number of possible integer bands
and the number of count values in each band. A posterior approximation is
paid only by widening the small-ball event. -/
theorem moving_center_small_ball (p f g : ℤ → ℝ) (T : Finset ℤ) (a b : ℤ)
    (s K τ err A tail : ℝ) (hab : a ≤ b) (hs : 0 < s)
    (hτ : 0 ≤ τ) (herr : 0 ≤ err) (hA : 0 ≤ A)
    (hp : ∀ t, 0 ≤ p t) (hmax : ∀ t ∈ Icc a b, p t ≤ A)
    (hlower : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x)
    (hupper : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      x ≤ y → g y - g x ≤ K * s * ((y - x : ℤ) : ℝ))
    (happrox : ∀ t ∈ Icc a b, |f t - g t| ≤ err)
    (htail : eventMass p (T \ Icc a b) ≤ tail) :
    eventMass p (T.filter fun t => ∃ z : ℤ, |f t - z| ≤ τ) ≤
      A * (K * s * ((b - a : ℤ) : ℝ) + 2 * (τ + err) + 1) *
        (2 * (τ + err) / s + 1) + tail := by
  classical
  let I := Icc a b
  let h := τ + err
  let Z := integerTargets (g a - h) (g b + h)
  have ha : a ∈ I := mem_Icc.mpr ⟨le_refl _, hab⟩
  have hb : b ∈ I := mem_Icc.mpr ⟨hab, le_refl _⟩
  have hnonneg : 0 ≤ h := add_nonneg hτ herr
  have hgmono : g a ≤ g b := by
    have hd := hlower a ha b hb hab
    have hba : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hab
    nlinarith
  have hZ : (Z.card : ℝ) ≤ K * s * ((b - a : ℤ) : ℝ) + 2 * h + 1 := by
    have hc := integer_targets_card_le (g a - h) (g b + h) (by linarith)
    have hu := hupper a ha b hb hab
    dsimp [Z] at *
    linarith
  have hsub : T.filter (fun t => ∃ z : ℤ, |f t - z| ≤ τ) ⊆
      arithmeticEvent g h I Z ∪ (T \ I) := by
    intro t ht
    have htf := mem_filter.mp ht
    by_cases hti : t ∈ I
    · rcases htf.2 with ⟨z, hz⟩
      have hgz : |g t - z| ≤ h := by
        have hi := abs_add_le (g t - f t) (f t - z)
        have he := happrox t hti
        rw [abs_sub_comm (f t)] at he
        have ha : g t - f t + (f t - z) = g t - z := by ring
        rw [ha] at hi
        dsimp [h]; linarith
      have hlo := hlower a ha t hti (mem_Icc.mp hti).1
      have hhi := hlower t hti b hb (mem_Icc.mp hti).2
      have hat : (0 : ℝ) ≤ ((t - a : ℤ) : ℝ) := by
        exact_mod_cast sub_nonneg.mpr (mem_Icc.mp hti).1
      have htb : (0 : ℝ) ≤ ((b - t : ℤ) : ℝ) := by
        exact_mod_cast sub_nonneg.mpr (mem_Icc.mp hti).2
      have hzt : z ∈ Z := by
        apply mem_Icc.mpr
        constructor
        · apply Int.ceil_le.mpr
          nlinarith [(abs_le.mp hgz).2]
        · apply Int.le_floor.mpr
          nlinarith [(abs_le.mp hgz).1]
      exact mem_union_left _ (mem_filter.mpr ⟨hti, z, hzt, hgz⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨htf.1, hti⟩)
  have hm : eventMass p (T.filter fun t => ∃ z : ℤ, |f t - z| ≤ τ) ≤
      eventMass p (arithmeticEvent g h I Z) + eventMass p (T \ I) := by
    have hpart := sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hp t)
    have hu : (∑ t ∈ arithmeticEvent g h I Z ∪ (T \ I), p t) ≤
        eventMass p (arithmeticEvent g h I Z) + eventMass p (T \ I) := by
      unfold eventMass
      rw [← sum_union_inter]
      exact le_add_of_nonneg_right (sum_nonneg (fun t _ => hp t))
    exact hpart.trans hu
  have hc := arithmetic_central_mass_bound p g I Z s h A hs hnonneg hA hmax hlower
  have hzbound : A * (Z.card : ℝ) * (2 * h / s + 1) ≤
      A * (K * s * ((b - a : ℤ) : ℝ) + 2 * h + 1) * (2 * h / s + 1) := by
    gcongr
  exact hm.trans (add_le_add (hc.trans hzbound) htail)
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
from D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
from D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
end
end D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Estimation.TimeArrow.NativeRowCountTail
noncomputable section
private theorem path_fourth_moment {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hM6 : 6 ≤ M)
    (hLM : (L : ℝ) / M ≤ 1 / 45) (i : Fin M) :
    (∑ o : Obs M (2 * M * L) .path, probability r .path S o *
      (4 : ℝ) ^ (count .path o i 1 + count .path o i (-1))) ≤
        3 * Real.exp (3 * (L : ℝ)) := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb : |b r S (.inl i)| ≤ 1 := by
    rw [abs_le]
    simp only [b]
    split_ifs <;> constructor <;> linarith
  let η : ℝ := 3 / (2 * M)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 / 4 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M)).mpr
    have hh : (6 : ℝ) ≤ M := by exact_mod_cast hM6
    linarith
  have hA : driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4) =
      (3 : ℂ) / (2 * M) := by norm_num [driftA, tiltU, tiltV]
  have hB : driftB r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4) =
      ((b r S (.inl i) : ℂ) * 3) / (2 * M) := by norm_num [driftB, tiltU, tiltV]
  have hAn : ‖driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)‖ ≤ η := by
    rw [hA, norm_div, norm_mul, Complex.norm_natCast]
    norm_num [η, abs_of_pos hM]
  have hBn : ‖driftB r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)‖ ≤ η := by
    rw [hB, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
    norm_num
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hTη : ((2 * M * L : ℕ) : ℝ) * η ^ 2 = (9 / 2) * ((L : ℝ) / M) := by
    dsimp [η]
    push_cast
    field_simp
    <;> ring
  have hT : ((2 * M * L : ℕ) : ℝ) * η ^ 2 ≤ 1 / 10 := by
    rw [hTη]
    nlinarith
  have hh := actual_marked_path_pgf_poisson_envelope hq hqm hr hr1 hc1 S
    (Or.inl rfl) (fun _ : Fin 1 => i) (fun a b _ => Subsingleton.elim a b)
    (fun _ => 4) (fun _ => 4) hη hη1 hAn hBn hT
  let Z : ℝ := ∑ o : Obs M (2 * M * L) .path, probability r .path S o *
      (4 : ℝ) ^ (count .path o i 1 + count .path o i (-1))
  have hZ : actualPGF r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)
      (2 * M * L) = (Z : ℂ) := by
    simp [actualPGF, Z, pow_add]
  have htA : ((2 * M * L : ℕ) : ℂ) *
      driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4) = (3 * (L : ℝ) : ℝ) := by
    rw [hA]
    push_cast
    field_simp
    <;> ring
  have htre : ((2 * M * L : ℕ) : ℝ) *
      (driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)).re = 3 * (L : ℝ) := by
    have he := congrArg Complex.re htA
    simpa using he
  rw [hZ, htA, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, htre] at hh
  have hcoef : 20 * ((2 * M * L : ℕ) : ℝ) * η ^ 2 ≤ 2 := by
    nlinarith
  have he := hh.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
  have hu := (abs_le.mp he).2
  change Z ≤ _
  linarith
private theorem pair_fourth_moment {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (i : Fin M) :
    (∑ o : Obs M (2 * M * L) .pair, probability r .pair S o *
      (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1))) ≤
        Real.exp (3 * (L : ℝ)) := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hlaw := finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 Experiment.pair
  have hrow := (hlaw.1 S).1.2
  let g := fun p : Vertex M × Vertex M => if p.1 = .inl i then (4 : ℝ) else 1
  have hedge (x y : Vertex M) :
      (if x = .inl i ∧ chi y = 1 then (4 : ℝ) else 1) *
        (if x = .inl i ∧ chi y = -1 then (4 : ℝ) else 1) = g (x, y) := by
    cases y <;> by_cases hx : x = .inl i <;> norm_num [g, chi, hx]
  have hcount (o : Obs M (2 * M * L) .pair) :
      (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1)) =
        ∏ k : Fin (2 * M * L), g (o k) := by
    rw [pow_add]
    have hp : (4 : ℝ) ^ count .pair o i 1 =
        ∏ k : Fin (2 * M * L), if (o k).1 = .inl i ∧ chi (o k).2 = 1 then 4 else 1 := by
      simp [prod_ite, prod_const, count, edges]
      rfl
    have hm : (4 : ℝ) ^ count .pair o i (-1) =
        ∏ k : Fin (2 * M * L), if (o k).1 = .inl i ∧ chi (o k).2 = -1 then 4 else 1 := by
      simp [prod_ite, prod_const, count, edges]
      rfl
    rw [hp, hm, ← prod_mul_distrib]
    exact prod_congr rfl fun k _ => hedge _ _
  let K := fun p : Vertex M × Vertex M =>
    (2 * (M : ℝ))⁻¹ * transition r S p.1 p.2 * g p
  have hsum : (∑ p : Vertex M × Vertex M, K p) = 1 + 3 / (2 * M) := by
    rw [Fintype.sum_prod_type]
    have hx (x : Vertex M) : (∑ y : Vertex M, K (x, y)) =
        (2 * (M : ℝ))⁻¹ * (if x = .inl i then 4 else 1) := by
      dsimp [K, g]
      calc
        _ = ((2 * (M : ℝ))⁻¹ * (if x = .inl i then 4 else 1)) *
            ∑ y : Vertex M, transition r S x y := by
          rw [mul_sum]
          apply sum_congr rfl
          intro y _
          ring
        _ = _ := by rw [hrow x, mul_one]
    simp_rw [hx]
    rw [← mul_sum]
    have he : (∑ x : Vertex M, if x = .inl i then (4 : ℝ) else 1) = 2 * M + 3 := by
      have hh (x : Vertex M) : (if x = .inl i then (4 : ℝ) else 1) =
          1 + if x = .inl i then 3 else 0 := by split_ifs <;> norm_num
      simp_rw [hh]
      simp [sum_add_distrib, Fintype.card_sum, Fintype.card_fin]
      ring
    rw [he]
    field_simp
    <;> ring
  have hmass (o : Obs M (2 * M * L) .pair) :
      probability r .pair S o * (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1)) =
        ∏ k : Fin (2 * M * L), K (o k) := by
    rw [hcount]
    simp [probability, K, prod_mul_distrib]
  simp_rw [hmass]
  change (∑ o : Fin (2 * M * L) → Vertex M × Vertex M, ∏ k, K (o k)) ≤ _
  rw [← Fintype.prod_sum (fun (_ : Fin (2 * M * L)) p => K p)]
  simp_rw [hsum]
  simp only [prod_const, card_univ, Fintype.card_fin]
  calc
    (1 + 3 / (2 * (M : ℝ))) ^ (2 * M * L) ≤
        (Real.exp (3 / (2 * M))) ^ (2 * M * L) :=
      pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp (3 / (2 * (M : ℝ)))) _
    _ = Real.exp (3 * (L : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
      <;> ring
/-- An exponential budget holds under each original complete-history law.
The path estimate retains adjacent visits and all terminal coordinates. -/
theorem native_row_count_tail {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hM6 : 6 ≤ M)
    (hL : 1 ≤ L) (hLM : (L : ℝ) / M ≤ 1 / 45)
    (e : Experiment) (i : Fin M) :
    (∑ o : Obs M (2 * M * L) e,
      if 8 * L < count e o i 1 + count e o i (-1) then probability r e S o else 0) ≤
        Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S
  have hmgf : (∑ o : Obs M (2 * M * L) e, probability r e S o *
      (4 : ℝ) ^ (count e o i 1 + count e o i (-1))) ≤ 3 * Real.exp (3 * (L : ℝ)) := by
    cases e
    · exact (pair_fourth_moment r S hq hqm hr hr1 hc1 i).trans
        (by nlinarith [Real.exp_pos (3 * (L : ℝ))])
    · exact path_fourth_moment r S hq hqm hr hr1 hc1 hM6 hLM i
  have hmarkov : (4 : ℝ) ^ (8 * L) *
      (∑ o : Obs M (2 * M * L) e,
        if 8 * L < count e o i 1 + count e o i (-1) then probability r e S o else 0) ≤
      ∑ o : Obs M (2 * M * L) e, probability r e S o *
        (4 : ℝ) ^ (count e o i 1 + count e o i (-1)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro o _
    split_ifs with ho
    · have hh : (4 : ℝ) ^ (8 * L) ≤
          (4 : ℝ) ^ (count e o i 1 + count e o i (-1)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (hp o)
    · simp only [mul_zero]
      exact mul_nonneg (hp o) (pow_nonneg (by norm_num) _)
  have h3 : 3 ≤ Real.exp (3 * (L : ℝ)) := by
    have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hh := Real.add_one_le_exp (3 * (L : ℝ))
    linarith
  have hb : 3 * Real.exp (3 * (L : ℝ)) ≤ Real.exp (6 * (L : ℝ)) := by
    rw [show 6 * (L : ℝ) = 3 * L + 3 * L by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have hpow : (4 : ℝ) ^ (8 * L) = Real.exp (8 * (L : ℝ) * Real.log 4) := by
    conv_lhs => rw [show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
  have htotal := hmarkov.trans (hmgf.trans hb)
  rw [hpow] at htotal
  calc
    _ ≤ Real.exp (6 * (L : ℝ)) / Real.exp (8 * (L : ℝ) * Real.log 4) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using htotal)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring
/-- A single all-row cutoff preserves all original rows and pays the union
budget, uniformly in the true support and in the experiment. -/
theorem native_all_row_count_cut {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hM6 : 6 ≤ M)
    (hL : 1 ≤ L) (hLM : (L : ℝ) / M ≤ 1 / 45) (e : Experiment) :
    (∑ o : Obs M (2 * M * L) e,
      if ∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
      then probability r e S o else 0) ≥
        1 - (M : ℝ) * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have law := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1
  have hp := law.1 S
  have hsum := law.2 S
  have hpoint (o : Obs M (2 * M * L) e) :
      (if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
       then probability r e S o else 0) ≤
        ∑ i : Fin M, if 8 * L < count e o i 1 + count e o i (-1)
          then probability r e S o else 0 := by
    by_cases ho : ∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
    · rw [if_neg (not_not.mpr ho)]
      apply sum_nonneg
      intro i _
      split_ifs <;> [exact hp o; exact le_rfl]
    · rw [if_pos ho]
      push_neg at ho
      obtain ⟨i, hi⟩ := ho
      have hh := single_le_sum (f := fun j : Fin M =>
        if 8 * L < count e o j 1 + count e o j (-1) then probability r e S o else 0)
        (fun j _ => by split_ifs <;> [exact hp o; exact le_rfl]) (mem_univ i)
      simpa only [if_pos hi] using hh
  have hbad : (∑ o : Obs M (2 * M * L) e,
      if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
      then probability r e S o else 0) ≤
        (M : ℝ) * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
    calc
      _ ≤ ∑ o : Obs M (2 * M * L) e, ∑ i : Fin M,
          if 8 * L < count e o i 1 + count e o i (-1)
          then probability r e S o else 0 := sum_le_sum fun o _ => hpoint o
      _ = ∑ i : Fin M, ∑ o : Obs M (2 * M * L) e,
          if 8 * L < count e o i 1 + count e o i (-1)
          then probability r e S o else 0 := sum_comm
      _ ≤ ∑ _i : Fin M, Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) :=
        sum_le_sum fun i _ => native_row_count_tail r S hq hqm hr hr1 hc1 hM6 hL hLM e i
      _ = _ := by simp
  have hpartition :
      (∑ o : Obs M (2 * M * L) e,
        if ∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
        then probability r e S o else 0) +
      (∑ o : Obs M (2 * M * L) e,
        if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
        then probability r e S o else 0) = 1 := by
    rw [← sum_add_distrib, ← hsum]
    apply sum_congr rfl
    intro o _
    split_ifs <;> simp_all only [not_true_eq_false, not_false_eq_true,
      add_zero, zero_add]
  linarith
end
end D5.S3.Estimation.TimeArrow.NativeRowCountTail
open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
noncomputable section
/-- Coarse Stirling envelopes used only inside the four-cell atom estimate. -/
theorem log_factorial_envelopes {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log n - n + Real.log n / 2 ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n / 2 + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have hl := Stirling.le_log_factorial_stirling hn.ne'
    have hc : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  · have hs := Stirling.log_stirlingSeq'_antitone (show 0 ≤ n - 1 by omega)
    have hi : n - 1 + 1 = n := by omega
    change Real.log (Stirling.stirlingSeq (n - 1 + 1)) ≤
      Real.log (Stirling.stirlingSeq (0 + 1)) at hs
    rw [hi, Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one] at hs
    simp (disch := positivity) only [Real.log_div, Real.log_exp,
      Real.log_sqrt, Real.log_mul] at hs
    linarith
/-- The four positive cells and their row and column margins are one table.
The entropy term in its factorial ratio is nonpositive. -/
private theorem four_cell_entropy (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a+b) * Real.log (a+b) + (c+d) * Real.log (c+d) +
      (a+c) * Real.log (a+c) + (b+d) * Real.log (b+d) -
      (a+b+c+d) * Real.log (a+b+c+d) -
      a * Real.log a - b * Real.log b - c * Real.log c - d * Real.log d ≤ 0 := by
  let N := a+b+c+d
  have hN : 0 < N := by dsimp [N]; positivity
  let A : Fin 4 → ℝ := ![a,b,c,d]
  let B : Fin 4 → ℝ := ![(a+b)*(a+c)/N, (a+b)*(b+d)/N,
    (c+d)*(a+c)/N, (c+d)*(b+d)/N]
  have hA (i : Fin 4) : 0 < A i := by fin_cases i <;> simp [A] <;> assumption
  have hB (i : Fin 4) : 0 < B i := by fin_cases i <;> simp [B] <;> positivity
  have hAs : (∑ i, A i) = N := by simp [A, Fin.sum_univ_four, N]
  have hBs : (∑ i, B i) = N := by
    simp [B, Fin.sum_univ_four]
    field_simp
    dsimp [N]
    ring
  have h := D5.S3.DivergenceSupport.LogSumInequality.log_sum_inequality A B
    (fun i => (hA i).le) (fun i => (hB i).le)
    (fun i hi => False.elim ((hB i).ne' hi))
  rw [hAs, hBs, div_self hN.ne', Real.log_one, mul_zero] at h
  simp [A, B, Fin.sum_univ_four] at h
  simp (disch := positivity) only [Real.log_div, Real.log_mul] at h
  dsimp [N] at h
  linarith only [h]
/-- A uniform atom cap on the central table region. The four lower bounds
are for the same table; no independence or unguarded natural subtraction is used. -/
private theorem hypergeometric_central_atom {N R U t : ℕ} (hR : R ≤ N) (hU : U ≤ N)
    (htR : t < R) (htU : t < U) (hfour : U - t < N - R)
    (ht : 0 < t) (γ : ℝ) (hγ : 0 < γ)
    (h0 : γ * N ≤ t) (h1 : γ * N ≤ ((R-t : ℕ) : ℝ))
    (h2 : γ * N ≤ ((U-t : ℕ) : ℝ))
    (h3 : γ * N ≤ ((N-R-(U-t) : ℕ) : ℝ)) :
    ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ) ≤
      Real.exp 4 / (γ ^ 2 * Real.sqrt N) := by
  have hN : 0 < N := lt_of_lt_of_le (lt_trans ht htR) hR
  have hNR : 0 < N - R := lt_of_le_of_lt (Nat.zero_le _) hfour
  have hNU : 0 < N - U := by omega
  have hRt : 0 < R - t := Nat.sub_pos_of_lt htR
  have hUt : 0 < U - t := Nat.sub_pos_of_lt htU
  have hD : 0 < N - R - (U-t) := Nat.sub_pos_of_lt hfour
  have hRN : (R : ℝ) ≤ N := by exact_mod_cast hR
  have hUN : (U : ℝ) ≤ N := by exact_mod_cast hU
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hNR0 : (0 : ℝ) < (N-R : ℕ) := by exact_mod_cast hNR
  have hNU0 : (0 : ℝ) < (N-U : ℕ) := by exact_mod_cast hNU
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hRt0 : (0 : ℝ) < (R-t : ℕ) := by exact_mod_cast hRt
  have hUt0 : (0 : ℝ) < (U-t : ℕ) := by exact_mod_cast hUt
  have hD0 : (0 : ℝ) < (N-R-(U-t) : ℕ) := by exact_mod_cast hD
  let H : ℝ := ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ)
  have hH : 0 < H := by
    dsimp [H]
    exact div_pos (mul_pos (by exact_mod_cast Nat.choose_pos htR.le)
      (by exact_mod_cast Nat.choose_pos hfour.le)) (by exact_mod_cast Nat.choose_pos hU)
  have hlogH : Real.log H = Real.log (R.factorial : ℝ) + Real.log ((N-R).factorial : ℝ) +
      Real.log (U.factorial : ℝ) + Real.log ((N-U).factorial : ℝ) -
      Real.log (N.factorial : ℝ) - Real.log (t.factorial : ℝ) -
      Real.log ((R-t).factorial : ℝ) - Real.log ((U-t).factorial : ℝ) -
      Real.log ((N-R-(U-t)).factorial : ℝ) := by
    dsimp [H]
    rw [Nat.cast_choose ℝ htR.le, Nat.cast_choose ℝ hfour.le, Nat.cast_choose ℝ hU]
    simp (disch := positivity) only [Real.log_mul, Real.log_div]
    ring
  have hent := four_cell_entropy (t : ℝ) ((R-t : ℕ) : ℝ) ((U-t : ℕ) : ℝ)
    ((N-R-(U-t) : ℕ) : ℝ) ht0 hRt0 hUt0 hD0
  have hAB : (t : ℝ) + (R-t : ℕ) = R := by exact_mod_cast Nat.add_sub_of_le htR.le
  have hCD : ((U-t : ℕ) : ℝ) + (N-R-(U-t) : ℕ) = (N-R : ℕ) := by
    exact_mod_cast Nat.add_sub_of_le hfour.le
  have hAC : (t : ℝ) + (U-t : ℕ) = U := by exact_mod_cast Nat.add_sub_of_le htU.le
  have hBD : ((R-t : ℕ) : ℝ) + (N-R-(U-t) : ℕ) = (N-U : ℕ) := by
    exact_mod_cast (by omega : R-t+(N-R-(U-t)) = N-U)
  have hAll : (t : ℝ) + (R-t : ℕ) + (U-t : ℕ) + (N-R-(U-t) : ℕ) = N := by
    exact_mod_cast (by omega : t+(R-t)+(U-t)+(N-R-(U-t)) = N)
  rw [hAll, hAB, hCD, hAC, hBD] at hent
  have hlogupper : Real.log H ≤ 4 +
      (Real.log R + Real.log (N-R : ℕ) + Real.log U + Real.log (N-U : ℕ) -
        Real.log N - Real.log t - Real.log (R-t : ℕ) - Real.log (U-t : ℕ) -
        Real.log (N-R-(U-t) : ℕ)) / 2 := by
    rw [hlogH]
    have hRa := (log_factorial_envelopes (by omega : 0 < R)).2
    have hNa := (log_factorial_envelopes hNR).2
    have hUa := (log_factorial_envelopes (by omega : 0 < U)).2
    have hNUa := (log_factorial_envelopes hNU).2
    have hNb := (log_factorial_envelopes hN).1
    have htb := (log_factorial_envelopes ht).1
    have hRb := (log_factorial_envelopes hRt).1
    have hUb := (log_factorial_envelopes hUt).1
    have hDb := (log_factorial_envelopes hD).1
    have htot : (R : ℝ) + (N-R : ℕ) + U + (N-U : ℕ) =
        N + t + (R-t : ℕ) + (U-t : ℕ) + (N-R-(U-t) : ℕ) := by
      exact_mod_cast (by omega : R+(N-R)+U+(N-U) = N+t+(R-t)+(U-t)+(N-R-(U-t)))
    linarith
  have hlR := Real.log_le_log hR0 hRN
  have hlU := Real.log_le_log hU0 hUN
  have hlNR := Real.log_le_log hNR0 (show ((N-R : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast (Nat.sub_le N R))
  have hlNU := Real.log_le_log hNU0 (show ((N-U : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast (Nat.sub_le N U))
  have hγN : 0 < γ * (N : ℝ) := mul_pos hγ hN0
  have hl0 := Real.log_le_log hγN h0
  have hl1 := Real.log_le_log hγN h1
  have hl2 := Real.log_le_log hγN h2
  have hl3 := Real.log_le_log hγN h3
  rw [Real.log_mul hγ.ne' hN0.ne'] at hl0 hl1 hl2 hl3
  have hl : Real.log H ≤ 4 - 2 * Real.log γ - Real.log N / 2 := by linarith
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hexp := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hH] at hexp
  have hrhs : Real.exp (4 - 2 * Real.log γ - Real.log (N : ℝ) / 2) =
      Real.exp 4 / (γ ^ 2 * Real.sqrt N) := by
    rw [show 4 - 2 * Real.log γ - Real.log (N : ℝ) / 2 =
      4 - (Real.log (γ ^ 2) + Real.log (Real.sqrt (N : ℝ))) by
        rw [Real.log_pow, Real.log_sqrt hN0.le]; ring,
      Real.exp_sub, Real.exp_add, Real.exp_log (sq_pos_of_pos hγ), Real.exp_log hsqrt]
  exact hexp.trans_eq hrhs
/-- Balanced numerical margins supply the four interior-cell hypotheses of
the atom estimate throughout one central interval. -/
private theorem hypergeometric_balanced_central_atom {N R U t : ℕ}
    (hN : 0 < N) (hR : R ≤ N) (hU : U ≤ N) (δ w : ℝ) (hδ : 0 < δ)
    (hRlo : δ * N ≤ R) (hRhi : (R : ℝ) ≤ (1-δ)*N)
    (hUlo : δ * N ≤ U) (hUhi : (U : ℝ) ≤ (1-δ)*N)
    (hw : w ≤ δ ^ 2 * N / 2) (ht : |(t : ℝ) - (U : ℝ)*R/N| ≤ w) :
    ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ) ≤
      Real.exp 4 / ((δ ^ 2 / 2) ^ 2 * Real.sqrt N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := central_four_cells_lower (N : ℝ) R U δ t w hN0 hδ.le
    hRlo hRhi hUlo hUhi ht
  have hγ : 0 < δ ^ 2 / 2 := by positivity
  have hγN : 0 < δ ^ 2 / 2 * (N : ℝ) := mul_pos hγ hN0
  have hs (j : Fin 4) : δ ^ 2 / 2 * (N : ℝ) ≤ cellCounts N R U t j := by
    have hj := hc j
    linarith
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  simp only [cellCounts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have ht0 : 0 < t := by exact_mod_cast (hγN.trans_le h0)
  have htR : t < R := by exact_mod_cast (by linarith : (t : ℝ) < R)
  have htU : t < U := by exact_mod_cast (by linarith : (t : ℝ) < U)
  have hf : U-t < N-R := by
    have hsub : (U : ℝ) - t < (N : ℝ) - R := by linarith
    exact_mod_cast (show ((U-t : ℕ) : ℝ) < (N-R : ℕ) by
      rw [Nat.cast_sub htU.le, Nat.cast_sub hR]; exact hsub)
  apply hypergeometric_central_atom hR hU htR htU hf ht0 (δ ^ 2 / 2) hγ h0
  · simpa only [Nat.cast_sub htR.le] using h2
  · simpa only [Nat.cast_sub htU.le] using h1
  · rw [Nat.cast_sub hf.le, Nat.cast_sub hR, Nat.cast_sub htU.le]
    linarith
open D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
set_option quotPrecheck false in
local notation "H" => fun N R U t : ℕ => if t ≤ U then
  ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ) else 0
open scoped Classical in
/-- The integer count kernel retains both support guards. Its atom and tail
inputs to the moving-center engine are proved here from the original kernel. -/
theorem hypergeometric_arithmetic_bound {N R U : ℕ}
    (hN : 1 < N) (hR : R ≤ N) (hU : U ≤ N)
    (δ L s K h : ℝ) (hδ : 0 < δ) (hL : 0 < L) (hs : 0 < s) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hRlo : δ * N ≤ R) (hRhi : (R : ℝ) ≤ (1-δ)*N)
    (hUlo : δ * N ≤ U) (hUhi : (U : ℝ) ≤ (1-δ)*N)
    (hwide : 1 ≤ L * Real.sqrt N) (hsmall : L * Real.sqrt N ≤ δ ^ 2 * N / 2)
    (g : ℤ → ℝ)
    (hlower : ∀ x ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      ∀ y ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      x ≤ y → s * ((y-x : ℤ) : ℝ) ≤ g y-g x)
    (hupper : ∀ x ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      ∀ y ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      x ≤ y → g y-g x ≤ K*s*((y-x : ℤ) : ℝ)) :
    (∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g (t : ℤ)-z| ≤ h), H N R U t) ≤
      Real.exp 4 / ((δ ^ 2 / 2) ^ 2 * Real.sqrt N) *
        (K*s*(2*L*Real.sqrt N)+2*h+1) * (2*h/s+1) + 1/(4*L^2) := by
  classical
  let ν : ℝ := (U : ℝ)*R/N
  let w : ℝ := L * Real.sqrt N
  let a : ℤ := ⌈ν-w⌉
  let b : ℤ := ⌊ν+w⌋
  let T := (range (U+1)).map (Nat.castEmbedding : ℕ ↪ ℤ)
  let p : ℤ → ℝ := fun t => if 0 ≤ t then H N R U t.toNat else 0
  let A : ℝ := Real.exp 4 / ((δ ^ 2 / 2) ^ 2 * Real.sqrt N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp (t : ℤ) : 0 ≤ p t := by dsimp [p]; split_ifs <;> positivity
  have hpc (t : ℕ) : p t = H N R U t := by simp [p]
  have hcentral (t : ℤ) : t ∈ Icc a b ↔ |(t : ℝ)-ν| ≤ w := by
    simp only [mem_Icc, a, b, Int.ceil_le, Int.le_floor, abs_le]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hab : a ≤ b := by
    have ha := Int.ceil_lt_add_one (ν-w)
    have hb := Int.sub_one_lt_floor (ν+w)
    have : (a : ℝ) < b := by dsimp [a,b]; dsimp [w] at *; linarith
    exact_mod_cast this.le
  have hmax (t : ℤ) (ht : t ∈ Icc a b) : p t ≤ A := by
    by_cases ht0 : 0 ≤ t
    · dsimp only [p]
      rw [if_pos ht0]
      by_cases htU : t.toNat ≤ U
      · rw [if_pos htU]
        apply hypergeometric_balanced_central_atom (by omega : 0 < N) hR hU δ w hδ
          hRlo hRhi hUlo hUhi hsmall
        have hcast : (t.toNat : ℝ) = (t : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg ht0
        simpa only [hcast] using (hcentral t).mp ht
      · simp only [if_neg htU]
        exact hA
    · simp only [p, if_neg ht0]
      exact hA
  have hout : T \ Icc a b =
      ((range (U+1)).filter fun t : ℕ => w < |(t : ℝ)-ν|).map (Nat.castEmbedding : ℕ ↪ ℤ) := by
    rw [sdiff_eq_filter, filter_map]
    congr 1
    apply filter_congr
    intro t _
    simp only [Function.comp_apply, Nat.castEmbedding_apply]
    rw [hcentral]
    simp only [Int.cast_natCast, not_le]
  have htail : eventMass p (T \ Icc a b) ≤ 1/(4*L^2) := by
    rw [hout, eventMass, sum_map]
    simp only [Nat.castEmbedding_apply, hpc]
    exact kernel_central_tail hR hU hN L hL
  have he := moving_center_small_ball p g g T a b s K h 0 A (1/(4*L^2)) hab hs hh
    le_rfl hA hp hmax hlower hupper (fun t _ => by simp) htail
  have hleft : eventMass p (T.filter fun t => ∃ z : ℤ, |g t-z| ≤ h) =
      ∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g (t : ℤ)-z| ≤ h), H N R U t := by
    rw [eventMass, filter_map, sum_map]
    simp only [Function.comp_apply, Nat.castEmbedding_apply, hpc]
  rw [hleft] at he
  have hwidth : ((b-a : ℤ) : ℝ) ≤ 2*w := by
    have ha := Int.le_ceil (ν-w)
    have hb := Int.floor_le (ν+w)
    dsimp [a,b]
    push_cast
    linarith
  calc
    _ ≤ A * (K*s*((b-a : ℤ) : ℝ)+2*h+1)*(2*h/s+1)+1/(4*L^2) := by
      simpa only [add_zero] using he
    _ ≤ _ := by
      dsimp [A,w] at *
      gcongr
      simpa only [mul_assoc] using hwidth
open scoped Classical in
/-- An arbitrary native predicate only needs lattice containment centrally.
The remaining count values are paid by the original kernel tail. -/
theorem hypergeometric_predicate_bound {N R U : ℕ}
    (hR : R ≤ N) (hU : U ≤ N) (hN : 1 < N) (L : ℝ) (hL : 0 < L)
    (P : ℕ → Prop) (g : ℤ → ℝ) (h B : ℝ)
    (hpush : ∀ t ∈ range (U+1), |(t : ℝ)-(U : ℝ)*R/N| ≤ L*Real.sqrt N →
      P t → ∃ z : ℤ, |g t-z| ≤ h)
    (hsmall : (∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g t-z| ≤ h),
      H N R U t) ≤ B+1/(4*L^2)) :
    (∑ t ∈ (range (U+1)).filter P, H N R U t) ≤ B+1/(2*L^2) := by
  have hpart : (∑ t ∈ (range (U+1)).filter P, H N R U t) ≤
      (∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g t-z| ≤ h), H N R U t) +
      ∑ t ∈ (range (U+1)).filter (fun t : ℕ => L*Real.sqrt N <
        |(t : ℝ)-(U : ℝ)*R/N|), H N R U t := by
    simp only [sum_filter]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro t ht
    have hp : 0 ≤ H N R U t := by dsimp; split_ifs <;> positivity
    by_cases hP : P t
    · rw [if_pos hP]
      by_cases hc : |(t : ℝ)-(U : ℝ)*R/N| ≤ L*Real.sqrt N
      · rw [if_pos (hpush t ht hc hP), if_neg (not_lt.mpr hc)]
        exact le_add_of_nonneg_right (le_refl 0)
      · rw [if_pos (lt_of_not_ge hc)]
        exact le_add_of_nonneg_left (by split_ifs <;> positivity)
    · rw [if_neg hP]
      positivity
  have htail := kernel_central_tail hR hU hN L hL
  have he := hpart.trans (add_le_add hsmall htail)
  have hsum : 1/(4*L^2)+1/(4*L^2) = 1/(2*L^2) := by ring
  linarith only [he,hsum]
end
end D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
open scoped BigOperators
open Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
noncomputable section
open private
  D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments.kernel_normalization
from D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
set_option quotPrecheck false in
local notation "W" => fun N R U t : ℕ => R.choose t * (N - R).choose (U - t)
set_option quotPrecheck false in
local notation "H" => fun N R U t : ℕ => if t ≤ U then
  ((R.choose t : ℝ) * ((N - R).choose (U - t) : ℝ)) / (N.choose U : ℝ) else 0
/-- Cross multiplication remains valid at the lower support boundary. -/
private theorem adjacent_cross {N R U t : ℕ} (hR : R ≤ N) (htR : t ≤ R)
    (htU : t < U) (hcell : U - t ≤ N - R + 1) :
    (W N R U (t + 1) : ℝ) * (t + 1) * ((N : ℝ) - R + t + 1 - U) =
      (W N R U t : ℝ) * ((R : ℝ) - t) * ((U : ℝ) - t) := by
  have ha := Nat.choose_succ_right_eq R t
  have hb := Nat.choose_succ_right_eq (N - R) (U - t - 1)
  have hk : U - t - 1 + 1 = U - t := by omega
  have hs : U - (t + 1) = U - t - 1 := by omega
  rw [hk] at hb
  have hc : U - t - 1 ≤ N - R := by omega
  have haR : (R.choose (t + 1) : ℝ) * (t + 1) =
      (R.choose t : ℝ) * ((R : ℝ) - t) := by
    have ha' : (R.choose (t + 1) : ℝ) * ((t + 1 : ℕ) : ℝ) =
        (R.choose t : ℝ) * ((R - t : ℕ) : ℝ) := by exact_mod_cast ha
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub htR] using ha'
  have hbR : ((N - R).choose (U - (t + 1)) : ℝ) * ((N : ℝ) - R + t + 1 - U) =
      ((N - R).choose (U - t) : ℝ) * ((U : ℝ) - t) := by
    have hb' : ((N - R).choose (U - t) : ℝ) * ((U - t : ℕ) : ℝ) =
        ((N - R).choose (U - t - 1) : ℝ) * ((N - R - (U - t - 1) : ℕ) : ℝ) := by
      exact_mod_cast hb
    rw [Nat.cast_sub htU.le, Nat.cast_sub hc, Nat.cast_sub hR,
      Nat.cast_sub (by omega : 1 ≤ U - t), Nat.cast_sub htU.le] at hb'
    rw [hs]
    push_cast at hb'
    nlinarith [hb']
  push_cast
  calc
    _ = ((R.choose (t + 1) : ℝ) * (t + 1)) *
        (((N - R).choose (U - (t + 1)) : ℝ) * ((N : ℝ) - R + t + 1 - U)) := by ring
    _ = ((R.choose t : ℝ) * ((R : ℝ) - t)) *
        (((N - R).choose (U - t) : ℝ) * ((U : ℝ) - t)) := by rw [haR, hbR]
    _ = _ := by ring
/-- Every positive maximizing atom lies between the two adjacent-ratio thresholds. -/
private theorem maximizing_thresholds {N R U m : ℕ} (hR : R ≤ N) (hU : U ≤ N)
    (hmR : m ≤ R) (hmU : m ≤ U) (hcell : U - m ≤ N - R)
    (hpos : 0 < W N R U m) (hmax : ∀ t ≤ U, W N R U t ≤ W N R U m) :
    ((N : ℝ) + 2) * m ≤ ((R : ℝ) + 1) * (U + 1) ∧
      ((R : ℝ) + 1) * (U + 1) ≤ ((N : ℝ) + 2) * (m + 1) := by
  have hposR : (0 : ℝ) < W N R U m := by exact_mod_cast hpos
  have hmRR : (m : ℝ) ≤ R := by exact_mod_cast hmR
  have hmUR : (m : ℝ) ≤ U := by exact_mod_cast hmU
  have hRN : (R : ℝ) ≤ N := by exact_mod_cast hR
  have hUN : (U : ℝ) ≤ N := by exact_mod_cast hU
  constructor
  · by_cases hm0 : m = 0
    · subst m; simp only [Nat.cast_zero, mul_zero]; positivity
    have hm1 : 1 ≤ m := by omega
    have hp := adjacent_cross hR (by omega : m - 1 ≤ R)
      (by omega : m - 1 < U) (by omega : U - (m - 1) ≤ N - R + 1)
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm1]; norm_num
    rw [Nat.sub_add_cancel hm1, hcast] at hp
    have hp' : (W N R U m : ℝ) * ((m : ℝ) * ((N : ℝ) - R + m - U)) =
        (W N R U (m - 1) : ℝ) * (((R : ℝ) - m + 1) * ((U : ℝ) - m + 1)) := by
      nlinarith [hp]
    have hprev : (W N R U (m - 1) : ℝ) ≤ W N R U m := by
      exact_mod_cast hmax (m - 1) (by omega)
    have hb : 0 ≤ ((R : ℝ) - m + 1) * ((U : ℝ) - m + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hx := mul_le_mul_of_nonneg_right hprev hb
    rw [← hp'] at hx
    have hy := le_of_mul_le_mul_left hx hposR
    nlinarith [hy]
  · by_cases hmEq : m = U
    · subst m; nlinarith
    have hmLt : m < U := by omega
    have hp := adjacent_cross hR hmR hmLt (by omega : U - m ≤ N - R + 1)
    have hnext : (W N R U (m + 1) : ℝ) ≤ W N R U m := by
      exact_mod_cast hmax (m + 1) (by omega)
    have hd : 0 ≤ (N : ℝ) - R + m + 1 - U := by
      have hc : ((U - m : ℕ) : ℝ) ≤ (N - R : ℕ) := by exact_mod_cast hcell
      rw [Nat.cast_sub hmU, Nat.cast_sub hR] at hc
      linarith
    have hx := mul_le_mul_of_nonneg_right hnext
      (mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) hd)
    have hp' : (W N R U m : ℝ) * (((R : ℝ) - m) * ((U : ℝ) - m)) =
        (W N R U (m + 1) : ℝ) * (((m : ℝ) + 1) * ((N : ℝ) - R + m + 1 - U)) := by
      nlinarith [hp]
    rw [← hp'] at hx
    have hy := le_of_mul_le_mul_left hx hposR
    nlinarith [hy]
/-- A maximizing atom is within two of the mean, including tied modes. -/
private theorem maximizing_near_mean {N R U m : ℕ} (hN : 0 < N)
    (hR : R ≤ N) (hU : U ≤ N) (hmR : m ≤ R) (hmU : m ≤ U)
    (hcell : U - m ≤ N - R) (hpos : 0 < W N R U m)
    (hmax : ∀ t ≤ U, W N R U t ≤ W N R U m) :
    |(m : ℝ) - (U : ℝ) * R / N| ≤ 2 := by
  obtain ⟨hhi, hlo⟩ := maximizing_thresholds hR hU hmR hmU hcell hpos hmax
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hRN : (R : ℝ) ≤ N := by exact_mod_cast hR
  have hUN : (U : ℝ) ≤ N := by exact_mod_cast hU
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmRN : (m : ℝ) ≤ N := by exact_mod_cast hmR.trans hR
  have hmRR : (m : ℝ) ≤ R := by exact_mod_cast hmR
  have hmUR : (m : ℝ) ≤ U := by exact_mod_cast hmU
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  apply abs_le.mpr
  constructor
  · have hmult : (U : ℝ) * R ≤ ((m : ℝ) + 2) * N := by
      nlinarith
    have hh : (U : ℝ) * R / N ≤ (m : ℝ) + 2 := (div_le_iff₀ hN0).mpr hmult
    linarith
  · have hmult : ((m : ℝ) - 2) * N ≤ (U : ℝ) * R := by
      nlinarith
    have hh : (m : ℝ) - 2 ≤ (U : ℝ) * R / N := (le_div_iff₀ hN0).mpr hmult
    linarith
/-- Each atom is at most one under the normalized, support-guarded kernel. -/
private theorem kernel_le_one {N R U t : ℕ} (hR : R ≤ N) (hU : U ≤ N) :
    H N R U t ≤ 1 := by
  by_cases ht : t ≤ U
  · have hs :=
      D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments.kernel_normalization hR hU
    have hl := Finset.single_le_sum (f := H N R U)
      (fun i _ => by dsimp; split_ifs <;> positivity)
      (show t ∈ range (U + 1) by exact mem_range.mpr (by omega))
    exact hl.trans_eq hs
  · simp only [if_neg ht]; norm_num
/-- For a fixed balance parameter, one constant controls every atom of
all hypergeometric tables, uniformly in both margins and population size. -/
theorem hypergeometric_balanced_max_atom (ρ : ℝ) (hρ : 0 < ρ) (hρhi : ρ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R U t : ℕ), 2 ≤ N → R ≤ N → U ≤ N →
      ρ * N ≤ R → (R : ℝ) ≤ (1 - ρ) * N →
      ρ * N ≤ U → (U : ℝ) ≤ (1 - ρ) * N →
      (if t ≤ U then
        ((R.choose t : ℝ) * ((N - R).choose (U - t) : ℝ)) / (N.choose U : ℝ)
      else 0) ≤ C / Real.sqrt N := by
  let C : ℝ := Real.sqrt (4 / ρ ^ 2) + Real.exp 4 / ((ρ ^ 2 / 2) ^ 2)
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N R U t hN hR hU hRlo hRhi hUlo hUhi
  have hNpos : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  by_cases hlarge : 4 / ρ ^ 2 ≤ (N : ℝ)
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range (U + 1))
      (W N R U) (by simp : (range (U + 1)).Nonempty)
    have hmU : m ≤ U := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hmax' : ∀ u ≤ U, W N R U u ≤ W N R U m := by
      intro u hu; exact hmax u (mem_range.mpr (by omega))
    have htmin : U - min R U ≤ N - R := by omega
    have hminpos : 0 < W N R U (min R U) :=
      Nat.mul_pos (Nat.choose_pos (min_le_left _ _)) (Nat.choose_pos htmin)
    have hpos : 0 < W N R U m := hminpos.trans_le (hmax' _ (min_le_right _ _))
    have hmR : m ≤ R := Nat.choose_ne_zero_iff.mp
      (left_ne_zero_of_mul hpos.ne')
    have hcell : U - m ≤ N - R := Nat.choose_ne_zero_iff.mp
      (right_ne_zero_of_mul hpos.ne')
    have hnear := maximizing_near_mean hNpos hR hU hmR hmU hcell hpos hmax'
    have hw : 2 ≤ ρ ^ 2 * (N : ℝ) / 2 := by
      have hh := (div_le_iff₀ hρ2).mp hlarge
      nlinarith
    have hc :=
      D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.hypergeometric_balanced_central_atom
        hNpos hR hU ρ 2 hρ
      hRlo hRhi hUlo hUhi hw hnear
    have hCm : Real.exp 4 / ((ρ ^ 2 / 2) ^ 2) ≤ C := by
      dsimp [C]; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have hfinal : Real.exp 4 / ((ρ ^ 2 / 2) ^ 2 * Real.sqrt N) ≤ C / Real.sqrt N := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right hCm hsqrt.le
    by_cases ht : t ≤ U
    · simp only [if_pos ht]
      have htm : (W N R U t : ℝ) ≤ W N R U m := by exact_mod_cast hmax' t ht
      have hden : (0 : ℝ) ≤ N.choose U := Nat.cast_nonneg _
      have hl := div_le_div_of_nonneg_right htm hden
      simp only [Nat.cast_mul] at hl
      exact hl.trans (hc.trans hfinal)
    · simp only [if_neg ht]; positivity
  · have hsmall : (N : ℝ) ≤ 4 / ρ ^ 2 := le_of_lt (lt_of_not_ge hlarge)
    have hsc := Real.sqrt_le_sqrt hsmall
    have hCt : Real.sqrt (N : ℝ) ≤ C := hsc.trans
      (by dsimp [C]; exact le_add_of_nonneg_right (by positivity))
    have hc : (1 : ℝ) ≤ C / Real.sqrt N := (le_div_iff₀ hsqrt).mpr (by simpa using hCt)
    exact (kernel_le_one hR hU).trans hc
end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
