/- GID: D5/S3/Analytic/Oscillation/MontgomeryMatchingCap
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryMatchingCap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint close-pair phase defects force a strict Lorentz cap under a zero-phase bound. -/

import D5.S3.Analytic.Oscillation.MontgomeryAutocorrelationLimit
import D5.S3.Analytic.Oscillation.MontgomeryCountUpper
import D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting
import OmegaBuild.Commands

/-! Disjoint close pairs amplify a local phase defect into the ordered Lorentz sum. -/

compile_only_with_mathlib

namespace D5.S3.Analytic.Oscillation.MontgomeryMatchingCap

open Set
open scoped BigOperators

noncomputable section

open D5.S3.Analytic.Oscillation.MontgomeryCountUpper
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting

open D5.S3.Analytic.Oscillation.MontgomeryAutocorrelationLimit (copies_pair_sum)
open D5.S3.Analytic.Oscillation.MontgomeryWindow (pairCos)
open Omega.MeasureTheory.LorentzIntervalMass (kernel kernel_level kernel_nonneg)

def phaseResidual (a b : ℝ) : ℝ := 1 - Real.cos (a - b)

def localCopies {J : Type*} (s : Finset J) (gamma : J → ℝ) (u : J) : Finset J :=
  s.filter (fun v => |gamma v - gamma u| ≤ 1)

def finiteLorentzPairSum {J : Type*} (s : Finset J) (gamma : J → ℝ) (t : ℝ) : ℝ :=
  ∑ u ∈ s, ∑ v ∈ s,
    kernel (gamma u - gamma v) * Real.cos (t * (gamma u - gamma v))

private lemma phaseResidual_nonneg (a b : ℝ) : 0 ≤ phaseResidual a b := by
  exact sub_nonneg.mpr (Real.cos_le_one _)

private lemma weighted_phaseResidual_triangle (a b c : ℝ) :
    (4 / 5 : ℝ) * phaseResidual a c + (1 / 2 : ℝ) * phaseResidual b c ≥
      (4 / 13 : ℝ) * phaseResidual a b := by
  let za : ℂ := Complex.exp ((a : ℂ) * Complex.I)
  let zb : ℂ := Complex.exp ((b : ℂ) * Complex.I)
  let zc : ℂ := Complex.exp ((c : ℂ) * Complex.I)
  have hnorm (x y : ℝ) :
      ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ^ 2 =
        2 * phaseResidual x y := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    have hx : Complex.normSq (Complex.exp ((x : ℂ) * Complex.I)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      norm_num
    have hy : Complex.normSq (Complex.exp ((y : ℂ) * Complex.I)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      norm_num
    have hxy :
        (Complex.exp ((x : ℂ) * Complex.I) *
          (starRingEnd ℂ) (Complex.exp ((y : ℂ) * Complex.I))).re = Real.cos (x-y) := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      rw [show (x : ℂ) * Complex.I + (starRingEnd ℂ) ((y : ℂ) * Complex.I) =
        ((x-y : ℝ) : ℂ) * Complex.I by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        ring]
      exact Complex.exp_ofReal_mul_I_re _
    rw [hx, hy, hxy]
    dsimp [phaseResidual]
    ring
  have htri : ‖za - zb‖ ≤ ‖za - zc‖ + ‖zc - zb‖ := by
    calc
      ‖za - zb‖ = ‖(za - zc) + (zc - zb)‖ := by ring_nf
      _ ≤ ‖za - zc‖ + ‖zc - zb‖ := norm_add_le _ _
  have hsq : ‖za - zb‖ ^ 2 ≤ (‖za - zc‖ + ‖zc - zb‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
  have hsum : (‖za - zc‖ + ‖zc - zb‖) ^ 2 ≤
      (13 / 4 : ℝ) * ((4 / 5 : ℝ) * ‖za - zc‖ ^ 2 + (1 / 2 : ℝ) * ‖zc - zb‖ ^ 2) := by
    nlinarith [sq_nonneg (8 * ‖za - zc‖ - 5 * ‖zc - zb‖)]
  dsimp [za, zb, zc] at hsq hsum
  rw [hnorm a b] at hsq
  rw [hnorm a c, hnorm c b] at hsum
  have hsym : phaseResidual c b = phaseResidual b c := by
    unfold phaseResidual
    rw [show c - b = -(b - c) by ring, Real.cos_neg]
  rw [hsym] at hsum
  linarith only [hsq, hsum]

private lemma kernel_ge_four_fifths {d : ℝ} (hd : |d| ≤ 1) :
    (4 / 5 : ℝ) ≤ kernel d := by
  have hradius : 2 * Real.sqrt (1 / (4 / 5 : ℝ) - 1) = 1 := by
    rw [show 1 / (4 / 5 : ℝ) - 1 = 1 / 4 by norm_num,
      Real.sqrt_div (by norm_num) 4, Real.sqrt_one,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  change d ∈ {x : ℝ | (4 / 5 : ℝ) ≤ kernel x}
  rw [kernel_level (by norm_num) (by norm_num), hradius]
  exact abs_le.mp hd

private lemma kernel_ge_half {d : ℝ} (hd : |d| ≤ 2) :
    (1 / 2 : ℝ) ≤ kernel d := by
  have hradius : 2 * Real.sqrt (1 / (1 / 2 : ℝ) - 1) = 2 := by
    rw [show 1 / (1 / 2 : ℝ) - 1 = 1 by norm_num, Real.sqrt_one, mul_one]
  change d ∈ {x : ℝ | (1 / 2 : ℝ) ≤ kernel x}
  rw [kernel_level (by norm_num) (by norm_num), hradius]
  exact abs_le.mp hd

private lemma row_pair_defect_lower {J : Type*} (s : Finset J) (gamma : J → ℝ)
    (t : ℝ) (u v : J)
    (huv : |gamma u - gamma v| ≤ 1) :
    (∑ k ∈ s, kernel (gamma u - gamma k) * phaseResidual (t * gamma u) (t * gamma k)) +
      (∑ k ∈ s, kernel (gamma v - gamma k) * phaseResidual (t * gamma v) (t * gamma k)) ≥
      (4 / 13 : ℝ) * (localCopies s gamma u).card *
        phaseResidual (t * gamma u) (t * gamma v) := by
  have hlocal :
      (∑ k ∈ localCopies s gamma u, kernel (gamma u - gamma k) *
        phaseResidual (t * gamma u) (t * gamma k)) +
        (∑ k ∈ localCopies s gamma u, kernel (gamma v - gamma k) *
          phaseResidual (t * gamma v) (t * gamma k)) ≥
      (4 / 13 : ℝ) * (localCopies s gamma u).card *
        phaseResidual (t * gamma u) (t * gamma v) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ ≥ ∑ _k ∈ localCopies s gamma u,
          (4 / 13 : ℝ) * phaseResidual (t * gamma u) (t * gamma v) := by
        apply Finset.sum_le_sum
        intro k hk
        have hku : |gamma u - gamma k| ≤ 1 := by
          simpa [localCopies, abs_sub_comm] using (Finset.mem_filter.mp hk).2
        have hkv : |gamma v - gamma k| ≤ 2 := by
          have htriangle := abs_sub_le (gamma v) (gamma u) (gamma k)
          have huv' : |gamma v - gamma u| ≤ 1 := by simpa [abs_sub_comm] using huv
          exact htriangle.trans (add_le_add huv' hku |>.trans (by norm_num))
        have hwu := mul_le_mul_of_nonneg_right
          (kernel_ge_four_fifths hku)
          (phaseResidual_nonneg (t * gamma u) (t * gamma k))
        have hwv := mul_le_mul_of_nonneg_right (kernel_ge_half hkv)
          (phaseResidual_nonneg (t * gamma v) (t * gamma k))
        exact (weighted_phaseResidual_triangle (t * gamma u) (t * gamma v) (t * gamma k)).trans
          (add_le_add hwu hwv)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc
    _ ≥ (∑ k ∈ localCopies s gamma u, kernel (gamma u - gamma k) *
        phaseResidual (t * gamma u) (t * gamma k)) +
        (∑ k ∈ localCopies s gamma u, kernel (gamma v - gamma k) *
          phaseResidual (t * gamma v) (t * gamma k)) := by
      apply add_le_add
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact (Finset.mem_filter.mp hk).1
        · intro k hk _
          apply mul_nonneg
          · exact kernel_nonneg _
          · exact phaseResidual_nonneg _ _
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact (Finset.mem_filter.mp hk).1
        · intro k hk _
          apply mul_nonneg
          · exact kernel_nonneg _
          · exact phaseResidual_nonneg _ _
    _ ≥ _ := hlocal

structure MatchingData (J P : Type*) (s : Finset J) (gamma : J → ℝ) where
  pairs : Finset P
  left : P → J
  right : P → J
  left_mem : ∀ p ∈ pairs, left p ∈ s
  right_mem : ∀ p ∈ pairs, right p ∈ s
  left_injective : ∀ ⦃p q : P⦄, p ∈ pairs → q ∈ pairs → left p = left q → p = q
  right_injective : ∀ ⦃p q : P⦄, p ∈ pairs → q ∈ pairs → right p = right q → p = q
  cross_left_right : ∀ ⦃p q : P⦄, p ∈ pairs → q ∈ pairs → left p ≠ right q
  close : ∀ p ∈ pairs, |gamma (left p) - gamma (right p)| ≤ 1

private def owner {J P : Type*} {s : Finset J} {gamma : J → ℝ}
    (M : MatchingData J P s gamma) (q : P × Bool) : J :=
  if q.2 then M.right q.1 else M.left q.1

private lemma owner_injective {J P : Type*} {s : Finset J} {gamma : J → ℝ}
    (M : MatchingData J P s gamma) :
    Set.InjOn (owner M) (↑(M.pairs.product (Finset.univ : Finset Bool))) := by
  intro x hx y hy heq
  rcases x with ⟨p, b⟩
  rcases y with ⟨q, c⟩
  have hp : p ∈ M.pairs := (Finset.mem_product.mp hx).1
  have hq : q ∈ M.pairs := (Finset.mem_product.mp hy).1
  simp only [owner] at heq
  fin_cases b <;> fin_cases c
  · change M.right p = M.right q at heq
    exact Prod.ext (M.right_injective hp hq heq) rfl
  · change M.right p = M.left q at heq
    exact False.elim (M.cross_left_right hq hp heq.symm)
  · change M.left p = M.right q at heq
    exact False.elim (M.cross_left_right hp hq heq)
  · change M.left p = M.left q at heq
    exact Prod.ext (M.left_injective hp hq heq) rfl

private lemma owner_mem {J P : Type*} {s : Finset J} {gamma : J → ℝ}
    (M : MatchingData J P s gamma) {q : P × Bool}
    (hq : q ∈ M.pairs.product (Finset.univ : Finset Bool)) : owner M q ∈ s := by
  rcases q with ⟨p, b⟩
  have hp := (Finset.mem_product.mp hq).1
  fin_cases b
  · change M.right p ∈ s
    exact M.right_mem p hp
  · change M.left p ∈ s
    exact M.left_mem p hp

private lemma selected_sum {J P : Type*} [DecidableEq J] {s : Finset J} {gamma : J → ℝ}
    (M : MatchingData J P s gamma) (f : J → ℝ) :
    (∑ u ∈ (M.pairs.product (Finset.univ : Finset Bool)).image (owner M), f u) =
      ∑ p ∈ M.pairs, (f (M.left p) + f (M.right p)) := by
  classical
  rw [Finset.sum_image (owner_injective M)]
  change (∑ x ∈ M.pairs ×ˢ (Finset.univ : Finset Bool), f (owner M x)) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  simp [owner]
  ring

/-- Disjoint endpoint rows amplify their phase deficits by the local copy count. -/
theorem finite_matching_defect {J P : Type*}
    {s : Finset J} {gamma : J → ℝ} {t : ℝ}
    (M : MatchingData J P s gamma) :
    (4 / 13 : ℝ) * ∑ p ∈ M.pairs,
        (localCopies s gamma (M.left p)).card *
          phaseResidual (t * gamma (M.left p)) (t * gamma (M.right p)) ≤
      finiteLorentzPairSum s gamma 0 - finiteLorentzPairSum s gamma t := by
  classical
  let rowDefect (u : J) := ∑ v ∈ s,
    kernel (gamma u - gamma v) * phaseResidual (t * gamma u) (t * gamma v)
  let selected : Finset J := (M.pairs.product (Finset.univ : Finset Bool)).image (owner M)
  have hselected : selected ⊆ s := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    exact owner_mem M hq
  have hrow_nonneg (u : J) (hu : u ∈ s) : 0 ≤ rowDefect u := by
    dsimp [rowDefect]
    apply Finset.sum_nonneg
    intro v hv
    apply mul_nonneg
    · exact kernel_nonneg _
    · exact phaseResidual_nonneg _ _
  have hdefect_lower :
      (4 / 13 : ℝ) * ∑ p ∈ M.pairs,
        (localCopies s gamma (M.left p)).card *
          phaseResidual (t * gamma (M.left p)) (t * gamma (M.right p)) ≤
      ∑ u ∈ selected, rowDefect u := by
    rw [Finset.mul_sum, selected_sum M rowDefect]
    apply Finset.sum_le_sum
    intro p hp
    have hpair := row_pair_defect_lower s gamma t (M.left p) (M.right p)
      (M.close p hp)
    dsimp [rowDefect]
    convert hpair using 1
    ring
  have hselected_le : ∑ u ∈ selected, rowDefect u ≤ ∑ u ∈ s, rowDefect u :=
    Finset.sum_le_sum_of_subset_of_nonneg hselected
      (fun u hu _ => hrow_nonneg u hu)
  have htotal : finiteLorentzPairSum s gamma 0 - finiteLorentzPairSum s gamma t =
      ∑ u ∈ s, rowDefect u := by
    unfold finiteLorentzPairSum
    dsimp [rowDefect]
    simp only [Real.cos_zero, zero_mul, mul_one, phaseResidual]
    simp_rw [show ∀ u v : J, t * gamma u - t * gamma v =
      t * (gamma u - gamma v) by intros; ring]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [htotal]
  exact hdefect_lower.trans hselected_le

#print axioms finite_matching_defect

open D5.S3.Analytic.Oscillation.MontgomeryCountUpper (pairSum)

private lemma copies_lorentz_pair_sum {S : Spectrum} {H t : ℝ} :
    finiteLorentzPairSum (CutDensity.copies (S.cut H) S.mult)
      (fun p => S.gamma p.1) t = pairSum S H t := by
  simpa only [finiteLorentzPairSum, pairSum, pairCos, kernel, mul_comm t] using
    (copies_pair_sum S H (fun j k => pairCos (S.gamma j - S.gamma k) t))

/-- The finite matching deficit for the ordered spectrum sum with multiplicities. -/
theorem spectrum_matching_defect {S : Spectrum} {P : Type*} {H t : ℝ}
    (M : MatchingData (Σ j : S.index, Fin (S.mult j)) P
      (CutDensity.copies (S.cut H) S.mult) (fun p => S.gamma p.1)) :
    (4 / 13 : ℝ) * ∑ p ∈ M.pairs,
      (localCopies (CutDensity.copies (S.cut H) S.mult)
        (fun q => S.gamma q.1) (M.left p)).card *
          phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1) ≤
      pairSum S H 0 - pairSum S H t := by
  simpa only [copies_lorentz_pair_sum] using (finite_matching_defect (t := t) M)

theorem strict_normalized_cap_of_matching {S : Spectrum} {P : Type*}
    {H t κ η c₁ c₂ c₃ : ℝ}
    (M : MatchingData (Σ j : S.index, Fin (S.mult j)) P
      (CutDensity.copies (S.cut H) S.mult) (fun p => S.gamma p.1))
    (hH : 1 < H) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hpairs : c₁ * H * Real.log H ≤ (M.pairs.card : ℝ))
    (hres : ∀ p ∈ M.pairs,
      c₂ ≤ phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1))
    (hhood : ∀ p ∈ M.pairs,
      c₃ * Real.log H ≤
        (localCopies (CutDensity.copies (S.cut H) S.mult)
          (fun q => S.gamma q.1) (M.left p)).card)
    (hbase : pairSum S H 0 ≤
      (κ - η + 4 * c₁ * c₂ * c₃ / 13) * (H * Real.log H ^ 2)) :
    pairSum S H t / (H * Real.log H ^ 2) ≤ κ - η := by
  classical
  have hlog : 0 < Real.log H := Real.log_pos hH
  have hheight : 0 < H := lt_trans zero_lt_one hH
  have hscale : 0 < H * Real.log H ^ 2 := by positivity
  have hterm (p : P) (hp : p ∈ M.pairs) :
      c₂ * (c₃ * Real.log H) ≤
        (localCopies (CutDensity.copies (S.cut H) S.mult)
          (fun q => S.gamma q.1) (M.left p)).card *
          phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1) := by
    have hcard := hhood p hp
    have hphase := hres p hp
    have hcard0 : (0 : ℝ) ≤
        ((localCopies (CutDensity.copies (S.cut H) S.mult)
          (fun q => S.gamma q.1) (M.left p)).card : ℝ) := by positivity
    have hphase0 := phaseResidual_nonneg (t * S.gamma (M.left p).1)
      (t * S.gamma (M.right p).1)
    have hleft := mul_le_mul_of_nonneg_left hcard hc₂
    have hright := mul_le_mul_of_nonneg_right hphase hcard0
    nlinarith
  have hsum : (4 * c₁ * c₂ * c₃ / 13) * (H * Real.log H ^ 2) ≤
      (4 / 13 : ℝ) * ∑ p ∈ M.pairs,
        (localCopies (CutDensity.copies (S.cut H) S.mult)
          (fun q => S.gamma q.1) (M.left p)).card *
          phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1) := by
    have hsum' := Finset.sum_le_sum (fun p hp => hterm p hp)
    have hcard := hpairs
    have hnonneg : 0 ≤ c₂ * (c₃ * Real.log H) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hpairs hnonneg
    have hraw : c₁ * c₂ * c₃ * (H * Real.log H ^ 2) ≤
        ∑ p ∈ M.pairs,
          (localCopies (CutDensity.copies (S.cut H) S.mult)
            (fun q => S.gamma q.1) (M.left p)).card *
            phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1) := by
      calc
        _ = (c₁ * H * Real.log H) * (c₂ * (c₃ * Real.log H)) := by ring
        _ ≤ (M.pairs.card : ℝ) * (c₂ * (c₃ * Real.log H)) := hmul
        _ ≤ _ := by simpa [Finset.sum_const, nsmul_eq_mul] using hsum'
    nlinarith [hraw]
  have hfinite := spectrum_matching_defect (t := t) M
  apply (div_le_iff₀ hscale).2
  nlinarith only [hfinite, hbase, hsum]

#print axioms spectrum_matching_defect
#print axioms strict_normalized_cap_of_matching

end

end D5.S3.Analytic.Oscillation.MontgomeryMatchingCap
