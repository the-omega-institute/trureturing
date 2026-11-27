/- GID: D5/S3/Analytic/Oscillation/MontgomeryMatchingCap
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryMatchingCap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint close-pair phase defects force a strict Lorentz cap under a conditional row budget. -/

import D5.S3.Analytic.Oscillation.MontgomeryCountUpper
import D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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

def lorentzKernel (d : ℝ) : ℝ := 4 / (4 + d ^ 2)

def phaseResidual (a b : ℝ) : ℝ := 1 - Real.cos (a - b)

def localCopies {J : Type*} (s : Finset J) (gamma : J → ℝ) (u : J) : Finset J :=
  s.filter (fun v => |gamma v - gamma u| ≤ 1)

def finiteLorentzPairSum {J : Type*} (s : Finset J) (gamma : J → ℝ) (t : ℝ) : ℝ :=
  ∑ u ∈ s, ∑ v ∈ s,
    lorentzKernel (gamma u - gamma v) * Real.cos (t * (gamma u - gamma v))

private lemma phaseResidual_nonneg (a b : ℝ) : 0 ≤ phaseResidual a b := by
  exact sub_nonneg.mpr (Real.cos_le_one _)

private lemma phaseResidual_triangle (a b c : ℝ) :
    phaseResidual a c + phaseResidual b c ≥ (1 / 2 : ℝ) * phaseResidual a b := by
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
      2 * (‖za - zc‖ ^ 2 + ‖zc - zb‖ ^ 2) := by
    nlinarith [sq_nonneg (‖za - zc‖ - ‖zc - zb‖)]
  dsimp [za, zb, zc] at hsq hsum
  rw [hnorm a b] at hsq
  rw [hnorm a c, hnorm c b] at hsum
  have hsym : phaseResidual c b = phaseResidual b c := by
    unfold phaseResidual
    rw [show c - b = -(b - c) by ring, Real.cos_neg]
  nlinarith

private lemma lorentzKernel_nonneg (d : ℝ) : 0 ≤ lorentzKernel d := by
  unfold lorentzKernel
  positivity

private lemma lorentzKernel_ge_half {d : ℝ} (hd : |d| ≤ 2) :
    (1 / 2 : ℝ) ≤ lorentzKernel d := by
  unfold lorentzKernel
  have hd2 : d ^ 2 ≤ 4 := by
    have h := (sq_le_sq).2 (show |d| ≤ |(2 : ℝ)| by simpa using hd)
    nlinarith
  apply (le_div_iff₀ (by positivity)).2
  nlinarith

private lemma finite_pair_sum_zero_le {J : Type*} (s : Finset J) (gamma : J → ℝ) (t : ℝ)
    (ρ : ℝ) (hrow : ∀ u ∈ s, ∑ v ∈ s, lorentzKernel (gamma u - gamma v) ≤ ρ) :
    finiteLorentzPairSum s gamma 0 ≤ ρ * s.card := by
  simp only [finiteLorentzPairSum, Real.cos_zero, zero_mul, mul_one]
  calc
    _ ≤ ∑ u ∈ s, ρ := Finset.sum_le_sum (fun u hu => hrow u hu)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private lemma row_pair_defect_lower {J : Type*} (s : Finset J) (gamma : J → ℝ)
    (t : ℝ) (u v : J) (hu : u ∈ s) (hv : v ∈ s)
    (huv : |gamma u - gamma v| ≤ 1) :
    (∑ k ∈ s, lorentzKernel (gamma u - gamma k) * phaseResidual (t * gamma u) (t * gamma k)) +
      (∑ k ∈ s, lorentzKernel (gamma v - gamma k) * phaseResidual (t * gamma v) (t * gamma k)) ≥
      (1 / 4 : ℝ) * (localCopies s gamma u).card *
        phaseResidual (t * gamma u) (t * gamma v) := by
  have hlocal :
      (∑ k ∈ localCopies s gamma u, lorentzKernel (gamma u - gamma k) *
        phaseResidual (t * gamma u) (t * gamma k)) +
        (∑ k ∈ localCopies s gamma u, lorentzKernel (gamma v - gamma k) *
          phaseResidual (t * gamma v) (t * gamma k)) ≥
      (1 / 4 : ℝ) * (localCopies s gamma u).card *
        phaseResidual (t * gamma u) (t * gamma v) := by
    have hterm (k : J) (hk : k ∈ localCopies s gamma u) :
        (1 / 2 : ℝ) * phaseResidual (t * gamma u) (t * gamma k) +
            (1 / 2 : ℝ) * phaseResidual (t * gamma v) (t * gamma k) ≥
          (1 / 4 : ℝ) * phaseResidual (t * gamma u) (t * gamma v) := by
      have hku : |gamma u - gamma k| ≤ 1 := by
        simpa [localCopies, abs_sub_comm] using (Finset.mem_filter.mp hk).2
      have hkv : |gamma v - gamma k| ≤ 2 := by
        have htriangle := abs_sub_le (gamma v) (gamma u) (gamma k)
        have huv' : |gamma v - gamma u| ≤ 1 := by simpa [abs_sub_comm] using huv
        exact htriangle.trans (add_le_add huv' hku |>.trans (by norm_num))
      have hweightu := lorentzKernel_ge_half (d := gamma u - gamma k)
        (hku.trans (by norm_num : (1 : ℝ) ≤ 2))
      have hweightv := lorentzKernel_ge_half (d := gamma v - gamma k) hkv
      have hwu := mul_le_mul_of_nonneg_right hweightu
        (phaseResidual_nonneg (t * gamma u) (t * gamma k))
      have hwv := mul_le_mul_of_nonneg_right hweightv
        (phaseResidual_nonneg (t * gamma v) (t * gamma k))
      nlinarith [hwu, hwv, phaseResidual_triangle (t * gamma u) (t * gamma v) (t * gamma k)]
    calc
      _ ≥ ∑ k ∈ localCopies s gamma u,
          ((1 / 2 : ℝ) * phaseResidual (t * gamma u) (t * gamma k) +
            (1 / 2 : ℝ) * phaseResidual (t * gamma v) (t * gamma k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro k hk
        have hweightu := lorentzKernel_ge_half (d := gamma u - gamma k)
          (by
            have h := (Finset.mem_filter.mp hk).2
            simpa [abs_sub_comm] using h.trans (by norm_num : (1 : ℝ) ≤ 2))
        have hweightv := lorentzKernel_ge_half (d := gamma v - gamma k) (by
          have h := (Finset.mem_filter.mp hk).2
          have htriangle := abs_sub_le (gamma v) (gamma u) (gamma k)
          exact htriangle.trans (add_le_add (by simpa [abs_sub_comm] using huv)
            (by simpa [abs_sub_comm] using h) |>.trans (by norm_num)))
        have hwu := mul_le_mul_of_nonneg_right hweightu
          (phaseResidual_nonneg (t * gamma u) (t * gamma k))
        have hwv := mul_le_mul_of_nonneg_right hweightv
          (phaseResidual_nonneg (t * gamma v) (t * gamma k))
        nlinarith [hwu, hwv, phaseResidual_triangle (t * gamma u) (t * gamma v) (t * gamma k)]
      _ ≥ ∑ _k ∈ localCopies s gamma u,
          (1 / 4 : ℝ) * phaseResidual (t * gamma u) (t * gamma v) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc
    _ ≥ (∑ k ∈ localCopies s gamma u, lorentzKernel (gamma u - gamma k) *
        phaseResidual (t * gamma u) (t * gamma k)) +
        (∑ k ∈ localCopies s gamma u, lorentzKernel (gamma v - gamma k) *
          phaseResidual (t * gamma v) (t * gamma k)) := by
      apply add_le_add
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact (Finset.mem_filter.mp hk).1
        · intro k hk _
          exact mul_nonneg (lorentzKernel_nonneg _) (phaseResidual_nonneg _ _)
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact (Finset.mem_filter.mp hk).1
        · intro k hk _
          exact mul_nonneg (lorentzKernel_nonneg _) (phaseResidual_nonneg _ _)
    _ ≥ _ := hlocal

structure MatchingData (J P : Type*) (s : Finset J) (gamma : J → ℝ) (t : ℝ) where
  pairs : Finset P
  left : P → J
  right : P → J
  left_mem : ∀ p ∈ pairs, left p ∈ s
  right_mem : ∀ p ∈ pairs, right p ∈ s
  left_injective : ∀ ⦃p q : P⦄, p ∈ pairs → q ∈ pairs → left p = left q → p = q
  right_injective : ∀ ⦃p q : P⦄, p ∈ pairs → q ∈ pairs → right p = right q → p = q
  cross_left_right : ∀ ⦃p q : P⦄, p ∈ pairs → q ∈ pairs → left p ≠ right q
  close : ∀ p ∈ pairs, |gamma (left p) - gamma (right p)| ≤ 1

private def owner {J P : Type*} {s : Finset J} {gamma : J → ℝ} {t : ℝ}
    (M : MatchingData J P s gamma t) (q : P × Bool) : J :=
  if q.2 then M.right q.1 else M.left q.1

private lemma owner_injective {J P : Type*} {s : Finset J} {gamma : J → ℝ} {t : ℝ}
    (M : MatchingData J P s gamma t) :
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

private lemma owner_mem {J P : Type*} {s : Finset J} {gamma : J → ℝ} {t : ℝ}
    (M : MatchingData J P s gamma t) {q : P × Bool}
    (hq : q ∈ M.pairs.product (Finset.univ : Finset Bool)) : owner M q ∈ s := by
  rcases q with ⟨p, b⟩
  have hp := (Finset.mem_product.mp hq).1
  fin_cases b
  · change M.right p ∈ s
    exact M.right_mem p hp
  · change M.left p ∈ s
    exact M.left_mem p hp

private lemma selected_sum {J P : Type*} [DecidableEq J] {s : Finset J} {gamma : J → ℝ} {t : ℝ}
    (M : MatchingData J P s gamma t) (f : J → ℝ) :
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
theorem finite_matching_defect {J P : Type*} [DecidableEq J]
    {s : Finset J} {gamma : J → ℝ} {t : ℝ}
    (M : MatchingData J P s gamma t) :
    (1 / 4 : ℝ) * ∑ p ∈ M.pairs,
        (localCopies s gamma (M.left p)).card *
          phaseResidual (t * gamma (M.left p)) (t * gamma (M.right p)) ≤
      finiteLorentzPairSum s gamma 0 - finiteLorentzPairSum s gamma t := by
  classical
  let rowDefect (u : J) := ∑ v ∈ s,
    lorentzKernel (gamma u - gamma v) * phaseResidual (t * gamma u) (t * gamma v)
  let selected : Finset J := (M.pairs.product (Finset.univ : Finset Bool)).image (owner M)
  have hselected : selected ⊆ s := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    exact owner_mem M hq
  have hrow_nonneg (u : J) (hu : u ∈ s) : 0 ≤ rowDefect u := by
    dsimp [rowDefect]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (lorentzKernel_nonneg _) (phaseResidual_nonneg _ _)
  have hdefect_lower :
      (1 / 4 : ℝ) * ∑ p ∈ M.pairs,
        (localCopies s gamma (M.left p)).card *
          phaseResidual (t * gamma (M.left p)) (t * gamma (M.right p)) ≤
      ∑ u ∈ selected, rowDefect u := by
    rw [Finset.mul_sum, selected_sum M rowDefect]
    apply Finset.sum_le_sum
    intro p hp
    have hpair := row_pair_defect_lower s gamma t (M.left p) (M.right p)
      (M.left_mem p hp) (M.right_mem p hp) (M.close p hp)
    dsimp [rowDefect]
    convert hpair using 1 <;> ring
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

private lemma sum_copies {J : Type*} (s : Finset J) (m : J → ℕ) (q : J → ℝ) :
    (∑ p ∈ CutDensity.copies s m, q p.1) =
      ∑ j ∈ s, (m j : ℝ) * q j := by
  rw [CutDensity.copies, Finset.sum_sigma]
  simp [Fintype.card_fin]

private lemma copies_pair_sum {S : Spectrum} {H t : ℝ} :
    finiteLorentzPairSum (CutDensity.copies (S.cut H) S.mult)
      (fun p => S.gamma p.1) t = pairSum S H t := by
  unfold finiteLorentzPairSum pairSum lorentzKernel
  rw [sum_copies (S.cut H) S.mult
    (fun j => ∑ r ∈ CutDensity.copies (S.cut H) S.mult,
      (4 / (4 + (S.gamma j - S.gamma r.1) ^ 2)) *
        Real.cos (t * (S.gamma j - S.gamma r.1)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sum_copies (S.cut H) S.mult (fun k =>
    (4 / (4 + (S.gamma j - S.gamma k) ^ 2)) *
      Real.cos (t * (S.gamma j - S.gamma k)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [D5.S3.Analytic.Oscillation.MontgomeryWindow.pairCos]
  ring

theorem spectrum_matching_defect {S : Spectrum} {P : Type*} {H t ρ : ℝ}
    (M : MatchingData (Σ j : S.index, Fin (S.mult j)) P
      (CutDensity.copies (S.cut H) S.mult) (fun p => S.gamma p.1) t)
    (hrow : ∀ u ∈ CutDensity.copies (S.cut H) S.mult,
      ∑ v ∈ CutDensity.copies (S.cut H) S.mult,
        lorentzKernel (S.gamma u.1 - S.gamma v.1) ≤ ρ) :
    pairSum S H t ≤ ρ * (S.N H : ℝ) - (1 / 4 : ℝ) * ∑ p ∈ M.pairs,
      (localCopies (CutDensity.copies (S.cut H) S.mult)
        (fun q => S.gamma q.1) (M.left p)).card *
          phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1) := by
  classical
  letI := Classical.decEq (Σ j : S.index, Fin (S.mult j))
  have hdefect := finite_matching_defect M
  have hzero := finite_pair_sum_zero_le (CutDensity.copies (S.cut H) S.mult)
    (fun q => S.gamma q.1) t ρ hrow
  simp only [copies_pair_sum] at hdefect hzero
  have hcard : ((CutDensity.copies (S.cut H) S.mult).card : ℝ) = S.N H :=
    copies_card S H
  rw [hcard] at hzero
  linarith [hdefect, hzero]

theorem strict_normalized_cap_of_matching {S : Spectrum} {P : Type*}
    {H t ρ κ η c₁ c₂ c₃ : ℝ}
    (M : MatchingData (Σ j : S.index, Fin (S.mult j)) P
      (CutDensity.copies (S.cut H) S.mult) (fun p => S.gamma p.1) t)
    (hrow : ∀ u ∈ CutDensity.copies (S.cut H) S.mult,
      ∑ v ∈ CutDensity.copies (S.cut H) S.mult,
        lorentzKernel (S.gamma u.1 - S.gamma v.1) ≤ ρ)
    (hH : 1 < H) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hη : 0 ≤ η)
    (hpairs : c₁ * H * Real.log H ≤ (M.pairs.card : ℝ))
    (hres : ∀ p ∈ M.pairs,
      c₂ ≤ phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1))
    (hhood : ∀ p ∈ M.pairs,
      c₃ * Real.log H ≤
        (localCopies (CutDensity.copies (S.cut H) S.mult)
          (fun q => S.gamma q.1) (M.left p)).card)
    (hbase : ρ * (S.N H : ℝ) ≤
      (κ - η + c₁ * c₂ * c₃ / 4) * (H * Real.log H ^ 2))
    (hscale : 0 < H * Real.log H ^ 2) :
    pairSum S H t / (H * Real.log H ^ 2) ≤ κ - η := by
  classical
  letI := Classical.decEq (Σ j : S.index, Fin (S.mult j))
  have hlog : 0 < Real.log H := Real.log_pos hH
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
  have hsum : (c₁ * c₂ * c₃ / 4) * (H * Real.log H ^ 2) ≤
      (1 / 4 : ℝ) * ∑ p ∈ M.pairs,
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
  have hfinite := spectrum_matching_defect M hrow
  have hupper : pairSum S H t ≤
      (κ - η + c₁ * c₂ * c₃ / 4) * (H * Real.log H ^ 2) -
        (c₁ * c₂ * c₃ / 4) * (H * Real.log H ^ 2) := by
    calc
      pairSum S H t ≤ ρ * (S.N H : ℝ) - (1 / 4 : ℝ) * ∑ p ∈ M.pairs,
          (localCopies (CutDensity.copies (S.cut H) S.mult)
            (fun q => S.gamma q.1) (M.left p)).card *
            phaseResidual (t * S.gamma (M.left p).1) (t * S.gamma (M.right p).1) := hfinite
      _ ≤ _ := by nlinarith [hbase, hsum]
  apply (div_le_iff₀ hscale).2
  have hδ : 0 ≤ c₁ * c₂ * c₃ / 4 := by positivity
  nlinarith [mul_nonneg hδ hscale.le]

#print axioms spectrum_matching_defect
#print axioms strict_normalized_cap_of_matching

end

end D5.S3.Analytic.Oscillation.MontgomeryMatchingCap
