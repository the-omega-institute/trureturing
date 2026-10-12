/- GID: D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native common-root feedback and arithmetic small-ball bounds use the same full environment. -/
import D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
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
    have hc : (S.card : ℝ) ≤ ((Icc a b).card : ℝ) := by exact_mod_cast card_le_card hsub
    have hi : ((Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by exact_mod_cast Int.card_Icc_of_le a b (by omega : a ≤ b + 1)
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
      unfold eventMass; exact (sum_le_sum fun t ht => hmax t (mem_filter.mp ht).1).trans_eq
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
  have hyb : (y : ℝ) ≤ b := hycast.trans (Int.floor_le b)
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
    dsimp [Z] at *; linarith
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
      have hat : (0 : ℝ) ≤ ((t - a : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr (mem_Icc.mp hti).1
      have htb : (0 : ℝ) ≤ ((b - t : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr (mem_Icc.mp hti).2
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
      rw [← sum_union_inter]; exact le_add_of_nonneg_right (sum_nonneg (fun t _ => hp t))
    exact hpart.trans hu
  have hc := arithmetic_central_mass_bound p g I Z s h A hs hnonneg hA hmax hlower
  have hzbound : A * (Z.card : ℝ) * (2 * h / s + 1) ≤
      A * (K * s * ((b - a : ℤ) : ℝ) + 2 * h + 1) * (2 * h / s + 1) := by
    gcongr
  exact hm.trans (add_le_add (hc.trans hzbound) htail)
end
end D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
set_option maxHeartbeats 800000
namespace D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
noncomputable section
/-- Coarse Stirling envelopes used only inside the four-cell atom estimate. -/
private theorem four_cell_entropy (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a+b) * Real.log (a+b) + (c+d) * Real.log (c+d) +
      (a+c) * Real.log (a+c) + (b+d) * Real.log (b+d) -
      (a+b+c+d) * Real.log (a+b+c+d) -
      a * Real.log a - b * Real.log b - c * Real.log c - d * Real.log d ≤ 0 := by
  let N := a+b+c+d
  have hN : 0 < N := by dsimp [N]; positivity
  let A : Fin 4 → ℝ := ![a,b,c,d]
  let B : Fin 4 → ℝ := ![(a+b)*(a+c)/N, (a+b)*(b+d)/N, (c+d)*(a+c)/N, (c+d)*(b+d)/N]
  have hA (i : Fin 4) : 0 < A i := by fin_cases i <;> simp [A] <;> assumption
  have hB (i : Fin 4) : 0 < B i := by fin_cases i <;> simp [B] <;> positivity
  have hAs : (∑ i, A i) = N := by simp [A, Fin.sum_univ_four, N]
  have hBs : (∑ i, B i) = N := by
    simp [B, Fin.sum_univ_four]
    field_simp
    dsimp [N]; ring
  have h := D5.S3.DivergenceSupport.LogSumInequality.log_sum_inequality A B (fun i => (hA i).le) (fun i => (hB i).le)
    (fun i hi => False.elim ((hB i).ne' hi))
  rw [hAs, hBs, div_self hN.ne', Real.log_one, mul_zero] at h; simp [A, B, Fin.sum_univ_four] at h
  simp (disch := positivity) only [Real.log_div, Real.log_mul] at h
  dsimp [N] at h; linarith only [h]
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
    dsimp [H]; exact div_pos (mul_pos (by exact_mod_cast Nat.choose_pos htR.le)
      (by exact_mod_cast Nat.choose_pos hfour.le)) (by exact_mod_cast Nat.choose_pos hU)
  have hlogH : Real.log H = Real.log (R.factorial : ℝ) + Real.log ((N-R).factorial : ℝ) +
      Real.log (U.factorial : ℝ) + Real.log ((N-U).factorial : ℝ) -
      Real.log (N.factorial : ℝ) - Real.log (t.factorial : ℝ) -
      Real.log ((R-t).factorial : ℝ) - Real.log ((U-t).factorial : ℝ) -
      Real.log ((N-R-(U-t)).factorial : ℝ) := by
    dsimp [H]
    rw [Nat.cast_choose ℝ htR.le, Nat.cast_choose ℝ hfour.le, Nat.cast_choose ℝ hU]
    simp (disch := positivity) only [Real.log_mul, Real.log_div]; ring
  have hent := four_cell_entropy (t : ℝ) ((R-t : ℕ) : ℝ) ((U-t : ℕ) : ℝ) ((N-R-(U-t) : ℕ) : ℝ) ht0 hRt0 hUt0 hD0
  have hAB : (t : ℝ) + (R-t : ℕ) = R := by exact_mod_cast Nat.add_sub_of_le htR.le
  have hCD : ((U-t : ℕ) : ℝ) + (N-R-(U-t) : ℕ) = (N-R : ℕ) := by exact_mod_cast Nat.add_sub_of_le hfour.le
  have hAC : (t : ℝ) + (U-t : ℕ) = U := by exact_mod_cast Nat.add_sub_of_le htU.le
  have hBD : ((R-t : ℕ) : ℝ) + (N-R-(U-t) : ℕ) = (N-U : ℕ) := by exact_mod_cast (by omega : R-t+(N-R-(U-t)) = N-U)
  have hAll : (t : ℝ) + (R-t : ℕ) + (U-t : ℕ) + (N-R-(U-t) : ℕ) = N := by
    exact_mod_cast (by omega : t+(R-t)+(U-t)+(N-R-(U-t)) = N)
  rw [hAll, hAB, hCD, hAC, hBD] at hent
  have hlogupper : Real.log H ≤ 4 + (Real.log R + Real.log (N-R : ℕ) + Real.log U + Real.log (N-U : ℕ) -
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
    rw [show 4 - 2 * Real.log γ - Real.log (N : ℝ) / 2 = 4 - (Real.log (γ ^ 2) + Real.log (Real.sqrt (N : ℝ))) by
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
  have hc := central_four_cells_lower (N : ℝ) R U δ t w hN0 hδ.le hRlo hRhi hUlo hUhi ht
  have hγ : 0 < δ ^ 2 / 2 := by positivity
  have hγN : 0 < δ ^ 2 / 2 * (N : ℝ) := mul_pos hγ hN0
  have hs (j : Fin 4) : δ ^ 2 / 2 * (N : ℝ) ≤ cellCounts N R U t j := by
    have hj := hc j
    linarith
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  simp only [cellCounts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
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
        apply hypergeometric_balanced_central_atom (by omega : 0 < N) hR hU δ w hδ hRlo hRhi hUlo hUhi hsmall
        have hcast : (t.toNat : ℝ) = (t : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ht0
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
    rw [hcentral]; simp only [Int.cast_natCast, not_le]
  have htail : eventMass p (T \ Icc a b) ≤ 1/(4*L^2) := by
    rw [hout, eventMass, sum_map]; simp only [Nat.castEmbedding_apply, hpc]
    exact kernel_central_tail hR hU hN L hL
  have he := moving_center_small_ball p g g T a b s K h 0 A (1/(4*L^2)) hab hs hh
    le_rfl hA hp hmax hlower hupper (fun t _ => by simp) htail
  have hleft : eventMass p (T.filter fun t => ∃ z : ℤ, |g t-z| ≤ h) =
      ∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g (t : ℤ)-z| ≤ h), H N R U t := by
    rw [eventMass, filter_map, sum_map]; simp only [Function.comp_apply, Nat.castEmbedding_apply, hpc]
  rw [hleft] at he
  have hwidth : ((b-a : ℤ) : ℝ) ≤ 2*w := by
    have ha := Int.le_ceil (ν-w)
    have hb := Int.floor_le (ν+w)
    dsimp [a,b]
    push_cast
    linarith
  calc
    _ ≤ A * (K*s*((b-a : ℤ) : ℝ)+2*h+1)*(2*h/s+1)+1/(4*L^2) := by simpa only [add_zero] using he
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
        ((N - R).choose (U - t - 1) : ℝ) * ((N - R - (U - t - 1) : ℕ) : ℝ) := by exact_mod_cast hb
    rw [Nat.cast_sub htU.le, Nat.cast_sub hc, Nat.cast_sub hR, Nat.cast_sub (by omega : 1 ≤ U - t), Nat.cast_sub htU.le] at hb'
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
    have hp := adjacent_cross hR (by omega : m - 1 ≤ R) (by omega : m - 1 < U) (by omega : U - (m - 1) ≤ N - R + 1)
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1]; norm_num
    rw [Nat.sub_add_cancel hm1, hcast] at hp
    have hp' : (W N R U m : ℝ) * ((m : ℝ) * ((N : ℝ) - R + m - U)) =
        (W N R U (m - 1) : ℝ) * (((R : ℝ) - m + 1) * ((U : ℝ) - m + 1)) := by nlinarith [hp]
    have hprev : (W N R U (m - 1) : ℝ) ≤ W N R U m := by exact_mod_cast hmax (m - 1) (by omega)
    have hb : 0 ≤ ((R : ℝ) - m + 1) * ((U : ℝ) - m + 1) := mul_nonneg (by linarith) (by linarith)
    have hx := mul_le_mul_of_nonneg_right hprev hb
    rw [← hp'] at hx
    have hy := le_of_mul_le_mul_left hx hposR
    nlinarith [hy]
  · by_cases hmEq : m = U
    · subst m; nlinarith
    have hmLt : m < U := by omega
    have hp := adjacent_cross hR hmR hmLt (by omega : U - m ≤ N - R + 1)
    have hnext : (W N R U (m + 1) : ℝ) ≤ W N R U m := by exact_mod_cast hmax (m + 1) (by omega)
    have hd : 0 ≤ (N : ℝ) - R + m + 1 - U := by
      have hc : ((U - m : ℕ) : ℝ) ≤ (N - R : ℕ) := by exact_mod_cast hcell
      rw [Nat.cast_sub hmU, Nat.cast_sub hR] at hc; linarith
    have hx := mul_le_mul_of_nonneg_right hnext (mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) hd)
    have hp' : (W N R U m : ℝ) * (((R : ℝ) - m) * ((U : ℝ) - m)) =
        (W N R U (m + 1) : ℝ) * (((m : ℝ) + 1) * ((N : ℝ) - R + m + 1 - U)) := by nlinarith [hp]
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
  · have hmult : (U : ℝ) * R ≤ ((m : ℝ) + 2) * N := by nlinarith
    have hh : (U : ℝ) * R / N ≤ (m : ℝ) + 2 := (div_le_iff₀ hN0).mpr hmult
    linarith
  · have hmult : ((m : ℝ) - 2) * N ≤ (U : ℝ) * R := by nlinarith
    have hh : (m : ℝ) - 2 ≤ (U : ℝ) * R / N := (le_div_iff₀ hN0).mpr hmult
    linarith
/-- Each atom is at most one under the normalized, support-guarded kernel. -/
private theorem kernel_le_one {N R U t : ℕ} (hR : R ≤ N) (hU : U ≤ N) :
    H N R U t ≤ 1 := by
  by_cases ht : t ≤ U
  · have hs := D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments.kernel_normalization hR hU
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
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range (U + 1)) (W N R U) (by simp : (range (U + 1)).Nonempty)
    have hmU : m ≤ U := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hmax' : ∀ u ≤ U, W N R U u ≤ W N R U m := by intro u hu; exact hmax u (mem_range.mpr (by omega))
    have htmin : U - min R U ≤ N - R := by omega
    have hminpos : 0 < W N R U (min R U) := Nat.mul_pos (Nat.choose_pos (min_le_left _ _)) (Nat.choose_pos htmin)
    have hpos : 0 < W N R U m := hminpos.trans_le (hmax' _ (min_le_right _ _))
    have hmR : m ≤ R := Nat.choose_ne_zero_iff.mp (left_ne_zero_of_mul hpos.ne')
    have hcell : U - m ≤ N - R := Nat.choose_ne_zero_iff.mp (right_ne_zero_of_mul hpos.ne')
    have hnear := maximizing_near_mean hNpos hR hU hmR hmU hcell hpos hmax'
    have hw : 2 ≤ ρ ^ 2 * (N : ℝ) / 2 := by
      have hh := (div_le_iff₀ hρ2).mp hlarge
      nlinarith
    have hc := D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.hypergeometric_balanced_central_atom hNpos hR hU ρ 2 hρ
      hRlo hRhi hUlo hUhi hw hnear
    have hCm : Real.exp 4 / ((ρ ^ 2 / 2) ^ 2) ≤ C := by dsimp [C]; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have hfinal : Real.exp 4 / ((ρ ^ 2 / 2) ^ 2 * Real.sqrt N) ≤ C / Real.sqrt N := by
      rw [← div_div]; exact div_le_div_of_nonneg_right hCm hsqrt.le
    by_cases ht : t ≤ U
    · simp only [if_pos ht]
      have htm : (W N R U t : ℝ) ≤ W N R U m := by exact_mod_cast hmax' t ht
      have hden : (0 : ℝ) ≤ N.choose U := Nat.cast_nonneg _
      have hl := div_le_div_of_nonneg_right htm hden
      simp only [Nat.cast_mul] at hl; exact hl.trans (hc.trans hfinal)
    · simp only [if_neg ht]; positivity
  · have hsmall : (N : ℝ) ≤ 4 / ρ ^ 2 := le_of_lt (lt_of_not_ge hlarge)
    have hsc := Real.sqrt_le_sqrt hsmall
    have hCt : Real.sqrt (N : ℝ) ≤ C := hsc.trans (by dsimp [C]; exact le_add_of_nonneg_right (by positivity))
    have hc : (1 : ℝ) ≤ C / Real.sqrt N := (le_div_iff₀ hsqrt).mpr (by simpa using hCt)
    exact (kernel_le_one hR hU).trans hc
end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
open D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
open D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
namespace D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
noncomputable section
set_option maxHeartbeats 800000 in
private theorem anchor_scale_budget (N q v a γ xStar : ℝ)
    (hN : 0 < N) (hq : 0 < q) (hv : 0 < v) (ha : 0 < a)
    (hγ1 : γ ≤ 1/2) (hγa : γ ≤ a*v/32)
    (hlarge : max 4 (32/(a*v)) ≤ Real.sqrt N)
    (hsize : N/q ≤ v/2) (hsize' : N/q ≤ v*Real.log 2/8)
    (hx : |xStar| ≤ a*N/(4*q)) :
    γ*N+2*Real.sqrt N ≤ v*q/2 ∧
      2*(γ*N+2*Real.sqrt N) ≤ v*q/4*Real.log 2 ∧
      |xStar|+8*(γ*N+2*Real.sqrt N)/(v*q) ≤ a*N/q := by
  have hs := Real.sq_sqrt hN.le
  have hs0 := Real.sqrt_nonneg N
  have hs4 : 4 ≤ Real.sqrt N := (le_max_left _ _).trans hlarge
  have hsav : 32/(a*v) ≤ Real.sqrt N := (le_max_right _ _).trans hlarge
  have hw : γ*N+2*Real.sqrt N ≤ N := by nlinarith only [hs,hs4,hγ1,hN]
  have hqsize := (div_le_iff₀ hq).mp hsize
  have hqsize' := (div_le_iff₀ hq).mp hsize'
  have hroot : 8*(γ*N+2*Real.sqrt N)/(v*q) ≤ 3*a*N/(4*q) := by
    apply (div_le_div_iff₀ (mul_pos hv hq) (by positivity : (0 : ℝ) < 4*q)).mpr
    have hg := mul_le_mul_of_nonneg_right hγa hN.le
    have hs' := (div_le_iff₀ (mul_pos ha hv)).mp hsav
    have hs'' := mul_le_mul_of_nonneg_right hs' hs0
    have hsbound : 32*Real.sqrt N ≤ N*a*v := by
      calc
        _ ≤ Real.sqrt N*a*v*Real.sqrt N := by simpa only [mul_assoc] using hs''
        _ = N*a*v := by rw [show Real.sqrt N*a*v*Real.sqrt N = (Real.sqrt N)^2*a*v by ring,hs]
    have hh : 8*(γ*N+2*Real.sqrt N) ≤ 3*a*N*v/4 := by nlinarith only [hg,hsbound]
    have hh' := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith only [hh']
  refine ⟨?_,?_,?_⟩
  · linarith only [hw,hqsize]
  · linarith only [hw,hqsize']
  · have he : a*N/(4*q)+3*a*N/(4*q) = a*N/q := by field_simp; ring
    linarith only [hx,hroot,he]
set_option maxHeartbeats 800000 in
/-- The native outside function and anchor are taken from one actual
collapsed fiber. The same full calibration curve is used at every real
central histogram, in either experiment; no posterior is reconditioned. -/
theorem native_anchored_central_feedback (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (v : ℝ) (hv : 0 < v) :
    ∃ a γ η c C : ℝ, 0 < a ∧ 0 < γ ∧ 0 < η ∧ 0 < c ∧ 0 < C ∧
    ∀ (M q s : ℕ) (S : Support M q) (e : Experiment) (o : Obs M s e),
    ∀ [Fintype (Sites s e)], ∀ (k l : ℕ) (z : Fiber S e o),
      1 ≤ q → q < M → 0 ≤ compensation M q r → compensation M q r < 1 →
      let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+ (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
      let V := nativeRectangleRows S e o k l z
      let N : ℝ := V.card
      let R : ℝ := (V.filter fun i => count e z.val i.val 1 = k).card
      let U : ℝ := (V.filter fun i => count e z.val i.val (-1) = l).card
      let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val-z0
      0 < N → N/4 ≤ R → R ≤ 3*N/4 → N/4 ≤ U → U ≤ 3*N/4 →
      max 4 (32/(a*v)) ≤ Real.sqrt N →
      N/q ≤ v/2 → N/q ≤ v*Real.log 2/8 → a*N/q < η →
      |compensation M q r| < η →
      ∀ bg : ℝ, 0 ≤ bg → bg ≤ N →
      ∀ (anchor : Fiber S e o) (xStar : ℝ),
        nativeMinimalRectangleReadout S e o k l anchor =
          nativeMinimalRectangleReadout S e o k l z →
        (∑ i : Fin M, Real.sigmoid (xStar+(score q r e anchor.val i-z0))) = q →
        v*q ≤ ∑ i : Fin M, Real.sigmoid (xStar+(score q r e anchor.val i-z0))*
          (1-Real.sigmoid (xStar+(score q r e anchor.val i-z0))) →
        |xStar| ≤ a*N/(4*q) →
        |(nativeRectangleACount S e o k l anchor : ℝ)-U*R/N| ≤ 2*Real.sqrt N →
        ∃ θ : ℝ → ℝ, (∀ t : ℝ, |t-U*R/N| ≤ γ*N →
          calibratedMean outside r (compensation M q r) N R U t (θ t) = q ∧
          |θ t| ≤ a*N/q ∧
          v*q/4 ≤ calibratedVariance outside r (compensation M q r) N R U t (θ t) ∧
          calibratedVariance outside r (compensation M q r) N R U t (θ t) ≤ q ∧
          HasDerivAt θ (-checkerboard r (compensation M q r) (θ t)/
            calibratedVariance outside r (compensation M q r) N R U t (θ t)) t ∧
          (∀ᶠ u in 𝓝 t, calibratedMean outside r (compensation M q r) N R U u (θ u) = q) ∧
          ∃ slope : ℝ, c*(N/q) ≤ slope ∧ slope ≤ C*(N/q) ∧
            HasDerivAt (fun u => (bg+u)*Real.sigmoid (θ u)-u/2) slope t) ∧
          ∀ y : Fiber S e o,
            nativeMinimalRectangleReadout S e o k l y =
              nativeMinimalRectangleReadout S e o k l z →
            |(nativeRectangleACount S e o k l y : ℝ)-U*R/N| ≤ γ*N →
            let x := θ (nativeRectangleACount S e o k l y)
            (∑ i : Fin M, Real.sigmoid (x+(score q r e y.val i-z0))) = q ∧
            v*q/4 ≤ ∑ i : Fin M, Real.sigmoid (x+(score q r e y.val i-z0))*
              (1-Real.sigmoid (x+(score q r e y.val i-z0))) ∧
            (∑ i : Fin M, Real.sigmoid (x+(score q r e y.val i-z0))*
              (1-Real.sigmoid (x+(score q r e y.val i-z0)))) ≤ q ∧
            ∀ u : ℝ, (∑ i : Fin M, Real.sigmoid (u+(score q r e y.val i-z0))) = q → u = x := by
  obtain ⟨d,η,hd,hη,hcal⟩ := anchored_central_shared_calibration r hr hr1
  let a := min 1 (d/128)
  let γ := min (1/64) (a*v/32)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hγ : 0 < γ := lt_min (by norm_num) (by positivity)
  refine ⟨a,γ,η,d/512,a/4+4/v,ha,hγ,hη,by positivity,by positivity,?_⟩
  intro M q s S e o _ k l z hq hqm he he1
  dsimp only
  intro hN hR hR' hU hU' hlarge hsize hsize' hηscale hε bg hbg hbgN anchor xStar henv hroot hvar hprecision hstar
  let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+ (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
  let V := nativeRectangleRows S e o k l z
  let N : ℝ := V.card
  let R : ℝ := (V.filter fun i => count e z.val i.val 1 = k).card
  let U : ℝ := (V.filter fun i => count e z.val i.val (-1) = l).card
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val-z0
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hi := native_environment_mean_variance S r e o k l anchor z henv hq hqm hr hr1 he he1 xStar
  dsimp only at hi
  have hanchor : calibratedMean outside r (compensation M q r) N R U
      (nativeRectangleACount S e o k l anchor) xStar = q := by
    rw [←hi.1]; exact hroot
  have hV : v*q ≤ calibratedVariance outside r (compensation M q r) N R U
      (nativeRectangleACount S e o k l anchor) xStar := by
    rw [←hi.2]; exact hvar
  have hpartition := native_outside_rectangle_card S e o k l z
  have hqM : (q : ℝ) <
      (Fintype.card {i : Fin M // nativeRowCell S e z.val k l i = none} : ℝ)+N := by
    have hh : q < Fintype.card {i : Fin M // nativeRowCell S e z.val k l i = none}+V.card := by rwa [hpartition]
    dsimp only [N]
    exact_mod_cast hh
  have hb := anchor_scale_budget N q v a γ xStar hN hqR hv ha
    ((min_le_left _ _).trans (by norm_num)) (min_le_right _ _) hlarge hsize hsize' hprecision
  obtain ⟨θ,hθ⟩ := hcal _ outside (compensation M q r) N R U q bg (1/4) γ a v 1
    (nativeRectangleACount S e o k l anchor) xStar hN hqR hqM (by norm_num)
    hγ.le (by have hh := min_le_left (1/64 : ℝ) (a*v/32); dsimp only [γ]; linarith only [hh])
    hv hbg (by simpa using hbgN)
    (by linarith only [hR]) (by linarith only [hR'])
    (by linarith only [hU]) (by linarith only [hU']) hanchor hV hstar
    hb.1 hb.2.1 hb.2.2 (by have hh := min_le_right (1 : ℝ) (d/128); dsimp only [a]; linarith only [hh])
    hηscale hε
  refine ⟨θ,?_,?_⟩
  · intro t ht
    have ht' := hθ t ht
    rcases ht'.2.2.2.2.2.2.2 with ⟨slope,hlo,hhi,hder⟩
    refine ⟨ht'.1,ht'.2.1,ht'.2.2.2.1,ht'.2.2.2.2.1,ht'.2.2.2.2.2.1, ht'.2.2.2.2.2.2.1,slope,?_,?_,hder⟩
    · convert hlo using 1 <;> ring
    · convert hhi using 1 <;> ring
  · intro y hy ht
    have hi := native_environment_mean_variance S r e o k l y z hy hq hqm hr hr1 he he1 (θ (nativeRectangleACount S e o k l y))
    dsimp only at hi
    have ht' := hθ (nativeRectangleACount S e o k l y) ht
    refine ⟨hi.1.trans ht'.1,?_,?_,?_⟩
    · rw [hi.2]
      exact ht'.2.2.2.1
    · rw [hi.2]
      exact ht'.2.2.2.2.1
    · intro u hu
      have hiu := native_environment_mean_variance S r e o k l y z hy hq hqm hr hr1 he he1 u
      dsimp only at hiu
      have hc (j : Fin 4) : 0 ≤ cellCounts N R U (nativeRectangleACount S e o k l y) j := by
        have hh := central_four_cells_lower N R U (1/4) (nativeRectangleACount S e o k l y)
          (γ*N) hN (by norm_num) (by linarith only [hR]) (by linarith only [hR'])
          (by linarith only [hU]) (by linarith only [hU']) ht j
        have hg : γ ≤ 1/64 := min_le_left _ _
        nlinarith only [hh,hg,hN]
      exact (unique_shared_root outside r (compensation M q r) N R U q (nativeRectangleACount S e o k l y) hN hqR hqM hc).unique
          (hiu.1.symm.trans hu) ht'.1
end
end D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
open D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
namespace D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
noncomputable section
private theorem row_reference_successors {M q L : ℕ} (S : Support M q) (r : ℝ)
    (i : Fin M) (k l : ℕ) :
    rowReference S r L i (k + 1, l) =
      ((L : ℝ) * (1 + b r S (.inl i)) / 2 / (k + 1)) * rowReference S r L i (k, l) ∧
    rowReference S r L i (k, l + 1) =
      ((L : ℝ) * (1 - b r S (.inl i)) / 2 / (l + 1)) * rowReference S r L i (k, l) := by
  unfold rowReference; simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  constructor <;> field_simp <;> ring
/-- Large central signal counts give simultaneous reference ratios for all
four cells, using the original compensated model rather than a new law. -/
theorem signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val) (k l : ℕ)
    (hkp : 15 / 16 ≤ ((L : ℝ) * (1 + r) / 2 / (k + 1)))
    (hkp' : ((L : ℝ) * (1 + r) / 2 / (k + 1)) ≤ 1)
    (hlp : 15 / 16 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))
    (hlp' : ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1) :
    ∀ j : Fin 4,
      7 / 8 * rowReference S r L i (k, l) ≤
        rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ≤
        9 / 8 * rowReference S r L i (k, l) := by
  have hpos := D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i (k,l)
  have hk := (row_reference_successors (L := L) S r i k l).1
  have hl := (row_reference_successors (L := L) S r i k l).2
  have hkl := (row_reference_successors (L := L) S r i k (l+1)).1
  simp only [b, if_pos hi] at hk hl hkl
  have hprodlo : 7 / 8 ≤
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) := by
    have hh := mul_le_mul hkp hlp (by norm_num : (0 : ℝ) ≤ 15 / 16) (by linarith)
    norm_num at hh; linarith only [hh]
  have hprodhi :
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1 := by
    nlinarith only [hkp, hkp', hlp, hlp', mul_nonneg (by linarith : 0 ≤ 1 - ((L : ℝ) * (1 + r) / 2 / (k + 1)))
        (by linarith : 0 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))]
  intro j
  fin_cases j
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l) ∧
      rowReference S r L i (k,l) ≤ 9/8 * rowReference S r L i (k,l)
    constructor <;> nlinarith only [hpos]
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l) ∧
      rowReference S r L i (k+1,l) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hk]
    constructor <;> nlinarith only [hpos, hkp, hkp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l+1) ∧
      rowReference S r L i (k,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hl]
    constructor <;> nlinarith only [hpos, hlp, hlp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l+1) ∧
      rowReference S r L i (k+1,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hkl, hl, ← mul_assoc]; exact ⟨mul_le_mul_of_nonneg_right hprodlo hpos.le,
      (mul_le_mul_of_nonneg_right hprodhi hpos.le).trans (by nlinarith only [hpos])⟩
/-- The central four-cell comparison retains the original natural floor
and l=lambda-k. Only explicit lower scale bounds are needed. -/
theorem floored_signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1-κ)
    (hcκ : compensation M q r ≤ 1-κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val)
    (hplus : 15 ≤ ((1+r)/2)*(L : ℝ)) (hminus : 30 ≤ ((1-r)/2)*(L : ℝ)) :
    let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
    let l := L-k
    ∀ j : Fin 4, 7/8 * rowReference S r L i (k,l) ≤
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ≤
        9/8 * rowReference S r L i (k,l) := by
  have hr1 : r < 1 := by linarith only [hrκ,hκ]
  have hh := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hh ⊢; exact signal_four_reference_ratios S r κ hκ hr hrκ hcκ hL i hi _ _
    hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2
/-- The background A mean is exactly the signal A mean times the negative
original A logit. The finite-size compensation and M-q are preserved. -/
theorem background_reference_cell_ratio {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (hq : 1 ≤ q) (hqm : q < M) (i j : Fin M)
    (hi : i ∈ S.val) (hj : j ∉ S.val) (k l : ℕ) :
    ((M - q : ℕ) : ℝ) * rowReference S r L j (k,l) =
      ((q : ℝ) * rowReference S r L i (k,l)) *
        Real.exp (-(k * Real.log ((1+r)/(1-compensation M q r)) +
          l * Real.log ((1-r)/(1+compensation M q r)) -
          Real.log (((M-q : ℕ) : ℝ) / q))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hMR : (0 : ℝ) < (M-q : ℕ) := by exact_mod_cast (show 0 < M-q by omega)
  rw [reference_likelihood_ratio S r κ hκ hr hrκ hcκ hL i j hi hj (k,l)]
  rw [neg_sub, Real.exp_sub, Real.exp_log (div_pos hMR hqR)]
  field_simp <;> ring
end
end D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
namespace D5.S3.Estimation.TimeArrow.OriginalScoreWindow
noncomputable section
/-- The original complete window keeps its left-open, right-closed endpoints. -/
def originalWindow {M s : ℕ} (q : ℕ) (r center width : ℝ)
    (e : Experiment) (o : Obs M s e) : Finset (Fin M) := by
  classical
  exact univ.filter fun i => center-width < score q r e o i ∧ score q r e o i ≤ center+width
/-- Exact scores index groups inside the complete window. -/
def originalScoreGroup {M s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (o : Obs M s e) : Finset (Fin M) := by
  classical
  exact (originalWindow q r center width e o).filter fun i => score q r e o i = value
/-- The denominator in inclusion is the complete uniform-size support posterior. -/
def originalGroupPosteriorMean {M s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (o : Obs M s e) : ℝ :=
  ∑ i ∈ originalScoreGroup q r center width value e o,inclusion q r e o i
/-- A cut on complete signed departure counts, including all background rows. -/
def originalCountCut {M s : ℕ} (H : ℕ) (e : Experiment) (o : Obs M s e) : Prop :=
  ∀ i : Fin M,count e o i 1+count e o i (-1) ≤ H
set_option maxHeartbeats 800000 in
private theorem compensated_log_bounds (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2) :
    |Real.log (1-ε)| ≤ 2*ε ∧ |Real.log (1+ε)| ≤ ε ∧
    Real.log (1-ε) ≤ -ε ∧ Real.log (1+ε) ≤ ε := by
  have hp : 0 < 1-ε := by linarith only [hε1]
  have hm := Real.log_le_sub_one_of_pos hp
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hi : (1-ε)⁻¹ ≤ 1+2*ε := by
    apply (inv_le_iff_one_le_mul₀ hp).mpr
    nlinarith only [hε,hε1]
  have hpl := Real.log_le_sub_one_of_pos (by linarith only [hε] : 0 < 1+ε)
  rw [abs_of_nonpos (Real.log_nonpos hp.le (by linarith only [hε])), abs_of_nonneg (Real.log_nonneg (by linarith only [hε]))]
  exact ⟨by linarith only [hl,hi],by linarith only [hpl], by linarith only [hm],by linarith only [hpl]⟩
set_option maxHeartbeats 800000 in
/-- Integer separation applies to the actual compensated scores. The error
uses the complete count cut and the original uncorrected window center. -/
private theorem count_score_grid_error (k l k0 l0 H Q P : ℕ) (h η ε center raw : ℝ)
    (hQ : 0 < Q) (hh : 0 < h) (hη : 0 < η) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2)
    (hkl : k+l ≤ H) (hraw : raw = k0*(h*((P : ℝ)/Q+η))-(l0 : ℝ)*h) :
    let a := h*((P : ℝ)/Q+η)-Real.log (1-ε)
    let b := -h-Real.log (1+ε)
    let D : ℤ := (P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0)
    |k*a+l*b-center-(h/Q)*D| ≤
      h*η*(H+k0+l0)+2*ε*H+|raw-center| := by
  dsimp only
  obtain ⟨hminus,hplus,_,_⟩ := compensated_log_bounds ε hε hε1
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have he : (k : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+ l*(-h-Real.log (1+ε))-center-(h/Q)*
        (((P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0) : ℤ) : ℝ) =
      h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)-l*Real.log (1+ε)+(raw-center) := by
    rw [hraw]
    push_cast
    field_simp <;> ring
  rw [he]
  have hk : |(k : ℝ)-k0| ≤ H+k0+l0 := by
    have hh' : (k : ℝ)+(l : ℝ) ≤ H := by exact_mod_cast hkl
    rw [abs_le]
    constructor <;> linarith only [hh',(Nat.cast_nonneg l : (0 : ℝ) ≤ l),(Nat.cast_nonneg k : (0 : ℝ) ≤ k),(Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0),(Nat.cast_nonneg l0 : (0 : ℝ) ≤ l0)]
  have hcounts : 2*ε*k+ε*l ≤ 2*ε*H := by
    have hh' : (k : ℝ)+(l : ℝ) ≤ H := by exact_mod_cast hkl
    nlinarith only [mul_le_mul_of_nonneg_left hh' hε,(Nat.cast_nonneg l : (0 : ℝ) ≤ l),hε]
  calc
    _ ≤ |h*η*((k : ℝ)-k0)|+|(k : ℝ)*Real.log (1-ε)|+
        |(l : ℝ)*Real.log (1+ε)|+|raw-center| := by
      have h1 := abs_add_le (h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)-l*Real.log (1+ε)) (raw-center)
      have h2 := abs_sub_le (h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)) 0 (l*Real.log (1+ε))
      have h3 := abs_sub_le (h*η*((k : ℝ)-k0)) 0 ((k : ℝ)*Real.log (1-ε))
      simp only [sub_zero,zero_sub,abs_neg] at h2 h3; linarith only [h1,h2,h3]
    _ ≤ h*η*(H+k0+l0)+2*ε*k+ε*l+|raw-center| := by
      simp only [abs_mul,abs_of_nonneg hh.le,abs_of_nonneg hη.le,
        abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k),abs_of_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
      have hx := mul_le_mul_of_nonneg_left hk (mul_nonneg hh.le hη.le)
      have hm := mul_le_mul_of_nonneg_left hminus (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have hp := mul_le_mul_of_nonneg_left hplus (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
      nlinarith only [hx,hm,hp]
    _ ≤ _ := by linarith only [hcounts]
set_option maxHeartbeats 800000 in
/-- The positive original score step separates exact groups, including
negative original grid indices. -/
private theorem compensated_grid_step_pos (Q P : ℕ) (h η ε : ℝ)
    (hPQ : P < Q) (hh : 0 < h) (hη : 0 < η) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2) :
    0 < (Q : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      P*(-h-Real.log (1+ε)) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hPQ' : (P : ℝ) < Q := by exact_mod_cast hPQ
  obtain ⟨_,_,hminus,hplus⟩ := compensated_log_bounds ε hε hε1
  have he : (Q : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      P*(-h-Real.log (1+ε)) = (Q : ℝ)*h*η-Q*Real.log (1-ε)-P*Real.log (1+ε) := by
    field_simp <;> ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hminus hQ.le
  have hp := mul_le_mul_of_nonneg_left hplus (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hgap : 0 ≤ ((Q : ℝ)-P)*ε := mul_nonneg (by linarith only [hPQ']) hε
  have hpos : 0 < (Q : ℝ)*h*η := by positivity
  nlinarith only [hm,hp,hgap,hpos]
end
end D5.S3.Estimation.TimeArrow.OriginalScoreWindow
