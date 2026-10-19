/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every supported OperationOmega coordinate is the grouped legal digit series. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SuccessorContinuity

abbrev CLabel := D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label
abbrev CGuard := D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Guard
abbrev SLabel := D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.Label

def guardBool : CGuard → Bool
  | .G0 => false
  | .G1 => true

def labelWindow : CLabel → SLabel
  | .L0 => nullLabel
  | .L3 => threeLabel
  | .L2 => twoLabel
  | .L5 => fiveLabel
  | .L25 => twoFiveLabel

def labelBit : CLabel → ℕ → Bool
  | .L0, _ => false
  | .L3, 0 => false
  | .L3, 1 => true
  | .L3, _ => false
  | .L2, 0 => true
  | .L2, _ => false
  | .L5, 2 => true
  | .L5, _ => false
  | .L25, 0 => true
  | .L25, 2 => true
  | .L25, _ => false

def rawDigits (a : ℕ → CLabel) : ℕ → Bool := fun n => labelBit (a (n / 3)) (n % 3)

theorem labelBit_window (l : CLabel) (i : Fin 3) :
    labelBit l i.val = (labelWindow l).val i := by
  cases l <;> fin_cases i <;> simp [labelBit, labelWindow, nullLabel, threeLabel,
    twoLabel, fiveLabel, twoFiveLabel]

theorem edge_third_guard (s : CGuard) (l : CLabel) (s' : CGuard)
    (h : nextGuard s l = some s') : labelBit l 2 = guardBool s' := by
  cases s <;> cases l <;> cases s' <;>
    simp [nextGuard, labelBit, guardBool] at h ⊢

theorem g1_edge_has_zero_first (l : CLabel) (s' : CGuard)
    (h : nextGuard .G1 l = some s') : labelBit l 0 = false := by
  cases l <;> cases s' <;> simp [nextGuard, labelBit] at h ⊢

theorem rawDigits_legal_of_operation_edges (a : ℕ → CLabel) (path : ℕ → CGuard)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1))) :
    ∀ j, ¬ (rawDigits a j = true ∧ rawDigits a (j + 1) = true) := by
  intro j
  have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · intro h
    have hcur : labelBit (a (j / 3)) 0 = true := by simpa [rawDigits, h0] using h.1
    have hnext : labelBit (a (j / 3)) 1 = true := by
      have hq : (j + 1) / 3 = j / 3 := by omega
      have hr : (j + 1) % 3 = 1 := by omega
      simpa [rawDigits, hq, hr] using h.2
    cases hl : a (j / 3) <;> simp [labelBit, hl] at hcur hnext
  · intro h
    have hcur : labelBit (a (j / 3)) 1 = true := by simpa [rawDigits, h1] using h.1
    have hnext : labelBit (a (j / 3)) 2 = true := by
      have hq : (j + 1) / 3 = j / 3 := by omega
      have hr : (j + 1) % 3 = 2 := by omega
      simpa [rawDigits, hq, hr] using h.2
    cases hl : a (j / 3) <;> simp [labelBit, hl] at hcur hnext
  · intro h
    let p := j / 3
    have hcur : labelBit (a p) 2 = true := by
      simpa [rawDigits, p, h2] using h.1
    have hnext : labelBit (a (p + 1)) 0 = true := by
      have hq : (j + 1) / 3 = p + 1 := by omega
      have hr : (j + 1) % 3 = 0 := by omega
      simpa [rawDigits, hq, hr, p] using h.2
    have hguardnext : path (p + 1) = .G1 := by
      have he := edge_third_guard (path p) (a p) (path (p + 1)) (hedges p)
      cases hpast : path (p + 1)
      · have hz : labelBit (a p) 2 = false := by simpa [hpast, guardBool] using he
        exact False.elim (Bool.noConfusion (hcur.symm.trans hz))
      · rfl
    have he := hedges (p + 1)
    have hfirst : labelBit (a (p + 1)) 0 = false := by
      apply g1_edge_has_zero_first
      simpa [hguardnext] using he
    exact Bool.noConfusion (hnext.symm.trans hfirst)

theorem coding_t_eq_s1_t :
    D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.t =
      D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.t := by
  dsimp [D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.t,
    D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.t,
    D5.S1.Digit.Infinite.SignedSeriesRange.alpha]
  rw [Real.inv_goldenRatio]
  dsimp [Real.goldenConj]
  ring

theorem rawDigits_window (a : ℕ → CLabel) (path : ℕ → CGuard)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1))) :
    let d : LegalDigits := ⟨rawDigits a, rawDigits_legal_of_operation_edges a path hedges⟩
    ∀ p, window d p = labelWindow (a p) := by
  dsimp
  intro p
  apply Subtype.ext
  funext i
  simp only [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift,
    rawDigits]
  have hdiv : (i.val + 3 * p) / 3 = p := by omega
  have hmod : (i.val + 3 * p) % 3 = i.val := by omega
  rw [hdiv, hmod]
  exact labelBit_window (a p) i

theorem branch_transport (l : CLabel) (y : ℝ) :
    D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.branch (labelWindow l) y =
      D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch l y := by
  have htc := coding_t_eq_s1_t
  have hsq : D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.t ^ 2 +
      D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.t = (1 : ℝ) := by
    dsimp [D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.t,
      D5.S1.Digit.Infinite.SignedSeriesRange.alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hg : D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.g =
      D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.g := by
    dsimp [D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.g,
      D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.g]
    rw [htc]
    have hmul := congrArg (fun z : ℝ => z *
      D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.t) hsq
    nlinarith
  cases l <;>
    simp [D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.branch,
      D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch,
      D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.offset,
      labelWindow, nullLabel, threeLabel, twoLabel, fiveLabel, twoFiveLabel,
      D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.shift,
      D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.T2, htc, hg] <;>
    nlinarith

theorem operation_digit_bridge (a : ℕ → CLabel) (x : ℕ → ℝ)
    (h : OperationOmega a x) :
    ∃ d : LegalDigits, ∃ path : ℕ → CGuard,
      path 0 = .G0 ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, window d p = labelWindow (a p)) ∧
      (∀ p, actualGuard false d p = guardBool (path p)) ∧
      (∀ p, x p ∈ D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.stateInterval
        (guardBool (path p))) ∧
      (∀ p, x p = D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.branch
        (labelWindow (a p)) (x (p + 1))) := by
  obtain ⟨path,hzero,hedges,hsupport,haffine⟩ := h
  let d : LegalDigits := ⟨rawDigits a, rawDigits_legal_of_operation_edges a path hedges⟩
  refine ⟨d,path,hzero,hedges,rawDigits_window a path hedges,?_,?_,?_⟩
  · intro p
    simp only [actualGuard]
    by_cases hp : p = 0
    · simp [hp, hzero, guardBool]
    · have hp' : 0 < p := Nat.pos_of_ne_zero hp
      have heq : 3 * p - 1 = 3 * (p - 1) + 2 := by omega
      have hquot : (3 * (p - 1) + 2) / 3 = p - 1 := by omega
      have hb : labelBit (a (p - 1)) 2 = guardBool (path p) := by
        have he := edge_third_guard (path (p - 1)) (a (p - 1)) (path p)
          (by simpa [Nat.sub_add_cancel hp'] using hedges (p - 1))
        cases hpast : path p <;> simp [hpast, guardBool] at he ⊢
        all_goals exact he
      simpa [hp, d, rawDigits, heq, hquot] using hb
  · intro p
    have hs := hsupport p
    cases hpast : path p <;>
      simpa [hpast, guardBool,
        D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.InSupport,
        D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.supportUpper,
        D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.phi,
        D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.stateInterval,
        coding_t_eq_s1_t, Set.mem_Icc] using hs
  · intro p
    simpa [branch_transport] using haffine p

theorem operation_finite_source_iff_of_bridge (a : ℕ → CLabel) (d : LegalDigits)
    (hw : ∀ p, window d p = labelWindow (a p)) :
    OperationFiniteSource a ↔ finiteTail d := by
  have hd : d.val = rawDigits a := by
    funext j
    let i : Fin 3 := ⟨j % 3, Nat.mod_lt j (by decide)⟩
    have hh := congrArg (fun l : SLabel => l.val i) (hw (j / 3))
    rw [← labelBit_window (a (j / 3)) i] at hh
    simpa [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, rawDigits, i,
      show j % 3 + 3 * (j / 3) = j by omega] using hh
  constructor
  · rintro ⟨M,hM⟩
    refine ⟨3 * M,?_⟩
    intro j hj
    let p := j / 3
    let i := j % 3
    have hp : M ≤ p := by dsimp [p]; omega
    have hj' : j = 3 * p + i := by dsimp [p,i]; omega
    have hl : a p = .L0 := hM p hp
    have hq : (3 * p + i) / 3 = p := by omega
    have hr : (3 * p + i) % 3 = i := by omega
    change d.val j = false
    rw [hd]
    simp [rawDigits, labelBit, hj', hq, hr, hl]
  · rintro ⟨N,hN⟩
    refine ⟨(N + 2) / 3,?_⟩
    intro p hp
    have hn : N ≤ 3 * p := by omega
    have hz0 : d.val (3 * p) = false := hN (3 * p) hn
    have hz1 : d.val (3 * p + 1) = false := hN (3 * p + 1) (by omega)
    have hz2 : d.val (3 * p + 2) = false := hN (3 * p + 2) (by omega)
    have hb0 : labelBit (a p) 0 = false := by
      simpa [hd, rawDigits, show (3 * p) / 3 = p by omega,
        show (3 * p) % 3 = 0 by omega] using hz0
    have hb1 : labelBit (a p) 1 = false := by
      simpa [hd, rawDigits, show (3 * p + 1) / 3 = p by omega,
        show (3 * p + 1) % 3 = 1 by omega] using hz1
    have hb2 : labelBit (a p) 2 = false := by
      simpa [hd, rawDigits, show (3 * p + 2) / 3 = p by omega,
        show (3 * p + 2) % 3 = 2 by omega] using hz2
    cases hl : a p <;> simp [labelBit, hl] at hb0 hb1 hb2 ⊢

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates

open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth (window_shift original_t_shift)
open Filter Topology

/-- The bounded affine coordinates of an arbitrary original source equal the
series of the same grouped legal digit stream at every deletion time. -/
theorem operation_coordinate_bridge (a : ℕ → CLabel) (x : ℕ → ℝ)
    (h : OperationOmega a x) :
    ∃ d : LegalDigits,
      (∀ p, window d p = labelWindow (a p)) ∧
      (∀ p, x p = kappa (bitShift d (3 * p))) ∧
      (OperationFiniteSource a ↔ finiteTail d) := by
  obtain ⟨d, path, hzero, hedges, hw, hguard, hs, hr⟩ := operation_digit_bridge a x h
  have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : 0 < g := pow_pos ht 3
  have hg1 : g < 1 := pow_lt_one₀ ht.le ht1 (by decide)
  have hshift (p : ℕ) : originalT (bitShift d (3 * p)) = bitShift d (3 * (p + 1)) := by
    exact original_t_shift d p
  have hwindow (p : ℕ) : window (bitShift d (3 * p)) 0 = labelWindow (a p) := by
    exact (window_shift d p).trans (hw p)
  have hk (p : ℕ) : kappa (bitShift d (3 * p)) =
      branch (labelWindow (a p)) (kappa (bitShift d (3 * (p + 1)))) := by
    have hh := (closed_observation_graph_realization.2.2.1 (bitShift d (3 * p))).1
    simpa only [hshift, hwindow] using hh
  have bounded (p : ℕ) : |x p - kappa (bitShift d (3 * p))| ≤ 4 := by
    have hx := hs p
    have hy : kappa (bitShift d (3 * p)) ∈ stateInterval false :=
      closed_observation_graph_realization.2.1 false ▸
        ⟨bitShift d (3 * p), by simp [stateAddress], rfl⟩
    have hxhi : x p ≤ 1 + t := by
      cases hp : guardBool (path p) <;> simp [hp, stateInterval] at hx <;> linarith [hx.2]
    have hxlo : -1 ≤ x p := hx.1
    change -1 ≤ kappa (bitShift d (3 * p)) ∧
      kappa (bitShift d (3 * p)) ≤ 1 + t at hy
    exact abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have difference (n p : ℕ) : x p - kappa (bitShift d (3 * p)) =
      (-g) ^ n * (x (p + n) - kappa (bitShift d (3 * (p + n)))) := by
    induction n generalizing p with
    | zero => simp
    | succ n ih =>
      calc
        x p - kappa (bitShift d (3 * p)) =
            -g * (x (p + 1) - kappa (bitShift d (3 * (p + 1)))) := by
          rw [hr p, hk p]
          dsimp [branch]
          ring
        _ = (-g) ^ (n + 1) *
            (x (p + (n + 1)) - kappa (bitShift d (3 * (p + (n + 1))))) := by
          rw [ih]
          simp only [pow_succ]
          rw [show p + 1 + n = p + (n + 1) by omega]
          ring
  refine ⟨d, hw, ?_, operation_finite_source_iff_of_bridge a d hw⟩
  intro p
  have hz : Tendsto (fun _ : ℕ => x p - kappa (bitShift d (3 * p))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hg.le hg1).mul_const 4)
    rw [Real.norm_eq_abs, difference n p, abs_mul, abs_pow, abs_neg, abs_of_pos hg]
    exact mul_le_mul_of_nonneg_left (bounded (p + n)) (pow_nonneg hg.le n)
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hz)

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
