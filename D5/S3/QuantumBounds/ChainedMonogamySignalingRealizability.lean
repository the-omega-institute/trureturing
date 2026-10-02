/- GID: D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/ChainedMonogamySignalingRealizability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every correlator vector obeying ElPrat is realized by a box with R_M = 2M + Delta. -/

/-
proof_shape: sgn, IsBox, OddMomentsVanish, corrAB, corrAE, corrBE, chainR, ElPrat,
  CoordinateBounds, Realizes: definition (outcome signs, boxes of conditional distributions,
  the class with vanishing one- and three-party means, the correlators, R_M, the inequalities
  (ElPrat), the range of the coordinates and their realization by a box)
proof_shape: claim: definition (published conjecture, read over every M >= 2, every Delta in
  [0, 2] and every coordinate vector in [-1, 1] satisfying (ElPrat))
proof_shape: result: content (an explicit box: the distribution (1 + ab u + ae v + be w) / 8 at
  each setting pair, with u at its extreme on the chain pairs and the common value
  t = (2 + Delta + T) / (2 + x_B^0 + x_B^1) of <B_0 E>, and the evaluation of R_M; the
  reduction of (ElPrat) to one inequality and every rewriting step are local steps)
escape_witness: result (form (2) of §3.2: the realizing box and the value of R_M are produced by
  the construction; no existing statement gives them)
admission_basis: open-problem-resolution (issue #12401; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumBounds.ChainedMonogamySignalingRealizability

open Finset

/-- The value `±1` of a binary outcome. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- A box assigns to every pair of settings `(A_i, B_j)` a function of the outcomes `(a, b, e)`;
`IsBox M p` says that for all settings `i, j < M` it is a probability distribution. -/
def IsBox (M : ℕ) (p : ℕ → ℕ → Bool → Bool → Bool → ℝ) : Prop :=
  ∀ i < M, ∀ j < M, (∀ a b e, 0 ≤ p i j a b e) ∧ ∑ a, ∑ b, ∑ e, p i j a b e = 1

/-- The class `𝒫` of the paper: every one-party and three-party expectation value vanishes. -/
def OddMomentsVanish (M : ℕ) (p : ℕ → ℕ → Bool → Bool → Bool → ℝ) : Prop :=
  ∀ i < M, ∀ j < M,
    ∑ a, ∑ b, ∑ e, sgn a * p i j a b e = 0 ∧ ∑ a, ∑ b, ∑ e, sgn b * p i j a b e = 0 ∧
      ∑ a, ∑ b, ∑ e, sgn e * p i j a b e = 0 ∧
        ∑ a, ∑ b, ∑ e, sgn a * sgn b * sgn e * p i j a b e = 0

/-- `⟨A_i B_j⟩`. -/
def corrAB (p : ℕ → ℕ → Bool → Bool → Bool → ℝ) (i j : ℕ) : ℝ :=
  ∑ a, ∑ b, ∑ e, sgn a * sgn b * p i j a b e

/-- `⟨A_i E⟩_{B_j}`. -/
def corrAE (p : ℕ → ℕ → Bool → Bool → Bool → ℝ) (i j : ℕ) : ℝ :=
  ∑ a, ∑ b, ∑ e, sgn a * sgn e * p i j a b e

/-- `⟨B_j E⟩_{A_i}`. -/
def corrBE (p : ℕ → ℕ → Bool → Bool → Bool → ℝ) (i j : ℕ) : ℝ :=
  ∑ a, ∑ b, ∑ e, sgn b * sgn e * p i j a b e

/-- `R_M = I^M_{AB} + 2⟨B_0 E⟩` with `I^M_{AB} = Σ_k (⟨A_k B_k⟩ + ⟨A_{k+1} B_k⟩)` and
`A_M = -A_0`. -/
def chainR (M : ℕ) (p : ℕ → ℕ → Bool → Bool → Bool → ℝ) : ℝ :=
  ∑ k ∈ range M, corrAB p k k + ∑ k ∈ range (M - 1), corrAB p (k + 1) k -
    corrAB p 0 (M - 1) + 2 * corrBE p 0 0

/-- The inequalities (ElPrat), one for each choice of the signs `a_i, b_i, c ∈ {0, 1}`. -/
def ElPrat (M : ℕ) (Δ : ℝ) (xA yA xB yB : ℕ → ℝ) : Prop :=
  ∀ (a b : ℕ → Fin 2) (c : Fin 2),
    Δ ≤ ∑ i ∈ Icc 1 (M - 1), (-1 : ℝ) ^ (a i : ℕ) * (xA i - yB i) +
      ∑ i ∈ Icc 1 (M - 2), (-1 : ℝ) ^ (b i : ℕ) * (xB (i + 1) - yA i) +
        (-1 : ℝ) ^ (c : ℕ) * (yA (M - 1) + yB 0) + xB 1 + xB 0

/-- The listed coordinates are correlators, so they lie in `[-1, 1]`. -/
def CoordinateBounds (M : ℕ) (xA yA xB yB : ℕ → ℝ) : Prop :=
  (∀ i ∈ Icc 1 (M - 1), |xA i| ≤ 1 ∧ |yA i| ≤ 1 ∧ |xB i| ≤ 1 ∧ |yB i| ≤ 1) ∧
    |xB 0| ≤ 1 ∧ |yB 0| ≤ 1

/-- The box realizes the coordinates `x_A^i = ⟨B_i E⟩_{A_i}`, `y_A^i = ⟨B_i E⟩_{A_{i+1}}`,
`x_B^i = ⟨A_i E⟩_{B_{i-1}}`, `y_B^i = ⟨A_i E⟩_{B_i}`, `x_B^0 = ⟨A_0 E⟩_{B_0}` and
`y_B^0 = ⟨A_0 E⟩_{B_{M-1}}`, with the setting `A_M = -A_0` read as `A_0`. -/
def Realizes (M : ℕ) (p : ℕ → ℕ → Bool → Bool → Bool → ℝ) (xA yA xB yB : ℕ → ℝ) : Prop :=
  (∀ i ∈ Icc 1 (M - 1), corrBE p i i = xA i ∧ corrAE p i (i - 1) = xB i ∧
      corrAE p i i = yB i) ∧
    (∀ i ∈ Icc 1 (M - 2), corrBE p (i + 1) i = yA i) ∧ corrBE p 0 (M - 1) = yA (M - 1) ∧
      corrAE p 0 0 = xB 0 ∧ corrAE p 0 (M - 1) = yB 0

/-- The conjecture of Kłobus, Oszmaniec, Augusiak and Grudka (arXiv:1408.1223, Section 5):
every coordinate vector satisfying (ElPrat) is realized by a box of the class `𝒫` with a common
`⟨B_0 E⟩_{A_i}` and `R_M = 2M + Δ`. -/
def claim : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ 2 → ∀ xA yA xB yB : ℕ → ℝ,
    CoordinateBounds M xA yA xB yB → ElPrat M Δ xA yA xB yB →
      ∃ p, IsBox M p ∧ OddMomentsVanish M p ∧ (∀ i < M, corrBE p i 0 = corrBE p 0 0) ∧
        chainR M p = 2 * M + Δ ∧ Realizes M p xA yA xB yB

theorem result : claim := by
  intro M hM Δ hΔ0 hΔ2 xA yA xB yB hbd hel
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  -- the three-correlator distribution
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ → ℝ → Bool → Bool → Bool → ℝ,
      q = fun u v w a b e => (1 + sgn a * sgn b * u + sgn a * sgn e * v + sgn b * sgn e * w) / 8 :=
    ⟨_, rfl⟩
  have hmom : ∀ u v w : ℝ, ∑ a, ∑ b, ∑ e, q u v w a b e = 1 ∧
      ∑ a, ∑ b, ∑ e, sgn a * q u v w a b e = 0 ∧ ∑ a, ∑ b, ∑ e, sgn b * q u v w a b e = 0 ∧
      ∑ a, ∑ b, ∑ e, sgn e * q u v w a b e = 0 ∧
      ∑ a, ∑ b, ∑ e, sgn a * sgn b * sgn e * q u v w a b e = 0 ∧
      ∑ a, ∑ b, ∑ e, sgn a * sgn b * q u v w a b e = u ∧
      ∑ a, ∑ b, ∑ e, sgn a * sgn e * q u v w a b e = v ∧
      ∑ a, ∑ b, ∑ e, sgn b * sgn e * q u v w a b e = w := by
    intro u v w
    subst hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Fintype.sum_bool, sgn, if_true, if_false, Bool.false_eq_true] <;> ring
  have hnn : ∀ u v w : ℝ, -1 + |v + w| ≤ u → u ≤ 1 - |v - w| → ∀ a b e, 0 ≤ q u v w a b e := by
    intro u v w h1 h2 a b e
    subst hq
    have := le_abs_self (v + w); have := neg_abs_le (v + w)
    have := le_abs_self (v - w); have := neg_abs_le (v - w)
    cases a <;> cases b <;> cases e <;> simp only [sgn, if_true, if_false, Bool.false_eq_true] <;>
      linarith
  have hxB0 : |xB 0| ≤ 1 := hbd.2.1
  have hyB0 : |yB 0| ≤ 1 := hbd.2.2
  have hin : ∀ i, 1 ≤ i → i ≤ m + 1 → |xA i| ≤ 1 ∧ |yA i| ≤ 1 ∧ |xB i| ≤ 1 ∧ |yB i| ≤ 1 :=
    fun i h1 h2 => hbd.1 i (by simp only [Finset.mem_Icc]; omega)
  have hxB1 : |xB 1| ≤ 1 := (hin 1 le_rfl (by omega)).2.2.1
  -- the sum of absolute values `T` and the reduction of (ElPrat) to one inequality
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ i ∈ Icc 1 (m + 1), |xA i - yB i| +
      ∑ i ∈ Icc 1 m, |xB (i + 1) - yA i| + |yA (m + 1) + yB 0| := ⟨_, rfl⟩
  have hTnn : 0 ≤ T := by rw [hT]; positivity
  have hkey : Δ ≤ xB 1 + xB 0 - T := by
    have hs : ∀ d : ℝ, (-1 : ℝ) ^ (((if 0 ≤ d then 1 else 0 : Fin 2)) : ℕ) * d = -|d| := by
      intro d
      split_ifs with hd
      · simp [abs_of_nonneg hd]
      · simp [abs_of_neg (lt_of_not_ge hd)]
    have h := hel (fun i => if 0 ≤ xA i - yB i then 1 else 0)
      (fun i => if 0 ≤ xB (i + 1) - yA i then 1 else 0)
      (if 0 ≤ yA (m + 1) + yB 0 then 1 else 0)
    simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, hs,
      Finset.sum_neg_distrib] at h
    rw [hT]
    linarith
  -- the common value `t = ⟨B_0 E⟩_{A_i}`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (2 + Δ + T) / (2 + xB 0 + xB 1) := ⟨_, rfl⟩
  have hden : 0 < 2 + xB 0 + xB 1 := by linarith
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
  have htmul : t * (2 + xB 0 + xB 1) = 2 + Δ + T := by rw [ht]; field_simp
  have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
  -- the parameters of the distribution at the setting pair `(i, j)`
  obtain ⟨V, hV⟩ : ∃ V : ℕ → ℕ → ℝ, V = fun i j =>
      if j = 0 then (if i = 0 then xB 0 else if i = 1 then xB 1 else 0)
      else if i = j then yB i else if i = j + 1 then xB i
      else if i = 0 ∧ j = m + 1 then yB 0 else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℕ → ℝ, W = fun i j =>
      if j = 0 then t else if i = j then xA i else if i = j + 1 then yA j
      else if i = 0 ∧ j = m + 1 then yA (m + 1) else 0 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℕ → ℕ → ℝ, U = fun i j =>
      if j = 0 then (if i = 0 ∨ i = 1 then t * V i j else 0)
      else if i = j ∨ i = j + 1 then 1 - |V i j - W i j|
      else if i = 0 ∧ j = m + 1 then -1 + |V i j + W i j| else 0 := ⟨_, rfl⟩
  have hVb : ∀ i < m + 2, ∀ j < m + 2, |V i j| ≤ 1 := by
    intro i hi j hj
    rw [hV]
    dsimp only
    split_ifs
    · exact hxB0
    · exact hxB1
    · simp
    · exact (hin i (by omega) (by omega)).2.2.2
    · exact (hin i (by omega) (by omega)).2.2.1
    · exact hyB0
    · simp
  have hWb : ∀ i < m + 2, ∀ j < m + 2, |W i j| ≤ 1 := by
    intro i hi j hj
    rw [hW]
    dsimp only
    split_ifs with h1 h2 h3 h4
    · exact hta
    · exact (hin i (by omega) (by omega)).1
    · exact (hin j (by omega) (by omega)).2.1
    · exact (hin (m + 1) (by omega) le_rfl).2.1
    · simp
  have hpair : ∀ v w : ℝ, |v| ≤ 1 → |w| ≤ 1 → |v + w| + |v - w| ≤ 2 := by
    intro v w hv hw
    rcases abs_le.mp hv with ⟨hv1, hv2⟩
    rcases abs_le.mp hw with ⟨hw1, hw2⟩
    rcases abs_cases (v + w) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases abs_cases (v - w) with ⟨h2, -⟩ | ⟨h2, -⟩ <;> linarith
  have hUb : ∀ i < m + 2, ∀ j < m + 2,
      -1 + |V i j + W i j| ≤ U i j ∧ U i j ≤ 1 - |V i j - W i j| := by
    intro i hi j hj
    have hp := hpair (V i j) (W i j) (hVb i hi j hj) (hWb i hi j hj)
    have hv := abs_le.mp (hVb i hi j hj)
    rw [hU]
    dsimp only
    split_ifs with h1 h2 h3 h4
    · have hw : W i j = t := by rw [hW]; simp [h1]
      rw [hw]
      have p1 : 0 ≤ (1 + V i j) * t := mul_nonneg (by linarith) ht0.le
      have p2 : 0 ≤ (1 - V i j) * (1 - t) := mul_nonneg (by linarith) (by linarith)
      have p3 : 0 ≤ (1 + V i j) * (1 - t) := mul_nonneg (by linarith) (by linarith)
      have p4 : 0 ≤ (1 - V i j) * t := mul_nonneg (by linarith) ht0.le
      have e1 : |V i j + t| ≤ 1 + t * V i j := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
      have e2 : |V i j - t| ≤ 1 - t * V i j := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
      constructor <;> linarith
    · push Not at h2
      have hv0 : V i j = 0 := by rw [hV]; simp [h1, h2.1, h2.2]
      have hw := hWb i hi j hj
      rw [hv0, zero_add, zero_sub, abs_neg]
      constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
    · push Not at h3
      have hv0 : V i j = 0 := by rw [hV]; simp [h1, h3.1, h3.2, h4]
      have hw0 : W i j = 0 := by rw [hW]; simp [h1, h3.1, h3.2, h4]
      rw [hv0, hw0]
      norm_num
  -- the realizing box
  have hshift : ∀ (g : ℕ → ℝ) (n : ℕ), ∑ i ∈ Icc 1 n, g i = ∑ k ∈ range n, g (k + 1) := by
    intro g n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  refine ⟨fun i j => q (U i j) (V i j) (W i j), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    exact ⟨hnn _ _ _ (hUb i hi j hj).1 (hUb i hi j hj).2, (hmom _ _ _).1⟩
  · intro i _ j _
    exact ⟨(hmom _ _ _).2.1, (hmom _ _ _).2.2.1, (hmom _ _ _).2.2.2.1, (hmom _ _ _).2.2.2.2.1⟩
  · intro i _
    change ∑ a, ∑ b, ∑ e, sgn b * sgn e * q (U i 0) (V i 0) (W i 0) a b e =
      ∑ a, ∑ b, ∑ e, sgn b * sgn e * q (U 0 0) (V 0 0) (W 0 0) a b e
    rw [(hmom _ _ _).2.2.2.2.2.2.2, (hmom _ _ _).2.2.2.2.2.2.2, hW]
    simp
  · have hAB : ∀ i j, corrAB (fun i j => q (U i j) (V i j) (W i j)) i j = U i j :=
      fun i j => (hmom _ _ _).2.2.2.2.2.1
    have hBE : ∀ i j, corrBE (fun i j => q (U i j) (V i j) (W i j)) i j = W i j :=
      fun i j => (hmom _ _ _).2.2.2.2.2.2.2
    simp only [chainR, hAB, hBE, show m + 2 - 1 = m + 1 by omega]
    rw [Finset.sum_range_succ' (fun k => U k k), Finset.sum_range_succ' (fun k => U (k + 1) k)]
    have h1 : ∀ k, U (k + 1) (k + 1) = 1 - |xA (k + 1) - yB (k + 1)| := by
      intro k
      rw [hU, hV, hW]
      simp [abs_sub_comm]
    have h2 : ∀ k, U (k + 1 + 1) (k + 1) = 1 - |xB (k + 1 + 1) - yA (k + 1)| := by
      intro k
      rw [hU, hV, hW]
      simp
    have h3 : U 0 (m + 1) = -1 + |yA (m + 1) + yB 0| := by
      rw [hU, hV, hW]
      simp [add_comm]
    have h4 : U 0 0 = t * xB 0 := by rw [hU, hV]; simp
    have h5 : U (0 + 1) 0 = t * xB 1 := by rw [hU, hV]; simp
    have h6 : W 0 0 = t := by rw [hW]; simp
    simp only [h1, h2, h3, h4, h5, h6]
    rw [hT, hshift, hshift] at htmul
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    push_cast
    linarith
  · have hAE : ∀ i j, corrAE (fun i j => q (U i j) (V i j) (W i j)) i j = V i j :=
      fun i j => (hmom _ _ _).2.2.2.2.2.2.1
    have hBE : ∀ i j, corrBE (fun i j => q (U i j) (V i j) (W i j)) i j = W i j :=
      fun i j => (hmom _ _ _).2.2.2.2.2.2.2
    simp only [Realizes, hAE, hBE, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc] at hi
      refine ⟨?_, ?_, ?_⟩
      · rw [hW]; simp [show i ≠ 0 by omega]
      · rw [hV]
        rcases Nat.lt_or_ge i 2 with h | h
        · obtain rfl : i = 1 := by omega
          simp
        · have hi1 : i - 1 + 1 = i := by omega
          simp [show i - 1 ≠ 0 by omega, show i ≠ i - 1 by omega, hi1]
      · rw [hV]; simp [show i ≠ 0 by omega]
    · rw [Finset.mem_Icc] at hi
      rw [hW]; simp [show i ≠ 0 by omega]
    · rw [hW]; simp
    · rw [hV]; simp
    · rw [hV]; simp

end D5.S3.QuantumBounds.ChainedMonogamySignalingRealizability
