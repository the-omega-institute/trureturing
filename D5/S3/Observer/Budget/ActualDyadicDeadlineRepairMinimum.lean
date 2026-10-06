/- GID: D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact all-policy causal deadline repair capacity on a closed error shell. -/

import D5.S3.Observer.Budget.ActualDyadicDeadlineLabelSupport
import D5.S3.Combinatorics.Graph.CyclicMixedDemandColoring
import Mathlib.Data.Nat.Log
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Observer.Budget.ActualDyadicDeadlineRepairMinimum
open D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity
open D5.S3.ConceptDynamics.Coding.ClosedPhaseBallOverlap
open ActualDyadicDeadlineSupport ActualDyadicDeadlineLabelSupport
open DyadicForwardWaitingOptimality DyadicPrefixDelayRange DyadicDeadlineStaircase
open D5.S3.Combinatorics.Graph.CyclicMixedDemandColoring

/-- The rank count is the cardinality of the actual raw-parity support. -/
noncomputable def actualDemand (d : Nat) (b : Fin 2) (D : Nat) (t : Fin (2 ^ d)) : Nat :=
  (actualParitySupport d b D t.val).card

/-- Only supported raw types are ranked. Both inverse maps retain the raw parity,
including the unique rank zero of a singleton whose raw parity is one. -/
noncomputable def supportedTypeRankEquiv (d : Nat) (b : Fin 2) (D : Nat) :
    {x : Fin (2 ^ d) × Fin 2 // x ∈ actualTypes d b D} ≃ Vertex (actualDemand d b D) := by
  classical
  let e (t : Fin (2 ^ d)) := (actualParitySupport d b D t.val).equivFin
  refine {
    toFun := fun x => ⟨x.val.1, e x.val.1 ⟨x.val.2, ?_⟩⟩
    invFun := fun v => ⟨(v.1, (e v.1).symm v.2), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa only [actualTypes, Finset.mem_filter, Finset.mem_univ, true_and] using x.property
  · simp only [actualTypes, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((e v.1).symm v.2).property
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val ((e x.val.1).symm_apply_apply _)
  · intro v
    apply Sigma.ext
    · rfl
    · exact heq_of_eq ((e v.1).apply_symm_apply _)

/-- Closed phase overlap is the cyclic integer shell, with its seam and boundary. -/
theorem actual_phase_overlap_near (d : Nat) (b : Fin 2) (D m : Nat) (eps : ℝ)
    (deadline : sharpWait (d + 1) ≤ D) (hm : 2 ≤ m)
    (lower : (m : ℝ) - 1 ≤ eps) (upper : eps < (m : ℝ))
    (i j : Fin (2 ^ d)) :
    (∃ q, dist q (prefixPhase d i) ≤ eps ∧ dist q (prefixPhase d j) ≤ eps) ↔
      Near m i j := by
  classical
  have zeroSupport : (0 : Fin 2) ∈ actualParitySupport d b D 0 := by
    rw [actual_deadline_raw_parity_support d b D 0 deadline (Nat.two_pow_pos d)]
    left
    simp
  simp only [actualParitySupport, Finset.mem_filter, Finset.mem_univ, true_and] at zeroSupport
  obtain ⟨N, ⟨policy, family, r0, past, bit, _, _⟩, _⟩ := zeroSupport
  have success : ∀ r, ∃ word terminal,
      Execution (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ word terminal ∧
      word.length ≤ d + 1 ∧ terminal.2 = r := by
    intro r
    obtain ⟨past, N, bit, word, terminal, run, bound, answer, _, _⟩ := family r
    exact ⟨word, terminal, run, bound, answer⟩
  obtain ⟨_, _, _, _, _, scaling, _, _⟩ :=
    actual_causal_closed_error_recovery (Nat.two_pow_pos (d + 1)) d rfl b policy success
  let r : Fin (2 ^ (d + 1)) := ⟨2 * i.val, by rw [pow_succ]; omega⟩
  let s : Fin (2 ^ (d + 1)) := ⟨2 * j.val, by rw [pow_succ]; omega⟩
  have ri : r.val / 2 = i.val := by dsimp [r]; omega
  have sj : s.val / 2 = j.val := by dsimp [s]; omega
  have phaseR : terminalPhase r = prefixPhase d i := by unfold terminalPhase prefixPhase; rw [ri]
  have phaseS : terminalPhase s = prefixPhase d j := by unfold terminalPhase prefixPhase; rw [sj]
  have half : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [pow_succ]; omega
  have distance := scaling r s
  simp only [phaseR, phaseS, prefixCircularDistance, ri, sj, half] at distance
  rw [closed_phase_ball_overlap, distance]
  have integerShell (k : Nat) : (k : ℝ) ≤ eps ↔ k < m := by
    constructor
    · intro bound
      exact_mod_cast (lt_of_le_of_lt bound upper)
    · intro small
      have natural : k ≤ m - 1 := by omega
      have real : (k : ℝ) ≤ ((m - 1 : Nat) : ℝ) := by exact_mod_cast natural
      have cast : ((m - 1 : Nat) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
  rw [show (2 * ((min (Nat.dist i.val j.val)
      (2 ^ d - Nat.dist i.val j.val) : Nat) : ℝ) ≤ 2 * eps) ↔
      ((min (Nat.dist i.val j.val) (2 ^ d - Nat.dist i.val j.val) : Nat) : ℝ) ≤ eps
      from by constructor <;> intro bound <;> linarith]
  rw [integerShell]
  have hi := i.isLt
  have hj := j.isLt
  unfold Nat.dist Near
  omega

/-- Coloring transport uses all and only the actual supported raw types. -/
theorem actual_supported_coloring_iff {Z : Type*} (d : Nat) (b : Fin 2)
    (D m : Nat) (eps : ℝ) (deadline : sharpWait (d + 1) ≤ D) (hm : 2 ≤ m)
    (lower : (m : ℝ) - 1 ≤ eps) (upper : eps < (m : ℝ)) :
    (∃ color : Fin (2 ^ d) × Fin 2 → Z, ActualTypeColoring d b D eps color) ↔
      ∃ color : Vertex (actualDemand d b D) → Z, Proper m (actualDemand d b D) color := by
  classical
  let e := supportedTypeRankEquiv d b D
  have prefixPreserved (v : Vertex (actualDemand d b D)) : (e.symm v).val.1 = v.1 := rfl
  have prefixPreserved' (x : {x : Fin (2 ^ d) × Fin 2 // x ∈ actualTypes d b D}) :
      (e x).1 = x.val.1 := rfl
  constructor
  · rintro ⟨color, proper⟩
    refine ⟨fun v => color (e.symm v).val, ?_⟩
    intro x y different near
    apply proper (e.symm x).val (e.symm x).property (e.symm y).val (e.symm y).property
    · intro equal
      exact different (e.symm.injective (Subtype.ext equal))
    · apply (actual_phase_overlap_near d b D m eps deadline hm lower upper _ _).mpr
      simpa only [prefixPreserved] using near
  · rintro ⟨color, proper⟩
    let x0 : Fin (2 ^ d) × Fin 2 := (⟨0, Nat.two_pow_pos d⟩, 0)
    have supported0 : x0 ∈ actualTypes d b D := by
      simp only [actualTypes, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [actual_deadline_raw_parity_support d b D 0 deadline (Nat.two_pow_pos d)]
      left
      simp [x0]
    let totalColor : Fin (2 ^ d) × Fin 2 → Z := fun x =>
      if hx : x ∈ actualTypes d b D then color (e ⟨x, hx⟩) else color (e ⟨x0, supported0⟩)
    refine ⟨totalColor, ?_⟩
    intro x hx y hy different overlap
    simp only [totalColor, dif_pos hx, dif_pos hy]
    apply proper (e ⟨x,hx⟩) (e ⟨y,hy⟩)
    · intro equal
      exact different (congrArg Subtype.val (e.injective equal))
    · have near :=
        (actual_phase_overlap_near d b D m eps deadline hm lower upper x.1 y.1).mp overlap
      simpa only [prefixPreserved'] using near

private theorem original_graph_minimum (j h m a rho : Nat) (b : Fin 2) (hj : 2 ≤ j) (hm : 2 ≤ m)
    (shell : 3 + Nat.log2 m ≤ j) (decomposition : 2 ^ (j - 1) = m * a + rho)
    (remainder : rho < m) (slack : 2 * rho ≤ a) :
    let d := j - 1
    let n := 2 ^ d
    let D := (j - 1) * 2 ^ j + 1 + h
    let k : Fin n → Nat := fun t => (actualParitySupport d b D t.val).card
    let q := ((Finset.Icc 1 j).filter (fun i => 2 ^ i ≤ h)).card
    let L := j - q
    let capacity := max (2 * m) ((2 * n - L + a - 1) / a)
    IsLeast {c : Nat | ∃ color : Vertex k → Fin c, Proper m k color} capacity ∧
      capacity = 2 * m + if L < 2 * rho then 1 else 0 := by
  classical
  dsimp only
  have counts :
      let d := j - 1
      let n := 2 ^ d
      let D := (j - 1) * 2 ^ j + 1 + h
      let q := ((Finset.Icc 1 j).filter (fun i => 2 ^ i ≤ h)).card
      let L := j - q
      ((Finset.univ : Finset (Fin n)).filter
        (fun t => (actualParitySupport d b D t.val).card = 1)).card = L ∧
      (actualTypes d b D).card = 2 * n - L
      := by
    classical
    dsimp only
    have depth : j - 1 + 1 = j := by omega
    have wait : sharpWait j = (j - 1) * 2 ^ j + 1 := by
      simp [sharpWait, show j ≠ 0 by omega]
    obtain ⟨_, singles, types⟩ := actual_deadline_staircase (j - 1) h b
    simp only [depth, wait] at singles types
    have qBound : ((Finset.Icc 1 j).filter (fun i => 2 ^ i ≤ h)).card ≤ j := by
      have bound := Finset.card_filter_le (s := Finset.Icc 1 j) (fun i => 2 ^ i ≤ h)
      simpa using bound
    have power : 2 ^ j = 2 * 2 ^ (j - 1) := by
      conv_lhs => rw [← depth, pow_succ]
      omega
    have small : j ≤ 2 ^ j := (Nat.lt_two_pow_self).le
    refine ⟨singles, ?_⟩
    omega
  have windowFacts :
      let d := j - 1
      let n := 2 ^ d
      let D := (j - 1) * 2 ^ j + 1 + h
      2 * m < n ∧
      ∀ t : Nat, t < m → t < n ∧ actualParitySupport d b D t = Finset.univ
      := by
    classical
    dsimp only
    let f := Nat.log2 m
    have upper : m < 2 ^ (f + 1) := by
      simpa [f, Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by decide : 1 < (2 : Nat)) m
    have low : 2 ^ f ≤ m := by
      simpa [f, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    have depth : j - 1 + 1 = j := by omega
    have expBound : f + 2 ≤ j - 1 := by dsimp [f]; omega
    have powerBound : 2 ^ (f + 2) ≤ 2 ^ (j - 1) := Nat.pow_le_pow_right (by decide) expBound
    have twice : 2 ^ (f + 2) = 2 * 2 ^ (f + 1) := by rw [pow_succ]; omega
    have large : 2 * m < 2 ^ (j - 1) := by omega
    have wait : sharpWait j = (j - 1) * 2 ^ j + 1 := by
      simp [sharpWait, show j ≠ 0 by omega]
    refine ⟨large, ?_⟩
    intro t ht
    have tn : t < 2 ^ (j - 1) := by omega
    have tf : t < 2 ^ (f + 1) := by omega
    obtain ⟨weightBound, top, _⟩ := (exceptional_prefix_timing (f + 1)).2.2.2 t tf
    have weight : t.bitIndices.length ≤ f := by
      by_contra nope
      have equal : t.bitIndices.length = f + 1 := by omega
      have value := top equal
      omega
    have extra := (exceptional_prefix_timing (j - 1)).2.2.1 t tn (by omega)
    have deadline : sharpWait (j - 1 + 1) ≤ (j - 1) * 2 ^ j + 1 + h := by
      rw [depth, wait]; omega
    have allowed : earliestTime (j - 1) t + 2 ^ (j - 1 + 1) ≤
        (j - 1) * 2 ^ j + 1 + h := extra.trans deadline
    refine ⟨tn, ?_⟩
    ext nu
    rw [actual_deadline_raw_parity_support (j - 1) b _ t deadline tn nu]
    simp [allowed]
  dsimp only at counts windowFacts
  let d := j - 1
  let n := 2 ^ d
  let D := (j - 1) * 2 ^ j + 1 + h
  let k : Fin n → Nat := fun t => (actualParitySupport d b D t.val).card
  have depth : j - 1 + 1 = j := by omega
  have wait : sharpWait j = (j - 1) * 2 ^ j + 1 := by
    simp [sharpWait, show j ≠ 0 by omega]
  have demands (t : Fin n) : k t = 1 ∨ k t = 2 := by
    obtain ⟨shape, _, _⟩ := actual_deadline_staircase (j - 1) h b
    have supp := shape t
    simp only [depth, wait] at supp
    dsimp [k, d, D]
    rw [supp]
    split_ifs <;> simp
  have hsize : m ≤ n := by dsimp [n, d]; omega
  let start : Fin n := ⟨0, Nat.two_pow_pos d⟩
  have window (i : Fin m) : k (cyclicIndex hsize start i) = 2 := by
    have original := windowFacts.2 i.val i.isLt
    have index : cyclicIndex hsize start i = (⟨i.val, original.1⟩ : Fin n) := by
      apply Fin.ext
      dsimp [cyclicIndex, start]
      rw [if_pos (by omega)]
      omega
    rw [index]
    dsimp [k, d, D]
    rw [original.2]
    simp
  have minimum := mixed_demand_minimum hm windowFacts.1 decomposition remainder slack
    k demands start window
  dsimp only at minimum
  dsimp [k, n, d, D] at minimum
  rw [counts.1] at minimum
  exact minimum

/-- The original all-policy, all-source, all-closed-error repair minimum. -/
theorem original_operational_minimum (j h m a rho : Nat) (b : Fin 2) (eps : ℝ)
    (hj : 2 ≤ j) (hm : 2 ≤ m) (lower : (m : ℝ) - 1 ≤ eps) (upper : eps < (m : ℝ))
    (shell : 3 + Nat.log2 m ≤ j) (decomposition : 2 ^ (j - 1) = m * a + rho)
    (remainder : rho < m) (slack : 2 * rho ≤ a) :
    let d := j - 1
    let n := 2 ^ d
    let D := (j - 1) * 2 ^ j + 1 + h
    let q := ((Finset.Icc 1 j).filter (fun i => 2 ^ i ≤ h)).card
    let L := j - q
    let capacity := max (2 * m) ((2 * n - L + a - 1) / a)
    IsLeast {c : Nat | ∃ writer : (Record → Action (2 ^ (d + 1))) → Record → Fin c,
      CommonRepairFeasible d b D eps writer} capacity ∧
      capacity = 2 * m + if L < 2 * rho then 1 else 0 := by
  classical
  dsimp only
  have depth : j - 1 + 1 = j := by omega
  have wait : sharpWait j = (j - 1) * 2 ^ j + 1 := by
    simp [sharpWait, show j ≠ 0 by omega]
  have deadline : sharpWait (j - 1 + 1) ≤ (j - 1) * 2 ^ j + 1 + h := by
    rw [depth, wait]; omega
  have correspondence (c : Nat) :
      (∃ writer : (Record → Action (2 ^ (j - 1 + 1))) → Record → Fin c,
        CommonRepairFeasible (j - 1) b ((j - 1) * 2 ^ j + 1 + h) eps writer) ↔
      ∃ color : Vertex (fun t : Fin (2 ^ (j - 1)) =>
        (actualParitySupport (j - 1) b ((j - 1) * 2 ^ j + 1 + h) t.val).card) → Fin c,
        Proper m (fun t => (actualParitySupport (j - 1) b
          ((j - 1) * 2 ^ j + 1 + h) t.val).card) color := by
    exact (actual_all_history_coloring_iff _ _ _ _).trans
      (actual_supported_coloring_iff _ _ _ _ _ deadline hm lower upper)
  obtain ⟨minimum, formula⟩ := original_graph_minimum j h m a rho b hj hm shell
    decomposition remainder slack
  refine ⟨⟨(correspondence _).mpr minimum.1, ?_⟩, formula⟩
  intro c member
  exact minimum.2 ((correspondence c).mp member)

end D5.S3.Observer.Budget.ActualDyadicDeadlineRepairMinimum
