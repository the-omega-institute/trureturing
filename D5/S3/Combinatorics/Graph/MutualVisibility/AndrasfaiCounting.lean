/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Closed Boolean labelled runs of the four-state machine are counted by transfer traces. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer
import D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence

/-! Boolean labels are summed before intermediate states, preserving parallel labels. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting

open scoped BigOperators Matrix
open AndrasfaiLanguage
open CycleItalianDominationRecurrence

/-- The four live states embed as the first four states of the original DFA. -/
def liveState (q : Fin 4) : Fin 5 := q.castSucc

/-- Closed runs retain both their Boolean word and their labelled starting state. -/
def ClosedRun (N : ℕ) :=
  {p : (Fin N → Bool) × Fin 4 //
    machine.evalFrom (liveState p.2) (List.ofFn p.1) = liveState p.2}

instance closedRunFintype (N : ℕ) : Fintype (ClosedRun N) := by
  unfold ClosedRun
  infer_instance

private def edgeWeight (q r : Fin 4) : ℤ :=
  ∑ b : Bool, if machine.step (liveState q) b = liveState r then 1 else 0

private def integerTransfer : Matrix (Fin 4) (Fin 4) ℤ := edgeWeight

private theorem integer_transfer_map :
    integerTransfer.map (Int.castRingHom ℚ) = AndrasfaiTransfer.transfer := by
  decide +kernel

private theorem live_ne_reject (q : Fin 4) : liveState q ≠ 4 := by
  intro h
  have hv := congrArg Fin.val h
  have hq := q.isLt
  norm_num [liveState] at hv
  omega

private theorem split_step (q r : Fin 4) (b : Bool) (w : List Bool) :
    (if machine.evalFrom (liveState q) (b :: w) = liveState r then (1 : ℤ) else 0) =
      ∑ s : Fin 4,
        (if machine.step (liveState q) b = liveState s then (1 : ℤ) else 0) *
        (if machine.evalFrom (liveState s) w = liveState r then 1 else 0) := by
  rw [DFA.evalFrom_cons]
  generalize machine.step (liveState q) b = t
  by_cases ht : t = 4
  · subst t
    have habs : machine.evalFrom 4 w = 4 :=
      List.foldl_fixed' (by decide +kernel) w
    have hne (s : Fin 4) : (4 : Fin 5) ≠ liveState s := (live_ne_reject s).symm
    simp [habs, hne]
  · have hlt : t.val < 4 := by
      have := t.isLt
      have : t.val ≠ 4 := by
        intro hv
        apply ht
        apply Fin.ext
        simpa using hv
      omega
    let s : Fin 4 := ⟨t.val, hlt⟩
    have hs : t = liveState s := by apply Fin.ext; rfl
    rw [hs]
    simp [liveState, Fin.castSucc_inj]

private theorem labelled_paths (n : ℕ) (q r : Fin 4) :
    (∑ labels : Fin (n+1) → Bool,
      if machine.evalFrom (liveState q) (List.ofFn labels) = liveState r
      then (1 : ℤ) else 0) =
    ∑ f : Fin n → Fin 4, pathWeight integerTransfer q f r := by
  induction n generalizing q with
  | zero =>
      rw [← (Fin.consEquiv (fun _ : Fin 1 => Bool)).sum_comp,
        Fintype.sum_prod_type]
      change (∑ b : Bool, ∑ f : Fin 0 → Bool,
        if machine.evalFrom (liveState q) (b :: List.ofFn f) = liveState r
        then (1 : ℤ) else 0) = _
      simp [pathWeight, integerTransfer, edgeWeight]
  | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n+2) => Bool)).sum_comp,
        Fintype.sum_prod_type]
      change (∑ b : Bool, ∑ labels : Fin (n+1) → Bool,
        if machine.evalFrom (liveState q) (List.ofFn (Fin.cons b labels)) = liveState r
        then (1 : ℤ) else 0) = _
      simp only [List.ofFn_cons]
      simp_rw [split_step]
      conv_lhs =>
        arg 2
        intro b
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ih]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      change (∑ s : Fin 4, integerTransfer q s *
        ∑ f : Fin n → Fin 4, pathWeight integerTransfer s f r) = _
      conv_rhs =>
        rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 4)).sum_comp,
          Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      change integerTransfer q s * pathWeight integerTransfer s f r =
        pathWeight integerTransfer q (Fin.cons s f) r
      simp only [pathWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.cons_last, Fin.castSucc_zero, Fin.castSucc_succ]
      ring

/-- Every positive-length closed Boolean labelled run contributes exactly once
 to the trace, including both labels on the state-three to state-one edge. -/
theorem closed_run_card_eq_trace (N : ℕ) (hN : 0 < N) :
    (Fintype.card (ClosedRun N) : ℚ) =
      Matrix.trace (AndrasfaiTransfer.transfer ^ N) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hc : (Fintype.card (ClosedRun (n+1)) : ℤ) =
      ∑ p : (Fin (n+1) → Bool) × Fin 4,
        if machine.evalFrom (liveState p.2) (List.ofFn p.1) = liveState p.2
        then (1 : ℤ) else 0 := by
    unfold ClosedRun
    rw [Fintype.card_subtype]
    exact (Finset.sum_boole _ _).symm
  have hz : (Fintype.card (ClosedRun (n+1)) : ℤ) =
      Matrix.trace (integerTransfer ^ (n+1)) := by
    rw [hc, Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [labelled_paths, sum_pathWeight]
    rfl
  have hq := congrArg (Int.castRingHom ℚ) hz
  rw [AddMonoidHom.map_trace, Matrix.map_pow, integer_transfer_map] at hq
  change ((Fintype.card (ClosedRun (n+1)) : ℤ) : ℚ) = _ at hq
  simpa only [Int.cast_natCast] using hq

end D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting
