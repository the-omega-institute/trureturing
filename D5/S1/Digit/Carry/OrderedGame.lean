/- GID: D5/S1/Digit/Carry/OrderedGame
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/OrderedGame
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every finite ordered game path satisfies the carry-reward inversion potential bound. -/

import D5.S1.Digit.Raw
import D5.S1.Digit.Carry.ListInversions
import D5.S1.Digit.Carry.SplitStabilization

namespace D5.S1.Digit.Carry.OrderedGame

open ListInversions

/-- Decode raw W indices to the paper's positive indices. -/
def decode (s : List ℕ) : List ℕ := s.map Nat.succ

/-- Multiplicities, not a position-indexed finitely supported list. -/
noncomputable def rawCounts (s : List ℕ) : RawDigits :=
  Multiset.toFinsupp (s : Multiset ℕ)

/-- Labels retain the raw carry index; a switch has no carry reward. -/
inductive Action where
  | switch
  | ones
  | twos
  | split (i : ℕ)
  | merge (a : ℕ)

/-- All five contextual adjacent moves, in zero-based indices. The general
split at raw index i+2 decodes to the paper's split at positive index i+3. -/
inductive Move : ℕ → Action → List ℕ → List ℕ → Prop where
  | switch (P S : List ℕ) (i j : ℕ) (h : j < i) :
      Move P.length .switch (P ++ [i, j] ++ S) (P ++ [j, i] ++ S)
  | ones (P S : List ℕ) : Move P.length .ones (P ++ [0, 0] ++ S) (P ++ [1] ++ S)
  | twos (P S : List ℕ) : Move P.length .twos (P ++ [1, 1] ++ S) (P ++ [0, 2] ++ S)
  | split (P S : List ℕ) (i : ℕ) :
      Move P.length (.split i) (P ++ [i + 2, i + 2] ++ S) (P ++ [i, i + 3] ++ S)
  | merge (P S : List ℕ) (a : ℕ) :
      Move P.length (.merge a) (P ++ [a, a + 1] ++ S) (P ++ [a + 2] ++ S)

/-- Full carry-then-sort reward, including the carry itself. -/
noncomputable def reward (s : List ℕ) : Action → ℕ
  | .switch => 0
  | .ones => rawCounts s 0 - 1
  | .twos => rawCounts s 1 - 1
  | .split i => rawCounts s (i + 1) + rawCounts s (i + 2) - 1
  | .merge a => rawCounts s (a + 1)

/-- Finite legal paths retain both actual move count and summed carry reward. -/
inductive Path : List ℕ → List ℕ → ℕ → ℕ → Prop where
  | nil (s) : Path s s 0 0
  | cons {position a s t u length weight} (move : Move position a s t)
      (tail : Path t u length weight) :
      Path s u (length + 1) (reward s a + weight)

/-- The consumed raw digits of a carry label. Switches are excluded by RawMove. -/
noncomputable def rawInput : Action → RawDigits
  | .switch => 0
  | .ones => Finsupp.single 0 2
  | .twos => Finsupp.single 1 2
  | .split i => Finsupp.single (i + 2) 2
  | .merge a => Finsupp.single a 1 + Finsupp.single (a + 1) 1

/-- The produced raw digits of a carry label. -/
noncomputable def rawOutput : Action → RawDigits
  | .switch => 0
  | .ones => splitOutput 0
  | .twos => splitOutput 1
  | .split i => splitOutput (i + 2)
  | .merge a => Finsupp.single (a + 2) 1

/-- A label together with the actual existing carry relation and its context. -/
def RawMove (a : Action) (c d : RawDigits) : Prop :=
  CarryStep c d ∧ ∃ rest, c = rest + rawInput a ∧
    d = rest + rawOutput a ∧ a ≠ .switch

/-- Full raw carry reward, sharing the split reward used in stabilization. -/
def rawReward (c : RawDigits) : Action → ℕ
  | .switch => 0
  | .ones => splitReward c 0
  | .twos => splitReward c 1
  | .split i => splitReward c (i + 2)
  | .merge a => c (a + 1)

/-- Labelled weighted raw paths. Carry labels are explicit data; no data is
recovered by eliminating a proof of the unlabelled CarryStep proposition. -/
inductive RawPath : RawDigits → RawDigits → ℕ → Prop where
  | nil (c) : RawPath c c 0
  | cons {a c d e w} (move : RawMove a c d) (tail : RawPath d e w) :
      RawPath c e (rawReward c a + w)

/-- Erasing all ordered switches preserves the complete accumulated reward
and maps every remaining move to a labelled instance of the existing carries. -/
theorem path_raw_erasure {s t : List ℕ} {length weight : ℕ}
    (path : Path s t length weight) : RawPath (rawCounts s) (rawCounts t) weight := by
  classical
  have context (P M S : List ℕ) :
      rawCounts (P ++ M ++ S) = rawCounts (P ++ S) + rawCounts M := by
    ext k
    simp [rawCounts, Multiset.toFinsupp_apply, List.count_append]
    omega
  have erase_move {p a s t} (step : Move p a s t) :
      (a = .switch ∧ rawCounts s = rawCounts t) ∨ RawMove a (rawCounts s) (rawCounts t) := by
    cases step with
    | switch P S i j h =>
      left
      refine ⟨rfl, ?_⟩
      ext k
      simp [rawCounts, Multiset.toFinsupp_apply, List.count_append, List.count_cons]
      omega
    | ones P S | twos P S | split P S i | merge P S i =>
      right
      rw [context, context]
      have inputs : ∀ (i : ℕ), rawCounts [i, i] = Finsupp.single i 2 := by
        intro i; ext k
        simp only [rawCounts, Multiset.toFinsupp_apply, Multiset.coe_count,
          Finsupp.single_apply, List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      have outputs : ∀ (i : ℕ), rawCounts [i] = Finsupp.single i 1 := by
        intro i; ext k
        simp [rawCounts, Finsupp.single_apply]
      have pair : ∀ (i j : ℕ), rawCounts [i, j] =
          Finsupp.single i 1 + Finsupp.single j 1 := by
        intro i j; ext k
        simp only [rawCounts, Multiset.toFinsupp_apply, Multiset.coe_count,
          Finsupp.add_apply, Finsupp.single_apply, List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      first
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [inputs, outputs, add_assoc] using CarryStep.double_zero (rawCounts (P ++ S))
        · simp [rawInput, inputs]
        · simp [rawOutput, splitOutput, outputs]
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [inputs, pair, add_assoc] using CarryStep.double_one (rawCounts (P ++ S))
        · simp [rawInput, inputs]
        · simp [rawOutput, splitOutput, pair]
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [inputs, pair, add_assoc] using CarryStep.double_succ (rawCounts (P ++ S)) i
        · simp [rawInput, inputs]
        · simp [rawOutput, splitOutput, pair]
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [pair, outputs, add_assoc] using CarryStep.adjacent (rawCounts (P ++ S)) i
        · simp [rawInput, pair]
        · simp [rawOutput, outputs]
  induction path with
  | nil => exact .nil _
  | cons step tail ih =>
    rcases erase_move step with ⟨rfl, same⟩ | carry
    · simpa [reward, same] using ih
    · have h := RawPath.cons carry ih
      convert h using 1
      cases step <;> rfl

/-- A natural-number telescope bounds every legal ordered path, including
arbitrary switch choices, by its raw carry reward and initial inversions. -/
theorem path_potential {s t : List ℕ} {length weight : ℕ}
    (path : Path s t length weight) :
    length + inv (decode t) ≤ inv (decode s) + weight := by
  have local_bound {position a s t} (step : Move position a s t) :
      1 + inv (decode t) ≤ inv (decode s) + reward s a := by
    have counts (l : List ℕ) (k : ℕ) :
        (l.map Nat.succ).count (k + 1) = l.count k :=
      List.count_map_of_injective l Nat.succ Nat.succ_injective k
    cases step with
    | switch P S i j h =>
      simp only [decode, List.map_append, List.map_cons, List.map_nil, reward]
      rw [inv_window, inv_window]
      simp [inv, show ¬i + 1 < j + 1 by omega, show j + 1 < i + 1 by omega]
      omega
    | ones P S =>
      have h := inv_replace_ones (decode P) (decode S)
      simp only [decode, ← List.map_append] at h
      rw [show 1 = 0 + 1 from rfl, counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
    | twos P S =>
      have h := inv_replace_twos (decode P) (decode S)
      simp only [decode, ← List.map_append] at h
      rw [show 2 = 1 + 1 from rfl, counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
    | split P S i =>
      have h := inv_replace_double (decode P) (decode S) (i + 3) (by omega)
      simp only [decode, ← List.map_append] at h
      rw [show i + 3 - 2 = i + 1 by omega,
        show i + 3 - 1 = (i + 1) + 1 by omega,
        show i + 3 = (i + 2) + 1 by omega, counts, counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
    | merge P S a =>
      have h := inv_replace_adjacent (decode P) (decode S) (a + 1)
      simp only [decode, ← List.map_append] at h
      rw [counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
  induction path with
  | nil => simp
  | cons step tail ih => have := local_bound step; omega

/-- Strategy priorities are restarted at each state. -/
def priority : Action → ℕ
  | .switch => 0
  | .ones => 1
  | .twos | .split _ => 2
  | .merge _ => 3

/-- All switches tie; ones and merges choose the leftmost position, splits
choose the rightmost position. No order is imposed on switch choices. -/
def Preferred (p : ℕ) (a : Action) (q : ℕ) (b : Action) : Prop :=
  priority a < priority b ∨
    (priority a = priority b ∧
      (((priority a = 1 ∨ priority a = 3) ∧ p < q) ∨
        (priority a = 2 ∧ q < p)))

/-- Actual legal moves satisfying the complete relational LGS priority. -/
def LGSMove (p : ℕ) (a : Action) (s t : List ℕ) : Prop :=
  Move p a s t ∧ ∀ q b u, Move q b s u → ¬Preferred q b p a

/-- Every permitted switch choice is retained in the complete strategy relation. -/
inductive LGSPath : List ℕ → List ℕ → ℕ → ℕ → Prop where
  | nil (s) : LGSPath s s 0 0
  | cons {p a s t u length weight} (move : LGSMove p a s t)
      (tail : LGSPath t u length weight) :
      LGSPath s u (length + 1) (reward s a + weight)

/-- No legal ordered operation is enabled. -/
def Terminal (s : List ℕ) : Prop := ∀ p a t, ¬Move p a s t

/-- The full source target, including nonvacuous completion. This definition
records an unproved proposition, not a resolution of the conjecture. -/
def Conjecture17 : Prop :=
  (∀ n, 0 < n → ∃ t length weight,
    LGSPath (List.replicate n 0) t length weight ∧ Terminal t) ∧
  (∀ n, 0 < n → ∀ g gl gw h hl hw,
    LGSPath (List.replicate n 0) g gl gw → Terminal g →
    Path (List.replicate n 0) h hl hw → Terminal h → hl ≤ gl)

end D5.S1.Digit.Carry.OrderedGame
