/- GID: D5/S1/Digit/Carry/OrderedGame
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/OrderedGame
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every finite ordered game path satisfies the carry-reward inversion potential bound. -/

import D5.S1.Digit.Raw
import D5.S1.Digit.Carry.ListInversions

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
