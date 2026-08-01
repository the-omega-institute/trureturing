/- GID: D5/S0/History/MarkerHistorySearch
   generality: G
   mirror-B: D5/B/S0/History/MarkerHistorySearch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Length-layered enumeration and bounded counterexample search for marker histories. -/

import D5.S0.History.HistoryCarrier

namespace D5.S0.History

instance : DecidableEq MarkerHistory := fun a b =>
  if h : a.toList = b.toList then
    isTrue (FreeMonoid.toList.injective h)
  else
    isFalse fun equality => h (congrArg FreeMonoid.toList equality)

/-- All marker histories of exactly the given length. -/
def historiesOfLength : ℕ → List MarkerHistory
  | 0 => [1]
  | n + 1 => (historiesOfLength n).flatMap fun h =>
      [FreeMonoid.of .E₀ * h, FreeMonoid.of .E₁ * h]

/-- Every marker history occurs in its exact length layer. -/
theorem mem_historiesOfLength_length (h : MarkerHistory) :
    h ∈ historiesOfLength h.length := by
  induction h using FreeMonoid.inductionOn' with
  | one => simp [historiesOfLength]
  | mul_of marker h ih =>
      rw [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.one_add]
      cases marker <;>
        simp only [historiesOfLength, List.mem_flatMap] <;>
        exact ⟨h, ih, by simp⟩

/-- All marker histories whose length is at most the given bound. -/
def historiesUpTo (n : ℕ) : List MarkerHistory :=
  (List.range (n + 1)).flatMap historiesOfLength

theorem mem_historiesUpTo_of_length_le (h : MarkerHistory) {n : ℕ}
    (hle : h.length ≤ n) : h ∈ historiesUpTo n := by
  simp only [historiesUpTo, List.mem_flatMap, List.mem_range]
  exact ⟨h.length, Nat.lt_succ_iff.mpr hle, mem_historiesOfLength_length h⟩

/-- Search a finite list for its first history rejected by `D`. -/
def findRejected (D : MarkerHistory → Bool) :
    List MarkerHistory → Option MarkerHistory
  | [] => none
  | h :: hs => if D h then findRejected D hs else some h

theorem findRejected_sound {D : MarkerHistory → Bool} {hs : List MarkerHistory}
    {h : MarkerHistory} (found : findRejected D hs = some h) : D h = false := by
  induction hs with
  | nil => simp [findRejected] at found
  | cons candidate rest ih =>
      cases decision : D candidate with
      | false =>
        simp [findRejected, decision] at found
        subst h
        exact decision
      | true =>
        simp [findRejected, decision] at found
        exact ih found

theorem findRejected_complete {D : MarkerHistory → Bool} {hs : List MarkerHistory}
    (exists_bad : ∃ h ∈ hs, D h = false) :
    ∃ h, findRejected D hs = some h := by
  induction hs with
  | nil => simp at exists_bad
  | cons candidate rest ih =>
      cases decision : D candidate with
      | false => exact ⟨candidate, by simp [findRejected, decision]⟩
      | true =>
        have rest_bad : ∃ h ∈ rest, D h = false := by
          obtain ⟨h, membership, rejected⟩ := exists_bad
          exact ⟨h, (List.mem_cons.mp membership).resolve_left (by
            intro equality
            subst h
            simp [decision] at rejected), rejected⟩
        obtain ⟨h, found⟩ := ih rest_bad
        exact ⟨h, by simp [findRejected, decision, found]⟩

/-- Search every marker history up to length `n` for the first rejected one. -/
def findCounterexample (D : MarkerHistory → Bool) (n : ℕ) :
    Option MarkerHistory :=
  findRejected D (historiesUpTo n)

theorem findCounterexample_sound {D : MarkerHistory → Bool} {n : ℕ}
    {h : MarkerHistory} (found : findCounterexample D n = some h) :
    D h = false :=
  findRejected_sound found

theorem findCounterexample_complete {D : MarkerHistory → Bool} {n : ℕ}
    (exists_bad : ∃ h, h.length ≤ n ∧ D h = false) :
    ∃ h, findCounterexample D n = some h := by
  apply findRejected_complete
  obtain ⟨h, hle, rejected⟩ := exists_bad
  exact ⟨h, mem_historiesUpTo_of_length_le h hle, rejected⟩

example (h : MarkerHistory) : h ∈ historiesOfLength h.length :=
  mem_historiesOfLength_length h

example (D : MarkerHistory → Bool) (n : ℕ) (h : MarkerHistory)
    (found : findCounterexample D n = some h) : D h = false :=
  findCounterexample_sound found

example (D : MarkerHistory → Bool) (n : ℕ)
    (exists_bad : ∃ h, h.length ≤ n ∧ D h = false) :
    ∃ h, findCounterexample D n = some h :=
  findCounterexample_complete exists_bad

def startsWithE₀ : MarkerHistory → Bool
  | [] => true
  | .E₀ :: _ => true
  | .E₁ :: _ => false

-- Non-vacuity witness: the bounded search finds the one-marker history `[E₁]`.
example : findCounterexample startsWithE₀ 1 = some [.E₁] := by decide

#eval findCounterexample startsWithE₀ 1

end D5.S0.History
