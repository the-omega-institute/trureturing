/- GID: D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy
   mirror-E: none(waiver:analytic-competitive-bound)
   anchors: []
   utility: none
   digest: A guarded deterministic threshold rule for repeated rent-or-buy. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A guarded threshold rule for repeated rent-or-buy

Each list entry is the increment newly visible on a billed call after call one.
Cost includes the full rent on reset calls. The guard spends at most one extra reset,
and enables it only after an ordinary reset on a strictly earlier call.
-/

set_option autoImplicit false

namespace GuardedRentOrBuy

noncomputable section

open Classical

/-- The carry after the previous decision, unfinished-cycle rent, and prefix flags. -/
structure State where
  carry : ℝ
  acc : ℝ
  previous : Option ℝ
  ordinarySeen : Bool
  dropSeen : Bool

def initial : State := ⟨0, 0, none, false, false⟩

def crossing (K : ℝ) (s : State) (a : ℝ) : Prop := K ≤ s.acc + (s.carry + a)

def drop (s : State) (a : ℝ) : Prop :=
  s.previous.elim False (fun previous => a < previous)

def reset (K : ℝ) (s : State) (a : ℝ) : Bool :=
  decide (crossing K s a ∨ (drop s a ∧ s.ordinarySeen = true ∧ s.dropSeen = false))

def advance (K : ℝ) (s : State) (a : ℝ) : State :=
  { carry := if reset K s a then 0 else s.carry + a
    acc := if reset K s a then 0 else s.acc + (s.carry + a)
    previous := some a
    ordinarySeen := s.ordinarySeen || decide (crossing K s a)
    dropSeen := s.dropSeen || decide (drop s a) }

def nextCarry (o a : ℝ) (r : Bool) : ℝ := if r then 0 else o + a

def bill (K o a : ℝ) (r : Bool) : ℝ := o + a + (if r then K else 0)

def comparatorCost (K : ℝ) (o : ℝ) : List (ℝ × Bool) → ℝ
  | [] => 0
  | (a, r) :: rest => bill K o a r + comparatorCost K (nextCarry o a r) rest

def policyCost (K : ℝ) (s : State) : List ℝ → ℝ
  | [] => 0
  | a :: rest => bill K s.carry a (reset K s a) + policyCost K (advance K s a) rest

/-- The action on call one is false. Each later action is calculated from its visible prefix. -/
def prefixRule (K : ℝ) (seen : List ℝ) : Bool :=
  match seen.getLast? with
  | none => false
  | some a => reset K (seen.dropLast.foldl (advance K) initial) a

@[simp] theorem prefixRule_nil (K : ℝ) : prefixRule K [] = false := rfl

@[local simp] private theorem prefixRule_snoc (K : ℝ) (xs : List ℝ) (a : ℝ) :
    prefixRule K (xs ++ [a]) = reset K (xs.foldl (advance K) initial) a := by
  simp [prefixRule]

def scheduled (K : ℝ) (s : State) : List ℝ → List (ℝ × Bool)
  | [] => []
  | a :: rest => (a, reset K s a) :: scheduled K (advance K s a) rest

/-- On call one the guard cannot create an extra reset. -/
theorem ordinary_initial (K a : ℝ) :
    reset K initial a = decide (crossing K initial a) := by
  have hd : ¬ drop initial a := by simp [drop, initial]
  by_cases hc : crossing K initial a <;> simp [reset, hd, hc]

/-- Computing bills from the recorded decisions gives the policy cost. -/
theorem scheduled_cost (K : ℝ) (s : State) (xs : List ℝ) :
    comparatorCost K s.carry (scheduled K s xs) = policyCost K s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [scheduled, comparatorCost, policyCost]
    rw [show nextCarry s.carry a (reset K s a) = (advance K s a).carry from rfl, ih]

/-- The recorded action at every position agrees with evaluating the rule on the visible prefix. -/
theorem scheduled_prefix (K : ℝ) (seen tail : List ℝ) (i : ℕ) (a : ℝ) (r : Bool)
    (h : (scheduled K (seen.foldl (advance K) initial) tail)[i]? = some (a, r)) :
    prefixRule K (seen ++ tail.take (i + 1)) = r := by
  induction tail generalizing seen i with
  | nil => simp [scheduled] at h
  | cons b rest ih =>
    cases i with
    | zero =>
      simp only [scheduled, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      simpa using h.2
    | succ i =>
      have hs : (seen ++ [b]).foldl (advance K) initial =
          advance K (seen.foldl (advance K) initial) b := by simp
      rw [scheduled, List.getElem?_cons_succ, ← hs] at h
      simpa [List.append_assoc] using ih (seen ++ [b]) i h

private def reserve (K : ℝ) (s : State) : ℝ :=
  if s.ordinarySeen && !s.dropSeen then K else 0

private theorem reserve_nonneg (K : ℝ) (s : State) (hK : 0 ≤ K) :
    0 ≤ reserve K s := by
  unfold reserve
  split <;> linarith

private theorem reserve_le (K : ℝ) (s : State) (hK : 0 ≤ K) :
    reserve K s ≤ K := by
  unfold reserve
  split <;> linarith

/-- A comparator's bills account for all newly seen increments, and either include a reset
price or dominate the rents of the online policy while both schedules retain their carry. -/
theorem billed_cycle {K e A o q a : ℝ} {r : Bool}
    (hK : 0 ≤ K) (hEA : e ≤ A) (ho : 0 ≤ o)
    (hcycle : e + K ≤ q ∨ (A ≤ q ∧ e ≤ o)) :
    e + a + K ≤ q + bill K o a r ∨
      (A + (e + a) ≤ q + bill K o a r ∧ e + a ≤ nextCarry o a r) := by
  cases r
  · rcases hcycle with h | ⟨h₁, h₂⟩
    · left
      simp [bill]
      linarith
    · right
      simp [bill, nextCarry]
      exact ⟨by linarith, by linarith⟩
  · left
    have h : e ≤ q := by rcases hcycle with h | ⟨h, _⟩ <;> linarith
    simp [bill]
    linarith

private theorem competitive_from (K : ℝ) (hK : 0 < K) (steps : List (ℝ × Bool))
    (ha : ∀ p ∈ steps, 0 ≤ p.1) (s : State) (o q : ℝ)
    (he : 0 ≤ s.carry) (hEA : s.carry ≤ s.acc) (hA : s.acc < K) (ho : 0 ≤ o)
    (hcycle : s.carry + K ≤ q ∨ (s.acc ≤ q ∧ s.carry ≤ o)) :
    policyCost K s (steps.map Prod.fst) + s.acc ≤
      3 * (q + comparatorCost K o steps) + reserve K s := by
  induction steps generalizing s o q with
  | nil =>
    have hr := reserve_nonneg K s hK.le
    rcases hcycle with h | ⟨h, _⟩ <;> simp [policyCost, comparatorCost] <;> linarith
  | cons p rest ih =>
    obtain ⟨a, r⟩ := p
    have han := ha (a, r) (by simp)
    have ha' : ∀ p ∈ rest, 0 ≤ p.1 := fun p hp => ha p (by simp [hp])
    let H := s.carry + a
    let Q := q + bill K o a r
    let O := nextCarry o a r
    let t := advance K s a
    have hH : 0 ≤ H := add_nonneg he han
    have hO : 0 ≤ O := by
      cases r <;> simp [O, nextCarry, add_nonneg ho han]
    have hQ : H + K ≤ Q ∨ (s.acc + H ≤ Q ∧ H ≤ O) :=
      billed_cycle hK.le hEA ho hcycle
    have hr₀ := reserve_nonneg K s hK.le
    have hr₁ := reserve_le K t hK.le
    have finish_reset (hb : reset K s a = true)
        (hcharge : s.acc + H + K + reserve K t ≤ 3 * Q + reserve K s) :
        bill K s.carry a (reset K s a) + policyCost K t (rest.map Prod.fst) + s.acc ≤
          3 * (q + (bill K o a r + comparatorCost K O rest)) + reserve K s := by
      have ht : t.carry = 0 ∧ t.acc = 0 := by simp [t, advance, hb]
      have hi := ih ha' t O 0 (by simp [ht.1]) (by simp [ht.1, ht.2])
        (by simpa [ht.2]) hO (Or.inr ⟨by simp [ht.2], by simpa [ht.1] using hO⟩)
      rw [ht.2, add_zero, zero_add] at hi
      rw [hb, show bill K s.carry a true = H + K from rfl]
      change H + K + policyCost K t (rest.map Prod.fst) + s.acc ≤
        3 * (q + (bill K o a r + comparatorCost K O rest)) + reserve K s
      dsimp only [Q] at hcharge
      linarith
    have finish_rent (hb : reset K s a = false) (hc : ¬ crossing K s a)
        (hr : reserve K t ≤ reserve K s) :
        bill K s.carry a (reset K s a) + policyCost K t (rest.map Prod.fst) + s.acc ≤
          3 * (q + (bill K o a r + comparatorCost K O rest)) + reserve K s := by
      have ht : t.carry = H ∧ t.acc = s.acc + H := by simp [t, advance, hb, H]
      have hi := ih ha' t O Q (ht.1 ▸ hH)
        (by rw [ht.1, ht.2]; linarith) (by rw [ht.2]; exact lt_of_not_ge hc)
        hO (by simpa [ht.1, ht.2] using hQ)
      rw [ht.2] at hi
      rw [hb, show bill K s.carry a false = H by simp [bill, H]]
      change H + policyCost K t (rest.map Prod.fst) + s.acc ≤
        3 * (q + (bill K o a r + comparatorCost K O rest)) + reserve K s
      dsimp only [Q] at hi
      linarith
    simp only [List.map_cons, policyCost, comparatorCost]
    by_cases hc : crossing K s a
    · apply finish_reset (by simp [reset, hc])
      have hc' : K ≤ s.acc + H := hc
      rcases hQ with h | ⟨h, _⟩ <;> linarith
    · by_cases hd : drop s a
      · by_cases hg : s.ordinarySeen = true ∧ s.dropSeen = false
        · apply finish_reset (by simp [reset, hc, hd, hg])
          have hr : reserve K s = K := by simp [reserve, hg.1, hg.2]
          have hr' : reserve K t = 0 := by simp [reserve, t, advance, hd]
          have hc' : s.acc + H < K := lt_of_not_ge hc
          rw [hr, hr', add_zero]
          rcases hQ with h | ⟨h, _⟩ <;> linarith
        · apply finish_rent (by simp [reset, hc, hd, hg]) hc
          simpa [reserve, t, advance, hd] using hr₀
      · apply finish_rent (by simp [reset, hc, hd]) hc
        simp [reserve, t, advance, hc, hd]

/-- Arbitrary-horizon competitive bound, including the forced reset and the last unfinished cycle. -/
theorem factor_three (K : ℝ) (hK : 0 < K) (steps : List (ℝ × Bool))
    (ha : ∀ p ∈ steps, 0 ≤ p.1) (firstReset : Bool) :
    comparatorCost K 0 (scheduled K initial (steps.map Prod.fst)) ≤
      3 * (bill K 0 0 firstReset + comparatorCost K 0 steps) := by
  rw [show (0 : ℝ) = initial.carry from rfl, scheduled_cost]
  have h := competitive_from K hK steps ha initial 0 0 (by simp [initial])
    (by simp [initial]) (by simpa [initial]) le_rfl (Or.inr (by simp [initial]))
  simp [initial, reserve] at h
  cases firstReset <;> simp [bill, initial] <;> linarith

end

end GuardedRentOrBuy
