/- GID: D5/S0/Certificates/HeterogeneousC4HatGame
   generality: I
   mirror-B: D5/B/S0/Certificates/HeterogeneousC4HatGame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:61990f6065f813ad461fa8c6aa37b6b86118bcfc50d7fca3739e30d696ae5e4c
   digest: Explicit legal strategies win two heterogeneous four-cycle hat games. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.HeterogeneousC4HatGame

/-- A local plan sees the two indicated neighbours and returns exactly `g v`
distinct colours from `Fin (h v)`. Vertices 0,1,2,3 denote A,B,Z,Omega. -/
def LocalPlan (h g : Fin 4 → Nat) (v left right : Fin 4) : Type :=
  Fin (h left) × Fin (h right) →
    {guesses : Finset (Fin (h v)) // guesses.card = g v}

/-- All colourings, in source order A,B,Z,Omega. -/
def Coloring (h : Fin 4 → Nat) : Type :=
  Fin (h 0) × Fin (h 1) × Fin (h 2) × Fin (h 3)

/-- The four legal local plans for the undirected cycle A-B-Z-Omega-A. -/
def Strategy (h g : Fin 4 → Nat) : Type :=
  LocalPlan h g 0 1 3 × LocalPlan h g 1 0 2 ×
    LocalPlan h g 2 1 3 × LocalPlan h g 3 2 0

/-- Own-colour membership in the local guess set at each vertex. -/
def GuessesCorrectly (h g : Fin 4 → Nat) (strategy : Strategy h g)
    (coloring : Coloring h) : Fin 4 → Prop :=
  ![coloring.1 ∈ (strategy.1 (coloring.2.1, coloring.2.2.2)).val,
    coloring.2.1 ∈ (strategy.2.1 (coloring.1, coloring.2.2.1)).val,
    coloring.2.2.1 ∈ (strategy.2.2.1 (coloring.2.1, coloring.2.2.2)).val,
    coloring.2.2.2 ∈ (strategy.2.2.2 (coloring.2.2.1, coloring.1)).val]

/-- Every colouring has at least one correctly guessing vertex. -/
def Wins (h g : Fin 4 → Nat) (strategy : Strategy h g) : Prop :=
  ∀ coloring : Coloring h, ∃ v : Fin 4, GuessesCorrectly h g strategy coloring v

/-- Existence of a legal strategy that wins against every colouring. -/
def Winnable (h g : Fin 4 → Nat) : Prop :=
  ∃ strategy : Strategy h g, Wins h g strategy

private def correctAtBool (h g : Fin 4 → Nat) (strategy : Strategy h g)
    (coloring : Coloring h) : Fin 4 → Bool :=
  ![decide (coloring.1 ∈ (strategy.1 (coloring.2.1, coloring.2.2.2)).val),
    decide (coloring.2.1 ∈ (strategy.2.1 (coloring.1, coloring.2.2.1)).val),
    decide (coloring.2.2.1 ∈ (strategy.2.2.1 (coloring.2.1, coloring.2.2.2)).val),
    decide (coloring.2.2.2 ∈ (strategy.2.2.2 (coloring.2.2.1, coloring.1)).val)]

private theorem correctAtBool_eq_true_iff (h g : Fin 4 → Nat)
    (strategy : Strategy h g) (coloring : Coloring h) (v : Fin 4) :
    correctAtBool h g strategy coloring v = true ↔
      GuessesCorrectly h g strategy coloring v := by
  fin_cases v <;> simp [correctAtBool, GuessesCorrectly]

-- Each matrix is unchanged from the source-aligned probe. Rows and columns
-- are respectively (B,Omega), (A,Z), (B,Omega), and (Z,A).
private def guessesA3443 (seen : Fin 4 × Fin 3) : Finset (Fin 3) :=
  ![![{0, 2}, {0, 2}, {0, 2}],
    ![{0, 1}, {0, 2}, {1, 2}],
    ![{0, 1}, {0, 1}, {0, 1}],
    ![{0, 1}, {1, 2}, {1, 2}]] seen.1 seen.2

private def guessB3443 (seen : Fin 3 × Fin 4) : Fin 4 :=
  ![![3, 3, 3, 1], ![0, 0, 0, 1], ![2, 2, 2, 3]] seen.1 seen.2

private def guessZ3443 (seen : Fin 4 × Fin 3) : Fin 4 :=
  ![![0, 3, 3], ![0, 2, 2], ![0, 3, 3], ![0, 3, 3]] seen.1 seen.2

private def guessO3443 (seen : Fin 4 × Fin 3) : Fin 3 :=
  ![![2, 1, 2], ![2, 1, 0], ![0, 0, 0], ![0, 0, 0]] seen.1 seen.2

private def strategy3443 : Strategy ![3, 4, 4, 3] ![2, 1, 1, 1] :=
  ⟨fun seen => ⟨guessesA3443 seen,
      (by decide : ∀ x, (guessesA3443 x).card = 2) seen⟩,
    fun seen => ⟨{guessB3443 seen}, Finset.card_singleton _⟩,
    fun seen => ⟨{guessZ3443 seen}, Finset.card_singleton _⟩,
    fun seen => ⟨{guessO3443 seen}, Finset.card_singleton _⟩⟩

#count_heartbeats in
private theorem strategy3443_wins_coordinates :
    ∀ (a : Fin 3) (b : Fin 4) (z : Fin 4) (o : Fin 3),
      ∃ v : Fin 4,
        correctAtBool ![3, 4, 4, 3] ![2, 1, 1, 1] strategy3443 ⟨a, b, z, o⟩ v = true := by
  decide

private theorem strategy3443_wins : Wins ![3, 4, 4, 3] ![2, 1, 1, 1] strategy3443 := by
  intro coloring
  obtain ⟨v, correct⟩ := strategy3443_wins_coordinates
    coloring.1 coloring.2.1 coloring.2.2.1 coloring.2.2.2
  exact ⟨v, (correctAtBool_eq_true_iff _ _ strategy3443 coloring v).mp correct⟩

private def guessesA3444 (seen : Fin 4 × Fin 4) : Finset (Fin 3) :=
  ![![{0, 1}, {0, 2}, {1, 2}, {0, 2}],
    ![{0, 1}, {0, 2}, {1, 2}, {0, 2}],
    ![{0, 1}, {1, 2}, {1, 2}, {1, 2}],
    ![{0, 1}, {0, 1}, {0, 1}, {0, 1}]] seen.1 seen.2

private def guessB3444 (seen : Fin 3 × Fin 4) : Fin 4 :=
  ![![2, 2, 2, 1], ![1, 1, 0, 0], ![0, 3, 3, 3]] seen.1 seen.2

private def guessZ3444 (seen : Fin 4 × Fin 4) : Fin 4 :=
  ![![2, 1, 2, 0], ![2, 2, 2, 3], ![2, 3, 1, 3], ![1, 0, 0, 0]] seen.1 seen.2

private def guessO3444 (seen : Fin 4 × Fin 3) : Fin 4 :=
  ![![2, 1, 0], ![2, 3, 0], ![3, 3, 1], ![2, 1, 0]] seen.1 seen.2

private def strategy3444 : Strategy ![3, 4, 4, 4] ![2, 1, 1, 1] :=
  ⟨fun seen => ⟨guessesA3444 seen,
      (by decide : ∀ x, (guessesA3444 x).card = 2) seen⟩,
    fun seen => ⟨{guessB3444 seen}, Finset.card_singleton _⟩,
    fun seen => ⟨{guessZ3444 seen}, Finset.card_singleton _⟩,
    fun seen => ⟨{guessO3444 seen}, Finset.card_singleton _⟩⟩

#count_heartbeats in
private theorem strategy3444_wins_coordinates :
    ∀ (a : Fin 3) (b : Fin 4) (z : Fin 4) (o : Fin 4),
      ∃ v : Fin 4,
        correctAtBool ![3, 4, 4, 4] ![2, 1, 1, 1] strategy3444 ⟨a, b, z, o⟩ v = true := by
  decide

private theorem strategy3444_wins : Wins ![3, 4, 4, 4] ![2, 1, 1, 1] strategy3444 := by
  intro coloring
  obtain ⟨v, correct⟩ := strategy3444_wins_coordinates
    coloring.1 coloring.2.1 coloring.2.2.1 coloring.2.2.2
  exact ⟨v, (correctAtBool_eq_true_iff _ _ strategy3444 coloring v).mp correct⟩

/-- Two heterogeneous C4 games are winnable, with A making two guesses.
The explicit local plans are checked over all 144 and 192 colourings. -/
theorem c4_three_four_winnable :
    Winnable ![3, 4, 4, 3] ![2, 1, 1, 1] ∧
      Winnable ![3, 4, 4, 4] ![2, 1, 1, 1] := by
  exact ⟨⟨strategy3443, strategy3443_wins⟩, ⟨strategy3444, strategy3444_wins⟩⟩

#print axioms c4_three_four_winnable

end D5.S0.Certificates.HeterogeneousC4HatGame
