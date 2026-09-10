/- GID: D5/S0/Certificates/Games/VersionBFaithfulClassification
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/VersionBFaithfulClassification
   mirror-E: none(waiver:kernel-checked-finite-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Games/VersionBFaithfulClassification.FaithfulClassification; result=D5/S0/Certificates/Games/VersionBFaithfulClassification.faithful_classification_refuted; claim=D5/S0/Certificates/Games/VersionBFaithfulClassification.FaithfulClassification
   digest: The threshold classification with all three parity cases fails in both directions at twelve piles in normal-play Version B. -/

import D5.S0.Certificates.Games.VersionBTwelvePileRefutation

/-!
# Both directions of the threshold classification fail at twelve piles

We reuse the frozen Version B game and its checked certificate. Positions
represent the closed subgame with pile sizes one through six; pile count is
unbounded. The classification is restricted to this subgame, so its refutation
also obstructs the same classification on unrestricted positive pile sizes.

The claim retains the lower bound of three piles, the strict ceiling threshold,
and the biconditional with three distinct parity cases for general pile count.
The even-count bounds are written without truncated subtraction: n + 2 ≤ k / 2
and n + 1 ≤ k / 2 express the two lower ranges. The upper ranges consist of
odd counts below k, starting at k / 2 + 1 or k / 2 + 2 respectively.

The six-five/six-six witness reuses target_losing. The seven-five/five-six
witness moves simultaneously to seven fours and five fives. Its losing status
is obtained by kernel reduction of the existing certificate bit through
losing_iff_certificate; no new enumeration or game semantics is introduced.
The refutation consumes this second witness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Games.VersionBFaithfulClassification

open VersionBTwelvePileRefutation

/-- Number of piles with odd size. -/
def oddPiles : Position → Nat
  | ⟨a, _, c, _, e, _⟩ => a + c + e

/-- Allowed odd-pile counts for general k: odd k, k divisible by four,
and k congruent to two modulo four. Bounds preserve empty ranges. -/
def allowedOddCount (k n : Nat) : Prop :=
  n ≤ k ∧
    ((k % 2 = 1 ∧ n % 2 = 0) ∨
     (k % 4 = 0 ∧
       ((n % 2 = 0 ∧ n + 2 ≤ k / 2) ∨
        (n % 2 = 1 ∧ k / 2 + 1 ≤ n ∧ n < k))) ∨
     (k % 4 = 2 ∧
       ((n % 2 = 0 ∧ n + 1 ≤ k / 2) ∨
        (n % 2 = 1 ∧ k / 2 + 2 ≤ n ∧ n < k))))

/-- Every present pile strictly exceeds the ceiling of one third of pile count. -/
def EveryPileExceedsThreshold (s : Position) : Prop :=
  let threshold := (pileCount s + 2) / 3
  (s.1 > 0 → 1 > threshold) ∧
  (s.2.1 > 0 → 2 > threshold) ∧
  (s.2.2.1 > 0 → 3 > threshold) ∧
  (s.2.2.2.1 > 0 → 4 > threshold) ∧
  (s.2.2.2.2.1 > 0 → 5 > threshold) ∧
  (s.2.2.2.2.2 > 0 → 6 > threshold)

/-- The full threshold-and-parity biconditional on the imported closed subgame. -/
def FaithfulClassification : Prop :=
  ∀ s : Position, 3 ≤ pileCount s → EveryPileExceedsThreshold s →
    (Losing s ↔ allowedOddCount (pileCount s) (oddPiles s))

/-- At twelve piles the allowed counts are exactly zero, two, four, seven,
nine and eleven. -/
theorem allowedOddCount_twelve_iff (n : Nat) :
    allowedOddCount 12 n ↔ n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 7 ∨ n = 9 ∨ n = 11 := by
  unfold allowedOddCount
  omega

/-- Seven piles of size five and five of size six. -/
def sevenFives_fiveSixes : Position := ⟨0,0,0,0,7,5⟩

/-- Seven piles of size four and five of size five. -/
def sevenFours_fiveFives : Position := ⟨0,0,0,7,5,0⟩

/-- The all-move successor is losing, certified by the frozen bit certificate. -/
theorem sevenFours_fiveFives_losing : Losing sevenFours_fiveFives := by
  apply (losing_iff_certificate sevenFours_fiveFives (by decide)).mpr
  decide +kernel

/-- Removing one token from every pile reaches the certified losing position. -/
theorem sevenFives_fiveSixes_all_move :
    AllMove sevenFives_fiveSixes sevenFours_fiveFives := by
  constructor <;> decide

/-- A losing twelve-pile position satisfying both hypotheses is excluded
by the allowed-count prediction, refuting necessity. -/
theorem sixFives_sixSixes_is_losing_but_predicted_winning :
    pileCount target = 12 ∧ 3 ≤ pileCount target ∧
    EveryPileExceedsThreshold target ∧ oddPiles target = 6 ∧
    Losing target ∧ ¬ allowedOddCount (pileCount target) (oddPiles target) := by
  refine ⟨by decide, by decide, ?_, by decide, target_losing, ?_⟩
  · unfold EveryPileExceedsThreshold
    decide
  · unfold allowedOddCount
    decide

/-- A winning twelve-pile position satisfying both hypotheses is included
by the allowed-count prediction, refuting sufficiency. -/
theorem sevenFives_fiveSixes_is_winning_but_predicted_losing :
    pileCount sevenFives_fiveSixes = 12 ∧ 3 ≤ pileCount sevenFives_fiveSixes ∧
    EveryPileExceedsThreshold sevenFives_fiveSixes ∧ oddPiles sevenFives_fiveSixes = 7 ∧
    ¬ Losing sevenFives_fiveSixes ∧
    allowedOddCount (pileCount sevenFives_fiveSixes) (oddPiles sevenFives_fiveSixes) := by
  refine ⟨by decide, by decide, ?_, by decide, ?_, ?_⟩
  · unfold EveryPileExceedsThreshold
    decide
  · intro h
    exact (losing_iff sevenFives_fiveSixes).mp h sevenFours_fiveFives
      (Or.inr sevenFives_fiveSixes_all_move) sevenFours_fiveFives_losing
  · unfold allowedOddCount
    decide

/-- The biconditional classification is false. -/
theorem faithful_classification_refuted : ¬ FaithfulClassification := by
  intro h
  obtain ⟨_, hk, ht, _, hn, ha⟩ :=
    sevenFives_fiveSixes_is_winning_but_predicted_losing
  exact hn ((h sevenFives_fiveSixes hk ht).mpr ha)

#print axioms oddPiles
#print axioms allowedOddCount
#print axioms EveryPileExceedsThreshold
#print axioms FaithfulClassification
#print axioms allowedOddCount_twelve_iff
#print axioms sevenFives_fiveSixes
#print axioms sevenFours_fiveFives
#print axioms sevenFours_fiveFives_losing
#print axioms sevenFives_fiveSixes_all_move
#print axioms sixFives_sixSixes_is_losing_but_predicted_winning
#print axioms sevenFives_fiveSixes_is_winning_but_predicted_losing
#print axioms faithful_classification_refuted

end D5.S0.Certificates.Games.VersionBFaithfulClassification
