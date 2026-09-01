/- GID: D5/S0/Tower/DBonacci/OrbitAlgebra
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/OrbitAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed d-bonacci gap refinement gives a uniform period-two orbit algebra. -/

import D5.S0.Tower.DBonacci.GapAlphabet
import D5.S0.Tower.DBonacci.ChampionOrbit

namespace D5.S0.Tower.DBonacci.OrbitAlgebra

/- Library-search audit trail (2026-08-17):
   * Repository search found the strict monotonicity of d-bonacci gap lengths,
     the typed gap substitution, and the three frozen order-specific proofs.
   * Pinned mathlib supplies only the elementary order, list, and integer-power
     algebra used here; no external d-bonacci orbit theorem was found. -/

/-- A typed adjacent gap records its letter and both normalized endpoint arms. -/
def IsDBonacciLetterOrbitGap (d Q : Nat) (x : Real)
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d)
    (leftArm rightArm : Real) : Prop :=
  ∃ i : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 2) - 1),
    D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
          (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) -
        D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
          (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
      D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d Q letter ∧
    x - D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
          (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
      leftArm * D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
        (-(Q : Int)) ∧
    D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
          (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) - x =
      rightArm * D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
        (-(Q : Int))

/-- The predecessor of the top letter, available for every order at least two. -/
def topPredecessorGapLetter (d : Nat) (hd : 2 ≤ d) :
    D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d :=
  ⟨d - 2, by omega⟩

/-- Typed gap lengths determine their letters uniquely. -/
theorem gap_letter_length_injective (d Q : Nat) (hd : 2 ≤ d) :
    Function.Injective
      (D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d Q) := by
  intro left right hlength
  apply Fin.ext
  apply (D5.S0.Tower.DBonacci.Gaps.dbonacciGapLength_strictMono d Q hd).injective
  exact hlength

/-- A typed orbit-gap witness carries the substitution of that same letter. -/
theorem letter_orbit_gap_refinement (d Q : Nat) (hd : 2 ≤ d)
    (x : Real)
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d)
    (leftArm rightArm : Real)
    (hgap : IsDBonacciLetterOrbitGap d Q x letter leftArm rightArm) :
    ∃ i : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 2) - 1),
      D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) -
          D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
        D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d Q letter ∧
      x - D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
        leftArm * D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
          (-(Q : Int)) ∧
      D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) - x =
        rightArm * D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
          (-(Q : Int)) ∧
      D5.S0.Tower.DBonacci.GapAlphabet.RealizesGapRefinement d Q i
        (D5.S0.Tower.DBonacci.GapAlphabet.gapLetterSubstitution d
          (by omega) letter) := by
  rcases hgap with ⟨i, hlength, hleft, hright⟩
  obtain ⟨actual, _, hactual, hrefinement⟩ :=
    D5.S0.Tower.DBonacci.GapAlphabet.dbonacci_gap_letter_substitution d Q hd i
  have hsame : actual = letter :=
    gap_letter_length_injective d Q hd (hactual.symm.trans hlength)
  subst actual
  exact ⟨i, hlength, hleft, hright, hrefinement⟩

/-- The unique inserted point is adjacent to both embedded coarse endpoints. -/
theorem inserted_singleton_positions (d Q : Nat)
    (i : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 2) - 1))
    (j : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 3)))
    (hset : D5.S0.Tower.DBonacci.Substitution.insertedNameIndices d Q i = {j}) :
    (D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
        (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)).1 + 1 = j.1 ∧
      j.1 + 1 =
        (D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
          (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i)).1 := by
  have hj : j ∈ D5.S0.Tower.DBonacci.Substitution.insertedNameIndices d Q i := by
    rw [hset]
    simp
  have hjbounds := hj
  simp only [D5.S0.Tower.DBonacci.Substitution.insertedNameIndices,
    Finset.mem_Ioo] at hjbounds
  have hcard :
      (D5.S0.Tower.DBonacci.Substitution.insertedNameIndices d Q i).card = 1 := by
    rw [hset]
    simp
  rw [D5.S0.Tower.DBonacci.Substitution.insertedNameIndices, Fin.card_Ioo] at hcard
  constructor <;> omega

/-- The top letter has normalized length one at every level. -/
theorem top_gap_letter_length (d Q : Nat) (hd : 2 ≤ d) :
    D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d Q
        (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega)) =
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(Q : Int)) := by
  unfold D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength
  simp only [D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter]
  unfold D5.S0.Tower.DBonacci.Gaps.dbonacciGapLength
  rw [D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound_full d hd, mul_one,
    zpow_neg, zpow_natCast, inv_pow]

/-- Passing from level Q to Q+1 multiplies normalized arms by the Perron root. -/
theorem dbonacci_scale_succ (d Q : Nat) (hd : 2 ≤ d) :
    D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(Q : Int)) =
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d *
        D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
          (-((Q + 1 : Nat) : Int)) := by
  calc
    D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(Q : Int)) =
        D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
          ((1 : Int) + -((Q + 1 : Nat) : Int)) := by
      congr 1
      push_cast
      omega
    _ = D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (1 : Int) *
        D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
          (-((Q + 1 : Nat) : Int)) := by
      rw [zpow_add₀ (ne_of_gt (zero_lt_one.trans
        (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d hd)))]
    _ = D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d *
        D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
          (-((Q + 1 : Nat) : Int)) := by
      rw [zpow_one]

/-- The right child of a nonzero letter has predecessor letter and affine arms. -/
theorem letter_orbit_gap_right_child (d Q : Nat) (hd : 2 ≤ d)
    (x : Real)
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d)
    (leftArm rightArm : Real) (hletter : letter.1 ≠ 0)
    (hgap : IsDBonacciLetterOrbitGap d Q x letter leftArm rightArm) :
    IsDBonacciLetterOrbitGap d (Q + 1) x
      ⟨letter.1 - 1, by omega⟩
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * leftArm - 1)
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * rightArm) := by
  obtain ⟨i, _, hleft, hright, hrefinement⟩ :=
    letter_orbit_gap_refinement d Q hd x letter leftArm rightArm hgap
  have hrefinement' :
      D5.S0.Tower.DBonacci.GapAlphabet.RealizesGapRefinement d Q i
        [D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega),
          (⟨letter.1 - 1, by omega⟩ :
            D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d)] := by
    simpa [D5.S0.Tower.DBonacci.GapAlphabet.gapLetterSubstitution, hletter]
      using hrefinement
  change ∃ j : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 3)),
      D5.S0.Tower.DBonacci.Substitution.insertedNameIndices d Q i = {j} ∧
        D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
          D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d (Q + 1)
            (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega)) ∧
        D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j =
          D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d (Q + 1)
            ⟨letter.1 - 1, by omega⟩ at hrefinement'
  rcases hrefinement' with ⟨j, hset, hjleft, hjright⟩
  have hpositions := inserted_singleton_positions d Q i j hset
  let next : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d ((Q + 1) + 2) - 1) :=
    ⟨j.1, by
      change j.1 < D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 3) - 1
      have hrightbound :=
        (D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
          (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i)).2
      omega⟩
  have hnextLeft :
      D5.S0.Tower.DBonacci.Substitution.gapLeft d (Q + 1) next = j := by
    apply Fin.ext
    simp [next, D5.S0.Tower.DBonacci.Substitution.gapLeft]
  have hnextRight :
      D5.S0.Tower.DBonacci.Substitution.gapRight d (Q + 1) next =
        D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
          (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) := by
    apply Fin.ext
    exact hpositions.2
  refine ⟨next, ?_, ?_, ?_⟩
  · rw [hnextLeft, hnextRight,
      D5.S0.Tower.DBonacci.Substitution.levelEmbedding_value]
    exact hjright
  · rw [hnextLeft]
    calc
      x - D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j =
          (x - D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)) -
          (D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)) := by ring
      _ = leftArm *
            D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(Q : Int)) -
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-((Q + 1 : Nat) : Int)) := by
        rw [hleft, hjleft, top_gap_letter_length d (Q + 1) hd]
      _ = (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * leftArm - 1) *
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-((Q + 1 : Nat) : Int)) := by
        rw [dbonacci_scale_succ d Q hd]
        ring
  · rw [hnextRight, D5.S0.Tower.DBonacci.Substitution.levelEmbedding_value]
    calc
      D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) - x =
          rightArm * D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-(Q : Int)) := hright
      _ = (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * rightArm) *
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-((Q + 1 : Nat) : Int)) := by
        rw [dbonacci_scale_succ d Q hd]
        ring

/-- The left child of a nonzero letter is top and has the complementary affine arms. -/
theorem letter_orbit_gap_left_child (d Q : Nat) (hd : 2 ≤ d)
    (x : Real)
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d)
    (leftArm rightArm : Real) (hletter : letter.1 ≠ 0)
    (hgap : IsDBonacciLetterOrbitGap d Q x letter leftArm rightArm) :
    IsDBonacciLetterOrbitGap d (Q + 1) x
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega))
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * leftArm)
      (1 - D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * leftArm) := by
  obtain ⟨i, _, hleft, _, hrefinement⟩ :=
    letter_orbit_gap_refinement d Q hd x letter leftArm rightArm hgap
  have hrefinement' :
      D5.S0.Tower.DBonacci.GapAlphabet.RealizesGapRefinement d Q i
        [D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega),
          (⟨letter.1 - 1, by omega⟩ :
            D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d)] := by
    simpa [D5.S0.Tower.DBonacci.GapAlphabet.gapLetterSubstitution, hletter]
      using hrefinement
  change ∃ j : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 3)),
      D5.S0.Tower.DBonacci.Substitution.insertedNameIndices d Q i = {j} ∧
        D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
          D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d (Q + 1)
            (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega)) ∧
        D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j =
          D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength d (Q + 1)
            ⟨letter.1 - 1, by omega⟩ at hrefinement'
  rcases hrefinement' with ⟨j, hset, hjleft, _⟩
  have hpositions := inserted_singleton_positions d Q i j hset
  let next : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d ((Q + 1) + 2) - 1) :=
    ⟨(D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
        (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)).1, by
      change (D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
        (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)).1 <
          D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 3) - 1
      have hjbound := j.2
      omega⟩
  have hnextLeft :
      D5.S0.Tower.DBonacci.Substitution.gapLeft d (Q + 1) next =
        D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
          (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) := by
    apply Fin.ext
    simp [next, D5.S0.Tower.DBonacci.Substitution.gapLeft]
  have hnextRight :
      D5.S0.Tower.DBonacci.Substitution.gapRight d (Q + 1) next = j := by
    apply Fin.ext
    exact hpositions.1
  refine ⟨next, ?_, ?_, ?_⟩
  · rw [hnextLeft, hnextRight,
      D5.S0.Tower.DBonacci.Substitution.levelEmbedding_value]
    exact hjleft
  · rw [hnextLeft, D5.S0.Tower.DBonacci.Substitution.levelEmbedding_value]
    calc
      x - D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
          leftArm * D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-(Q : Int)) := hleft
      _ = (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * leftArm) *
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-((Q + 1 : Nat) : Int)) := by
        rw [dbonacci_scale_succ d Q hd]
        ring
  · rw [hnextRight]
    calc
      D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j - x =
          (D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)) -
          (x - D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
            (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)) := by ring
      _ = D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-((Q + 1 : Nat) : Int)) -
          leftArm * D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-(Q : Int)) := by
        rw [hjleft, top_gap_letter_length d (Q + 1) hd, hleft]
      _ = (1 - D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * leftArm) *
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-((Q + 1 : Nat) : Int)) := by
        rw [dbonacci_scale_succ d Q hd]
        ring

/-- A top/predecessor base gap and four scalar identities generate the uniform period-two orbit. -/
theorem top_predecessor_period_two_orbit (d Q₀ : Nat) (hd : 3 ≤ d)
    (x largeLeft lowArm middleLeft middleRight : Real)
    (hlargeBranch :
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * largeLeft - 1 =
        middleLeft)
    (hmiddleRight :
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * lowArm = middleRight)
    (hmiddleBranch :
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * middleLeft =
        largeLeft)
    (hmiddleComplement :
      1 - D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d * middleLeft =
        lowArm)
    (hbase : IsDBonacciLetterOrbitGap d Q₀ x
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega))
      largeLeft lowArm) (k : Nat) :
    IsDBonacciLetterOrbitGap d (2 * k + Q₀) x
        (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega))
        largeLeft lowArm ∧
      IsDBonacciLetterOrbitGap d (2 * k + Q₀ + 1) x
        (topPredecessorGapLetter d (by omega)) middleLeft middleRight := by
  have htop_nonzero :
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega)).1 ≠ 0 := by
    simp [D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter]
    omega
  have hpredecessor_nonzero : (topPredecessorGapLetter d (by omega)).1 ≠ 0 := by
    simp [topPredecessorGapLetter]
    omega
  induction k with
  | zero =>
      have hmiddle := letter_orbit_gap_right_child d Q₀ (by omega) x
        (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega))
        largeLeft lowArm htop_nonzero hbase
      constructor
      · simpa using hbase
      · have hindex : 2 * 0 + Q₀ + 1 = Q₀ + 1 := by omega
        have hletter :
            topPredecessorGapLetter d (by omega) =
              ⟨(D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega)).1 - 1,
                by omega⟩ := by
          apply Fin.ext
          simp [D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter,
            topPredecessorGapLetter]
          omega
        rw [hindex, hletter, ← hlargeBranch, ← hmiddleRight]
        exact hmiddle
  | succ k ih =>
      have hlarge := letter_orbit_gap_left_child d (2 * k + Q₀ + 1)
        (by omega) x (topPredecessorGapLetter d (by omega))
        middleLeft middleRight hpredecessor_nonzero ih.2
      have hlarge' : IsDBonacciLetterOrbitGap d (2 * k + Q₀ + 1 + 1) x
          (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega))
          largeLeft lowArm := by
        rw [hmiddleComplement, hmiddleBranch] at hlarge
        exact hlarge
      have hmiddle := letter_orbit_gap_right_child d (2 * k + Q₀ + 1 + 1)
        (by omega) x
        (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega))
        largeLeft lowArm htop_nonzero hlarge'
      constructor
      · convert hlarge' using 1
        omega
      · have hindex : 2 * (k + 1) + Q₀ + 1 = 2 * k + Q₀ + 1 + 1 + 1 := by omega
        have hletter :
            topPredecessorGapLetter d (by omega) =
              ⟨(D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega)).1 - 1,
                by omega⟩ := by
          apply Fin.ext
          simp [D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter,
            topPredecessorGapLetter]
          omega
        rw [hindex, hletter, ← hlargeBranch, ← hmiddleRight]
        exact hmiddle

/-- The order-four orbit is an instance of the uniform typed period-two theorem. -/
theorem four_champion_gap_orbit_reproved (k : Nat) :
    D5.S0.Tower.DBonacci.ChampionOrbit.IsDBonacciOrbitGap 4 (2 * k + 4)
        D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint 3
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 /
          (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1))
        ((D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 -
            D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 - 1) /
          (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1)) ∧
      D5.S0.Tower.DBonacci.ChampionOrbit.IsDBonacciOrbitGap 4 (2 * k + 5)
        D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint 2
        (1 / (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1))
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 *
          ((D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 -
              D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 - 1) /
            (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1))) := by
  let b := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4
  let largeLeft := b / (b ^ 2 - 1)
  let lowArm := (b ^ 2 - b - 1) / (b ^ 2 - 1)
  let middleLeft := 1 / (b ^ 2 - 1)
  let middleRight := b * lowArm
  have hbase : IsDBonacciLetterOrbitGap 4 4
      D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter 4 (by norm_num))
      largeLeft lowArm := by
    rcases D5.S0.Tower.DBonacci.ChampionOrbit.four_champion_base_gap with
      ⟨i, hlength, hleft, hright⟩
    refine ⟨i, ?_, hleft, hright⟩
    simpa [D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength,
      D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter] using hlength
  have horbit := top_predecessor_period_two_orbit 4 4 (by norm_num)
    D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint
    largeLeft lowArm middleLeft middleRight
    D5.S0.Tower.DBonacci.ChampionOrbit.four_large_branch
    (by simp [b, middleRight])
    D5.S0.Tower.DBonacci.ChampionOrbit.four_middle_branch
    D5.S0.Tower.DBonacci.ChampionOrbit.four_middle_complement hbase k
  rcases horbit with ⟨hlarge, hmiddle⟩
  rcases hlarge with ⟨i, hlength, hleft, hright⟩
  rcases hmiddle with ⟨j, hmiddleLength, hmiddleLeft, hmiddleRight⟩
  constructor
  · refine ⟨i, ?_, hleft, hright⟩
    simpa [D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength,
      D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter] using hlength
  · refine ⟨j, ?_, hmiddleLeft, hmiddleRight⟩
    simpa [D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength,
      topPredecessorGapLetter] using hmiddleLength

end D5.S0.Tower.DBonacci.OrbitAlgebra
