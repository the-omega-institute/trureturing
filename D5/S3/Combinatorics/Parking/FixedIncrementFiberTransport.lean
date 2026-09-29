/- GID: D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Parking/FixedIncrementFiberTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-increment encoding and vacancy-normalized fiber transport. -/

import D5.S3.Combinatorics.Parking.OperationalDynamics

/-!
# Fixed-increment fiber transport

This module encodes every literal ordered pair by its anchor and positive
clockwise increment. Vacancy-normalized rotations give explicit forward and
inverse maps between a fixed-increment actual fiber and a one-choice fiber.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularTwoChoiceParkingBijection

/-- Recover the clockwise increment from an actual ordered pair. -/
def actualIncrement {n : Nat} (q : ActualChoice n) : Increment n :=
  ⟨(q.second - q.anchor).val, by
    constructor
    · by_contra h
      have hz : (q.second - q.anchor).val = 0 := by omega
      have heq : q.second - q.anchor = 0 :=
        ZMod.val_injective (n + 1) (by simpa using hz)
      exact q.distinct (sub_eq_zero.mp heq)
    · have := ZMod.val_lt (q.second - q.anchor)
      omega⟩

/-- Reconstruct an actual ordered pair from its anchor and positive increment. -/
def choiceOfAnchorIncrement {n : Nat} (anchor : Spot n) (k : Increment n) : ActualChoice n where
  anchor := anchor
  second := anchor + (k.1 : Spot n)
  distinct := by
    intro h
    have hklt : k.1 < n + 1 := (Nat.lt_succ_iff).2 k.property.2
    have hz : ((k.1 : Nat) : Spot n) = 0 := by
      apply_fun fun x => x - anchor at h
      simpa [add_sub_cancel_left] using h
    have hv := congrArg ZMod.val hz
    have hkzero : k.1 = 0 := by
      simpa [ZMod.val_natCast_of_lt hklt] using hv
    have hkpos := k.property.1
    omega

/-- The increment readout of all actual choices. -/
def actualIncrements {n : Nat} (choices : ActualPreferences n) : IncrementMatrix n :=
  fun i => actualIncrement (choices i)

private def anchorsOf {n : Nat} (choices : ActualPreferences n) : Anchors n :=
  fun i => (choices i).anchor

private def choicesOf {n : Nat} (anchors : Anchors n) (increments : IncrementMatrix n) :
    ActualPreferences n :=
  fun i => choiceOfAnchorIncrement (anchors i) (increments i)

private def fixedActualEmpty {n : Nat} (increments : IncrementMatrix n)
    (anchors : Anchors n) : Spot n :=
  actualEmpty n (choicesOf anchors increments)

private def normalizeAnchors {n : Nat} (empty : Anchors n -> Spot n)
    (j : Spot n) (anchors : Anchors n) : Anchors n :=
  rotateAnchors (j - empty anchors) anchors

/-- Actual fixed-increment inputs whose unique vacancy is the observed spot. -/
def FixedActualFiber (n : Nat) (increments : IncrementMatrix n) (j : Spot n) :=
  {choices : ActualPreferences n //
    actualIncrements choices = increments /\ actualEmpty n choices = j}

/-- One-choice circular inputs whose unique vacancy is the observed spot. -/
def OneChoiceFiber (n : Nat) (j : Spot n) :=
  {anchors : Anchors n // oneEmpty n anchors = j}

/-- Orbit normalization transports a fixed-increment actual fiber to the
one-choice fiber with the same observed vacancy. -/
def fixedFiberToOneChoice {n : Nat} (increments : IncrementMatrix n) (j : Spot n) :
    FixedActualFiber n increments j -> OneChoiceFiber n j := fun choices =>
  let anchors := anchorsOf choices.1
  let normalized := normalizeAnchors (oneEmpty n) j anchors
  ⟨normalized, by
    dsimp [normalized, normalizeAnchors]
    rw [oneEmpty_rotate]
    abel⟩

/-- The inverse orbit normalization reconstructs both ordered choices. -/
def oneChoiceToFixedFiber {n : Nat} (increments : IncrementMatrix n) (j : Spot n) :
    OneChoiceFiber n j -> FixedActualFiber n increments j := fun anchors =>
  let normalized := normalizeAnchors (fixedActualEmpty increments) j anchors.1
  ⟨choicesOf normalized increments,
    by
      funext i
      apply Subtype.ext
      simp only [actualIncrements, choicesOf, actualIncrement, choiceOfAnchorIncrement]
      rw [add_sub_cancel_left,
        ZMod.val_natCast_of_lt ((Nat.lt_succ_iff).2 (increments i).property.2)],
    by
      have hchoicesRotate : ∀ (t : Spot n) (a : Anchors n),
          choicesOf (rotateAnchors t a) increments =
            rotateActual t (choicesOf a increments) := by
        intro t a
        funext i
        simp only [choicesOf, rotateAnchors, rotateActual, choiceOfAnchorIncrement,
          rotateChoice]
        congr 1 <;> abel
      dsimp [normalized, normalizeAnchors]
      rw [hchoicesRotate, actualEmpty_rotate]
      change fixedActualEmpty increments anchors.1 +
        (j - fixedActualEmpty increments anchors.1) = j
      abel⟩

/-- The explicit fixed-increment, fixed-vacancy transport and its inverse. -/
def fixedFiberOneChoiceEquiv {n : Nat} (increments : IncrementMatrix n) (j : Spot n) :
    FixedActualFiber n increments j ≃ OneChoiceFiber n j where
  toFun := fixedFiberToOneChoice increments j
  invFun := oneChoiceToFixedFiber increments j
  left_inv choices := by
    apply Subtype.ext
    have hchoice : ∀ q : ActualChoice n,
        choiceOfAnchorIncrement q.anchor (actualIncrement q) = q := by
      intro q
      cases q with
      | mk anchor second distinct =>
          simp only [choiceOfAnchorIncrement, actualIncrement]
          congr
          rw [ZMod.natCast_zmod_val]
          abel
    have hrecover : choicesOf (anchorsOf choices.1) increments = choices.1 := by
      calc
        choicesOf (anchorsOf choices.1) increments =
            choicesOf (anchorsOf choices.1) (actualIncrements choices.1) := by
              rw [choices.2.1]
        _ = choices.1 := by
          funext i
          exact hchoice (choices.1 i)
    have hbase : fixedActualEmpty increments (anchorsOf choices.1) = j := by
      change actualEmpty n (choicesOf (anchorsOf choices.1) increments) = j
      rw [hrecover]
      exact choices.2.2
    have hchoicesRotate : ∀ (t : Spot n) (a : Anchors n),
        choicesOf (rotateAnchors t a) increments =
          rotateActual t (choicesOf a increments) := by
      intro t a
      funext i
      simp only [choicesOf, rotateAnchors, rotateActual, choiceOfAnchorIncrement,
        rotateChoice]
      congr 1 <;> abel
    have hfixedRotate : ∀ (t : Spot n) (a : Anchors n),
        fixedActualEmpty increments (rotateAnchors t a) =
          fixedActualEmpty increments a + t := by
      intro t a
      change actualEmpty n (choicesOf (rotateAnchors t a) increments) =
        actualEmpty n (choicesOf a increments) + t
      rw [hchoicesRotate, actualEmpty_rotate]
    have hcross :
        normalizeAnchors (fixedActualEmpty increments) j
          (normalizeAnchors (oneEmpty n) j (anchorsOf choices.1)) =
            anchorsOf choices.1 := by
      funext i
      simp only [normalizeAnchors, rotateAnchors]
      rw [hfixedRotate, hbase]
      abel
    change choicesOf
      (normalizeAnchors (fixedActualEmpty increments) j
        (normalizeAnchors (oneEmpty n) j (anchorsOf choices.1))) increments = choices.1
    rw [hcross]
    exact hrecover
  right_inv anchors := by
    apply Subtype.ext
    have hcross :
        normalizeAnchors (oneEmpty n) j
          (normalizeAnchors (fixedActualEmpty increments) j anchors.1) = anchors.1 := by
      funext i
      simp only [normalizeAnchors, rotateAnchors]
      rw [oneEmpty_rotate, anchors.2]
      abel
    change normalizeAnchors (oneEmpty n) j
      (anchorsOf (choicesOf
        (normalizeAnchors (fixedActualEmpty increments) j anchors.1) increments)) = anchors.1
    change normalizeAnchors (oneEmpty n) j
      (normalizeAnchors (fixedActualEmpty increments) j anchors.1) = anchors.1
    exact hcross


end D5.S3.Combinatorics.CircularTwoChoiceParkingBijection

