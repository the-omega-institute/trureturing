/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.exactChunk
   digest: Exact finite support checks bound request and collision counts for exceptional gaps. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeShiftCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary

def positions6 : List Nat := [0, 6, 8, 9, 11, 12]
def positions7a : List Nat := [0, 3, 6, 8, 9, 11, 12]
def positions7b : List Nat := [0, 6, 8, 9, 10, 11, 12]
def positions8 : List Nat := [0, 3, 6, 8, 9, 10, 11, 12]
def positions7r : List Nat := [0, 3, 5, 6, 8, 9, 11]
def positions8r : List Nat := [0, 3, 5, 6, 7, 8, 9, 11]

def labelDigit (code j : Nat) : Nat := code / 3 ^ j % 3

def labelledSupport (positions : List Nat) (code : Nat) :
    Finset (Bool × Fin 14) :=
  Finset.univ.filter fun v =>
    (List.range positions.length).any fun j =>
      decide (v.2.val = positions[j]!) &&
        if v.1 then decide (labelDigit code j ≠ 0)
        else decide (labelDigit code j ≠ 1)

/-- Direct source and destination scans for occupied requests and empty collisions. -/
def directScore (X : Finset (Bool × Fin 14)) : Nat :=
  (X.filter fun v => (positiveShift 14 v).2 ∈ columns X).card +
  (X.filter fun v => (negativeShift 14 v).2 ∈ columns X).card +
  (Finset.univ.filter fun v : Bool × Fin 14 =>
    v.2 ∉ columns X ∧ negativeShift 14 v ∈ X ∧ positiveShift 14 v ∈ X).card

def exactRow (positions : List Nat) (code : Nat) : Bool :=
  let X := labelledSupport positions code
  decide (X.card ≠ 10 ∨ directScore X ≤ 2 * positions.length + 2)

def exactChunk (positions : List Nat) (start count : Nat) : Bool :=
  (List.range count).all fun j => exactRow positions (start + j)

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact
