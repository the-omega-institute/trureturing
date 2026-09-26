/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: A bit-mask recurrence computes upper scores for partial cyclic gap words. -/
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

def choices (m : Nat) (p : List Nat) (j : Nat) : List Nat :=
  if hj : j < p.length then [p[j]] else (List.range m).map (· + 1)

def forward (c i j : Nat) : Nat := (i + j) % c
def backward (c i j : Nat) : Nat := (i + c - (j + 1)) % c

def phiUpper (m : Nat) (p : List Nat) (j : Nat) : Nat :=
  if 1 ∈ choices m p j then 2 else if 2 ∈ choices m p j then 1 else 0

def outer (c m : Nat) (p : List Nat) (i : Nat) : Nat :=
  phiUpper m p (backward c i 0) + phiUpper m p i

def priceBound (scores : List Nat) (price : Nat) : Nat :=
  10 * price + (scores.map fun s => s - price).sum

def exceptionalRoots : List (List Nat) :=
  [[6, 2, 1, 2, 1, 2],
   [3, 2, 1, 2, 1, 2, 3], [3, 3, 2, 1, 2, 1, 2],
   [6, 2, 1, 1, 1, 1, 2],
   [3, 2, 1, 1, 1, 1, 2, 3], [3, 3, 2, 1, 1, 1, 1, 2]]

/-- A bit at position s represents a reachable prefix sum s ≤ 6. -/
def reachMask (c m : Nat) (p : List Nat) (i : Nat) (reverse : Bool) :
    Nat → Nat
  | 0 => 1
  | k + 1 =>
      let old := reachMask c m p i reverse k
      let j := if reverse then backward c i k else forward c i k
      ((choices m p j).foldl (fun mask x => mask ||| (old <<< x)) 0) % 128

def maskHit (c m : Nat) (p : List Nat) (i : Nat) (reverse : Bool) (d : Nat) : Bool :=
  (List.range c).any fun j => (reachMask c m p i reverse (j + 1)).testBit d

def maskDirection (c m : Nat) (p : List Nat) (i : Nat) (reverse : Bool) : Nat :=
  if maskHit c m p i reverse 3 then 2 else if maskHit c m p i reverse 6 then 1 else 0

def maskInner (c m : Nat) (p : List Nat) (i : Nat) : Nat :=
  maskDirection c m p i false + maskDirection c m p i true

def maskSlots (c m : Nat) (p : List Nat) : List Nat :=
  (List.ofFn fun i : Fin c => [outer c m p i.val, maskInner c m p i.val]).flatten

def maskUpper (c m : Nat) (p : List Nat) : Nat :=
  let scores := maskSlots c m p
  min (priceBound scores 0) <|
  min (priceBound scores 1) <|
  min (priceBound scores 2) <|
  min (priceBound scores 3) (priceBound scores 4)

def maskCheck (c : Nat) : Nat → Nat → List Nat → Bool
  | fuel, m, p =>
      if maskUpper c m p ≤ 4 * c + 5 then true
      else match fuel with
        | 0 => decide (p.sum < 14 ∨ p ∈ exceptionalRoots)
        | k + 1 => (List.range m).all fun j => maskCheck c k m (p ++ [j + 1])

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
