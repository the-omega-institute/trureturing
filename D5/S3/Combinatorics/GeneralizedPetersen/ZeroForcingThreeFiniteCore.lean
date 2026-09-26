/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore
   mirror-E: none(waiver:finite-certificate-support-for-an-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.fortOK
   digest: Numeric masks and chunk predicates used by the finite fort certificate. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Sort
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite

abbrev V13 := Bool × Fin 13

def rotate13 (r : Fin 13) (v : V13) : V13 := (v.1, v.2 - r)

/-- The natural-number bit position used by the finite certificates. -/
def code13 (v : V13) : Nat := if v.1 then 13 + v.2.val else v.2.val

/-- Decode the low 26 bits of a natural number as vertices of `P(13,3)`. -/
def maskSet13 (m : Nat) : Finset V13 :=
  Finset.univ.filter fun v => m.testBit (code13 v)

/-- The three neighbours of a vertex of `P(13,3)`. -/
def neighbors13 (v : V13) : Finset V13 :=
  if v.1 then
    {(false, v.2), (true, v.2 + 3), (true, v.2 - 3)}
  else
    {(true, v.2), (false, v.2 + 1), (false, v.2 - 1)}


/-- Numeric neighbour positions for the low-26-bit representation of `P(13,3)`. -/
def neighborCodes13 (i : Nat) : List Nat :=
  if i < 13 then [(i + 12) % 13, (i + 1) % 13, 13 + i]
  else
    let j := i - 13
    [j, 13 + (j + 10) % 13, 13 + (j + 3) % 13]

/-- Direct finite fort checker for the low 26 bits. -/
def fortOK (m : Nat) : Bool :=
  decide (0 < m ∧ m < 2 ^ 26) &&
    (List.range 26).all fun i =>
      m.testBit i || decide ((neighborCodes13 i).countP m.testBit ≠ 1)

/-- Direct finite disjointness checker for two low-26-bit vertex masks. -/
def disjointOK (s f : Nat) : Bool :=
  decide (s < 2 ^ 26 ∧ f < 2 ^ 26 ∧ s &&& f = 0)

/-- A checked candidate/fort row. -/
def rowOK (row : Nat × Nat) : Bool := fortOK row.2 && disjointOK row.1 row.2

/-- Number of set bits among the 26 vertex positions. -/
def bitCount26 (m : Nat) : Nat :=
  (List.range 26).countP fun i => m.testBit i


/-- Six oriented initial-force configurations, using rotation but no reflection quotient. -/
inductive Anchor13 where
  | outerSpoke | outerNext | outerPrev | innerSpoke | innerNext | innerPrev
  deriving DecidableEq

instance : Fintype Anchor13 where
  elems := {.outerSpoke, .outerNext, .outerPrev, .innerSpoke, .innerNext, .innerPrev}
  complete a := by cases a <;> simp

def anchors13 : List Anchor13 :=
  [.outerSpoke, .outerNext, .outerPrev, .innerSpoke, .innerNext, .innerPrev]

/-- The source together with its two initially black neighbours. -/
def anchorRequired : Anchor13 → Finset V13
  | .outerSpoke => {(false, 12), (false, 0), (false, 1)}
  | .outerNext => {(false, 12), (false, 0), (true, 0)}
  | .outerPrev => {(false, 1), (false, 0), (true, 0)}
  | .innerSpoke => {(true, 10), (true, 0), (true, 3)}
  | .innerNext => {(true, 10), (true, 0), (false, 0)}
  | .innerPrev => {(true, 3), (true, 0), (false, 0)}

/-- The white target of the corresponding oriented initial force. -/
def anchorTarget : Anchor13 → V13
  | .outerSpoke => (true, 0)
  | .outerNext => (false, 1)
  | .outerPrev => (false, 12)
  | .innerSpoke => (false, 0)
  | .innerNext => (true, 3)
  | .innerPrev => (true, 10)


/-- A mask has exactly the shape of a seven-set extending the stated anchor. -/
def candidateShapeOK (a : Anchor13) (m : Nat) : Bool :=
  decide (m < 2 ^ 26 ∧ bitCount26 m = 7 ∧
    (∀ v ∈ anchorRequired a, m.testBit (code13 v)) ∧
    ¬m.testBit (code13 (anchorTarget a)))

/-- Adjacent keys are strictly increasing. -/
def StrictKeys (rows : List (Nat × Nat)) : Bool :=
  decide (rows.IsChain fun x y => x.1 < y.1)

/-- Structural checks used to prove that a family exhausts one anchor. -/
private def familyStructureOK (a : Anchor13) (rows : List (Nat × Nat)) : Bool :=
  decide (rows.length = 7315) && StrictKeys rows &&
    rows.all fun row => candidateShapeOK a row.1

/-- Size and distinct increasing order of one complete anchor family. -/
def familyOrderOK (rows : List (Nat × Nat)) : Bool :=
  decide (rows.length = 7315) && StrictKeys rows

/-- Check a consecutive block of certificate chunks for shape, fort validity, and disjointness. -/
def chunkBlockOK (a : Anchor13) (chunks : List (List (Nat × Nat)))
    (start len : Nat) : Bool :=
  (List.range len).all fun j =>
    (chunks.getD (start + j) []).all fun row => candidateShapeOK a row.1 && rowOK row

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
