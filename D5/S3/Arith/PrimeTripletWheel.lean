/- GID: D5/S3/Arith/PrimeTripletWheel
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeTripletWheel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite wheel certificates separate pairwise projection from ordered triplet escape. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PrimeTripletWheel

/-- The two diameter-six prime-triplet templates. -/
def tripletPlus : Finset ℕ := {0, 2, 6}

/-- The reflected diameter-six prime-triplet template. -/
def tripletMinus : Finset ℕ := {0, 4, 6}

/-- Signed ordered-gap chirality, with the common factor two retained. -/
def chirality (a b c : ℕ) : ℤ :=
  ((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)

/-- The unordered pair-distance multiset represented as a finite set. -/
def pairDistances (a b c : ℕ) : Finset ℕ :=
  {b - a, c - b, c - a}

/-- A finite wheel residue survives a template when every shifted value is
coprime to the wheel modulus. This is a candidate predicate, not a primality
predicate. -/
def wheelAdmissible (W : ℕ) (H : Finset ℕ) (r : ℕ) : Prop :=
  ∀ h ∈ H, Nat.Coprime (r + h) W

/-- All surviving residue representatives in the canonical range. -/
def wheelResidues (W : ℕ) (H : Finset ℕ) : Finset ℕ :=
  (Finset.range W).filter (wheelAdmissible W H)

/-- The fixed-origin prefix readout. -/
def wheelPrefixCount (W b : ℕ) (H : Finset ℕ) : ℕ :=
  ((Finset.Icc 1 b).filter (wheelAdmissible W H)).card

/-- Translation-invariant two-point candidate correlation. -/
def wheelPairCount (W s : ℕ) (H : Finset ℕ) : ℕ :=
  ((Finset.range W).filter fun r =>
    wheelAdmissible W H r ∧
      wheelAdmissible W H ((r + s) % W)).card

/-- Ordered three-point candidate correlation. -/
def wheelTripleCount (W s t : ℕ) (H : Finset ℕ) : ℕ :=
  ((Finset.range W).filter fun r =>
    wheelAdmissible W H r ∧
      wheelAdmissible W H ((r + s) % W) ∧
      wheelAdmissible W H ((r + t) % W)).card

theorem plus_chirality : chirality 0 2 6 = 2 := by
  norm_num [chirality]

theorem minus_chirality : chirality 0 4 6 = -2 := by
  norm_num [chirality]

theorem plus_minus_pair_distances :
    pairDistances 0 2 6 = pairDistances 0 4 6 := by
  norm_num [pairDistances]

/-- At modulus thirty the two templates have the same candidate density,
but distinct fixed-origin residue representatives. -/
theorem residues_30_plus :
    wheelResidues 30 tripletPlus = {11, 17} := by
  native_decide

theorem residues_30_minus :
    wheelResidues 30 tripletMinus = {7, 13} := by
  native_decide

/-- The origin-sensitive prefix readout already separates the templates at W = 30. -/
theorem prefix_30_separation :
    wheelPrefixCount 30 10 tripletPlus = 0 ∧
      wheelPrefixCount 30 10 tripletMinus = 1 := by
  native_decide

/-- The first translation-invariant three-point witness in the prescribed
positive-span window occurs at W = 210 and span pair (6,30). -/
theorem triple_210_separation :
    wheelTripleCount 210 6 30 tripletPlus = 1 ∧
      wheelTripleCount 210 6 30 tripletMinus = 0 := by
  native_decide

/-- The two-point candidate count cannot see the fixed-span three-point split. -/
theorem pair_210_same_at_6 :
    wheelPairCount 210 6 tripletPlus =
      wheelPairCount 210 6 tripletMinus := by
  native_decide

end D5.S3.Arith.PrimeTripletWheel
