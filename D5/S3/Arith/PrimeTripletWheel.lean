/- GID: D5/S3/Arith/PrimeTripletWheel
   generality: I
   mirror-B: none(waiver:finite-witness-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite wheel witnesses separate the two prime-triplet orientations.

   This proposal deliberately formalizes wheel candidates rather than actual
   prime-triplet counts.  The latter would require an additional arithmetic
   theorem and is outside the finite witness layer.
-/

import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PrimeTripletWheel

/-! ### The two minimal diameter-six templates -/

def tripletPlus : Finset ℕ := {0, 2, 6}

def tripletMinus : Finset ℕ := {0, 4, 6}

/-- Signed difference of the two consecutive gaps. -/
def chirality (a b c : ℕ) : ℤ :=
  ((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)

/-- The unordered pair-distance support of an ordered three-point template. -/
def pairDistances (a b c : ℕ) : Finset ℕ := {b - a, c - b, c - a}

theorem tripletPlus_chirality : chirality 0 2 6 = 2 := by
  norm_num [chirality]

theorem tripletMinus_chirality : chirality 0 4 6 = -2 := by
  norm_num [chirality]

theorem triplet_pairDistances_equal :
    pairDistances 0 2 6 = pairDistances 0 4 6 := by
  native_decide

/-- Reflect an offset set about the midpoint 3. -/
def reflectedOffsets (H : Finset ℕ) : Finset ℕ :=
  H.image (fun h => 6 - h)

theorem reflected_tripletPlus :
    reflectedOffsets tripletPlus = tripletMinus := by
  native_decide

/-! ### Finite wheel candidates -/

/-- A residue is a wheel candidate for every offset in `H`. -/
def wheelAdmissible (W : ℕ) (H : Finset ℕ) (r : ℕ) : Prop :=
  ∀ h ∈ H, Nat.Coprime (r + h) W

/-- Candidate residues in the canonical range `0, ..., W - 1`. -/
def wheelResidues (W : ℕ) (H : Finset ℕ) : Finset ℕ :=
  (Finset.range W).filter (wheelAdmissible W H)

/-- Prefix count with the fixed origin convention used by the foundational theory. -/
def wheelPrefixCount (W b : ℕ) (H : Finset ℕ) : ℕ :=
  ((Finset.Icc 1 b).filter (wheelAdmissible W H)).card

/-- Two-point wheel correlation at a labelled positive shift. -/
def wheelPairCount (W s : ℕ) (H : Finset ℕ) : ℕ :=
  ((Finset.range W).filter fun r =>
    wheelAdmissible W H r ∧
      wheelAdmissible W H ((r + s) % W)).card

/-- Three-point wheel correlation at labelled shifts `s,t`. -/
def wheelTripleCount (W s t : ℕ) (H : Finset ℕ) : ℕ :=
  ((Finset.range W).filter fun r =>
    wheelAdmissible W H r ∧
      wheelAdmissible W H ((r + s) % W) ∧
      wheelAdmissible W H ((r + t) % W)).card

/-! ### Machine-checked finite escape witnesses -/

theorem wheelResidues_30_plus :
    wheelResidues 30 tripletPlus = {11, 17} := by
  native_decide

theorem wheelResidues_30_minus :
    wheelResidues 30 tripletMinus = {7, 13} := by
  native_decide

/-- The first positive labelled prefix separates the two orientations. -/
theorem wheelPrefix_30_separates :
    wheelPrefixCount 30 10 tripletPlus = 0 ∧
      wheelPrefixCount 30 10 tripletMinus = 1 := by
  native_decide

/-- At modulus 210, the labelled three-point correlation `(6,30)` separates. -/
theorem wheelTriple_210_separates :
    wheelTripleCount 210 6 30 tripletPlus = 1 ∧
      wheelTripleCount 210 6 30 tripletMinus = 0 := by
  native_decide

/-- No positive pair of labelled spans below 30 has a nonzero three-point
correlation for either orientation. -/
theorem wheelTriple_no_smaller_positive_span :
    ∀ s t : Fin 30,
      0 < s.val → s.val < t.val →
        wheelTripleCount 210 s.val t.val tripletPlus = 0 ∧
          wheelTripleCount 210 s.val t.val tripletMinus = 0 := by
  native_decide

end D5.S3.Arith.PrimeTripletWheel
