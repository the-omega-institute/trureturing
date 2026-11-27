import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover

/-! Kernel replay of the exact low-spectrum cap bisection witness. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Certificate

open _root_.Matrix
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicDirectedOccupationCap (Mat)
open WuCubicLowSpectrumCover (Box CornerWitness InBox Tree)
open WuCubicLowSpectrumRationalCorner (cutBiasRat lowerCoeffRat upperCoeffRat)
open private corner sortedLevels midpoint from
  D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

private abbrev Shares := Fin 4 → ℚ

private def half : Shares := ![1 / 2, 1 / 2, 0, 0]

-- Fractions of the two cross coefficients and the two endpoint biases.
private def choices : List Shares := [half,
  ![1 / 4, 1 / 4, 0, 0], ![1 / 2, 1 / 2, 0, 1 / 64],
  ![1 / 2, 1 / 2, 0, 1 / 32], ![1 / 2, 1 / 2, 0, 1 / 16], ![3 / 4, 1 / 4, 0, 0],
  ![3 / 4, 1 / 4, 0, 1 / 32], ![3 / 4, 1 / 4, 1 / 64, 0], ![3 / 4, 1 / 4, 1 / 32, 0],
  ![3 / 4, 1 / 4, 1 / 16, 0], ![3 / 4, 1 / 4, 1 / 8, 0], ![3 / 4, 1 / 2, 1 / 32, 1 / 32],
  ![1, 1 / 4, 1 / 32, 0]]

private def leafWitness (box : Box) (overrides : List (ℕ × Shares))
    (ε : Fin 4 → Bool) : CornerWitness :=
  let mask := Fin.foldl 4 (fun index axis => 2 * index + (ε axis).toNat) 0
  let shares := ((overrides.find? fun entry => entry.1.testBit mask).map Prod.snd).getD half
  let y := corner box ε
  let z := sortedLevels y
  let B := cutBiasRat (y 0) (z 0) (z 1) (z 2)
  ⟨shares 0 * lowerCoeffRat (y 0) (z 0) (z 1) (z 2),
    shares 1 * upperCoeffRat (y 0) (z 1) (z 2), shares 2 * B 0, shares 3 * B 2⟩

-- Each override is a four-bit choice index followed by the sixteen-bit corner mask.
private def readOverrides : ℕ → ℕ → Option (List (ℕ × Shares) × ℕ)
  | 0, code => some ([], code)
  | count + 1, code => do
      let shares ← choices[code % 16]?
      let (rest, suffix) ← readOverrides count (code / 1048576)
      return ((code / 16 % 65536, shares) :: rest, suffix)

-- Read the preorder tree from the low bits. Tags 0–3 split on that coordinate,
-- tag 4 prunes, and tags 5–7 give leaves with zero, one, or two overrides.
private def readTree : ℕ → Box → ℕ → Option (Tree × ℕ)
  | 0, _, _ => none
  | depth + 1, box, code => do
      let tag := code % 8
      let rest := code / 8
      if tag < 4 then
        let axis := Fin.ofNat 4 tag
        let cut := midpoint box axis
        let (left, rest) ← readTree depth (leftBox box axis cut) rest
        let (right, suffix) ← readTree depth (rightBox box axis cut) rest
        return (.split axis left right, suffix)
      else if tag = 4 then
        return (.prune, rest)
      else
        let (overrides, suffix) ← readOverrides (tag - 5) rest
        return (.leaf (leafWitness box overrides), suffix)

private def decode (depth : ℕ) (box : Box) (code : ℕ) : Option Tree := do
  let (tree, suffix) ← readTree depth box code
  if suffix = 1 then some tree else none

private abbrev Accepted (box : Box) (decoded : Option Tree) : Prop :=
  decoded.map (fun tree => tree.check (1 / 10000) box) = some true

private theorem acceptedSplit {box : Box} (axis : Fin 4) {left right : Option Tree}
    (hl : Accepted (leftBox box axis (midpoint box axis)) left)
    (hr : Accepted (rightBox box axis (midpoint box axis)) right) :
    Accepted box (Tree.split axis <$> left <*> right) := by
  obtain ⟨leftTree, hLeftTree, hLeft⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨rightTree, hRightTree, hRight⟩ := Option.map_eq_some_iff.mp hr
  rw [hLeftTree, hRightTree]
  exact congrArg some (Bool.and_eq_true_iff.mpr ⟨hLeft, hRight⟩)

private theorem acceptedFloor {box : Box} {decoded : Option Tree} (accepted : Accepted box decoded)
    (U : unitary Mat) {x : Fin 4 → ℝ} (hx : InBox box x) (hmn : x 1 ≤ x 2) (hnq : x 2 ≤ x 3) :
    (1 / 10000 : ℝ) ≤ normalizedDeficit (x 0) U (x 1) (x 2) (x 3) := by
  obtain ⟨tree, _, h⟩ := Option.map_eq_some_iff.mp accepted
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using tree.check_sound U h hx hmn hnq

/-- The cap subtree at path `111011100111101000`, with `0` for left and `1` for right. -/
def firstBox : Box := ![(23 / 20, 93 / 80), (189 / 320, 63 / 100),
  (9 / 16, 19 / 32), (13 / 16, 27 / 32)]

private def firstDecoded : Option Tree := decode 2 firstBox 0x30800271

set_option profiler true in
set_option profiler.threshold 10 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
-- The kernel reduces the box endpoints and the sixteen rational corner checks.
private theorem firstAccepted : Accepted firstBox firstDecoded := by
  decide +kernel

/-- The supplied cap certificate gives a uniform deficit floor on this closed subbox. -/
theorem firstSubtree_floor (U : unitary Mat) {x : Fin 4 → ℝ} (hx : InBox firstBox x)
    (hmn : x 1 ≤ x 2) (hnq : x 2 ≤ x 3) :
    (1 / 10000 : ℝ) ≤ normalizedDeficit (x 0) U (x 1) (x 2) (x 3) :=
  acceptedFloor firstAccepted U hx hmn hnq

/-- The cap subtree at path `11101110011110100`. -/
def parentBox : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100),
  (9 / 16, 19 / 32), (13 / 16, 27 / 32)]

private def siblingBox : Box := rightBox parentBox 0 (midpoint parentBox 0)

private def siblingDecoded : Option Tree := decode 2 siblingBox 0x30808271

set_option profiler true in
set_option profiler.threshold 10 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
-- The kernel reduces the box endpoints and the sixteen rational corner checks.
private theorem siblingAccepted : Accepted siblingBox siblingDecoded := by
  decide +kernel

private def parentDecoded : Option Tree := Tree.split 0 <$> firstDecoded <*> siblingDecoded

private theorem parentAccepted : Accepted parentBox parentDecoded := by
  apply acceptedSplit 0 _ siblingAccepted
  have hbox : leftBox parentBox 0 (midpoint parentBox 0) = firstBox := by
    funext i
    fin_cases i <;> decide +kernel
  simpa only [hbox] using firstAccepted

/-- The two checked halves give a uniform deficit floor on their closed parent box. -/
theorem parentSubtree_floor (U : unitary Mat) {x : Fin 4 → ℝ} (hx : InBox parentBox x)
    (hmn : x 1 ≤ x 2) (hnq : x 2 ≤ x 3) :
    (1 / 10000 : ℝ) ≤ normalizedDeficit (x 0) U (x 1) (x 2) (x 3) :=
  acceptedFloor parentAccepted U hx hmn hnq

#print axioms firstAccepted
#print axioms siblingAccepted
#print axioms parentSubtree_floor

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Certificate
