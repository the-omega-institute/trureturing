/- GID: D5/S1/Digit/Infinite/WindowCylinderPartition
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/WindowCylinderPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite legal digit cylinders form affine intervals with exact golden circle cuts and oriented endpoint streams. -/

import D5.S1.Digit.Infinite.WindowSuccessorGraph
import D5.S1.Digit.Infinite.SignedSeriesFibres
import Mathlib.Algebra.Order.Group.Pointwise.Interval

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.WindowCylinderPartition

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.WindowSuccessorGraph

/-- The real circle with circumference one. -/
abbrev Circle := AddCircle (1 : ℝ)
/-- The negative golden phase indexed by a natural number. -/
noncomputable def E (m : ℕ) : Circle := ((-(m : ℝ) * Real.goldenRatio : ℝ) : Circle)
/-- The Fibonacci value of the digits of a finite return-block word. -/
def wordValue (w : List Block) : ℕ := ∑ j ∈ Finset.range (len w),
  if (digitsOf w)[j]?.getD false then Nat.fib (j + 2) else 0
/-- The natural index of a finite return-block seam. -/
def seamIndex (w : List Block) : ℕ := G (len w + 1) - wordValue w
/-- A return-block word with the specified seam index, or the empty word if none exists. -/
noncomputable def seamWord (m : ℕ) : List Block := by
  classical
  exact if h : ∃ w, seamIndex w = m then Classical.choose h else []
/-- The endpoint stream on the negative side of the indexed circle cut. -/
noncomputable def eMinus (m : ℕ) : LegalDigits :=
  if m ≤ 1 then v else
    if len (seamWord m) % 2 = 0 then rightStream (seamWord m) else leftStream (seamWord m)
/-- The endpoint stream on the positive side of the indexed circle cut. -/
noncomputable def ePlus (m : ℕ) : LegalDigits :=
  if m ≤ 1 then u else
    if len (seamWord m) % 2 = 0 then leftStream (seamWord m) else rightStream (seamWord m)

/-- The window digits completed by a zero exactly when the last digit is one. -/
def completedDigits {L : ℕ} (p : X L) : List (Fin 2) :=
  List.ofFn (fun i => if p.val i then 1 else 0) ++
    if (List.ofFn p.val).getLast?.getD false then [0] else []
/-- The return-block word obtained by decoding the completed window. -/
def c {L : ℕ} (p : X L) : List Block :=
  ((D5.S0.Automata.BinaryZeckendorfBlockSkeleton.decode (completedDigits p)).getD
    ⟨[], .recurrent⟩).blocks
/-- The digit length of the completed window. -/
def d {L : ℕ} (p : X L) : ℕ := L + if (List.ofFn p.val).getLast?.getD false then 1 else 0
/-- The signed golden sum of the window digits. -/
noncomputable def Sp {L : ℕ} (p : X L) : ℝ :=
  ∑ i : Fin L, (-1 : ℝ) ^ (i.val + 1) * alpha ^ (i.val + 2) * (if p.val i then 1 else 0)
/-- The set of legal streams with the specified initial window. -/
def C {L : ℕ} (p : X L) : Set LegalDigits := {x | P L x = p}
/-- The affine interval associated with a completed window. -/
noncomputable def I {L : ℕ} (p : X L) : Set ℝ :=
  (fun t => Sp p + r ^ d p * t) '' Set.Icc a b
/-- The lower real endpoint of a window interval. -/
noncomputable def ell {L : ℕ} (p : X L) : ℝ :=
  min (Sp p + r ^ d p * a) (Sp p + r ^ d p * b)
/-- The upper real endpoint of a window interval. -/
noncomputable def upper {L : ℕ} (p : X L) : ℝ :=
  max (Sp p + r ^ d p * a) (Sp p + r ^ d p * b)
/-- The open circle arc obtained from the interior of a window interval. -/
noncomputable def A {L : ℕ} (p : X L) : Set Circle :=
  (fun t : ℝ => (t : Circle)) '' Set.Ioo (ell p) (upper p)
/-- The negative golden phases indexed from one through the window count. -/
noncomputable def B (L : ℕ) : Set Circle := E '' Set.Icc 1 (G L)
/-- The circle images of the endpoints of all intervals of the specified window length. -/
noncomputable def actualCuts (L : ℕ) : Set Circle :=
  {z | ∃ p : X L, z = ((ell p : ℝ) : Circle) ∨ z = ((upper p : ℝ) : Circle)}

set_option maxHeartbeats 800000 in
/-- Legal windows partition the signed value interval into closed affine intervals with
disjoint interiors, exact negative golden cuts, and the indicated oriented endpoint streams. -/
theorem window_cylinder_partition :
  (∀ m, 2 ≤ m → ∃! w : List Block, seamIndex w = m) ∧
  (∀ m, 1 ≤ m → eMinus m ≠ ePlus m ∧
    ∀ x, D5.S1.Digit.Infinite.MultiplierObstruction.phase x = E m ↔
      x = eMinus m ∨ x = ePlus m) ∧
  (∀ L, 1 ≤ L →
    (Set.univ : Set (X L)).Finite ∧
    (∀ p : X L, len (c p) = d p ∧ S (c p) = Sp p ∧
      C p = Set.range (prependWord (c p)) ∧ signedValue '' C p = I p ∧
      I p = Set.Icc (ell p) (upper p) ∧
      upper p - ell p = alpha ^ d p ∧ 0 < alpha ^ d p ∧ alpha ^ d p < 1) ∧
    (⋃ p : X L, I p) = Set.Icc a b ∧
    (∀ p q : X L, p ≠ q → Disjoint (Set.Ioo (ell p) (upper p))
      (Set.Ioo (ell q) (upper q))) ∧
    actualCuts L = B L ∧
    (∀ p : X L, ∃ i j : ℕ, 1 ≤ i ∧ i ≤ G L ∧ 1 ≤ j ∧ j ≤ G L ∧
      ((ell p : ℝ) : Circle) = E i ∧ ((upper p : ℝ) : Circle) = E j ∧
      C p = D5.S1.Digit.Infinite.MultiplierObstruction.phase ⁻¹' A p ∪
        {ePlus i, eMinus j}) ∧
    (∀ m, 1 ≤ m → (P L (eMinus m) ≠ P L (ePlus m) ↔ m ≤ G L))) := by
  sorry

end D5.S1.Digit.Infinite.WindowCylinderPartition
