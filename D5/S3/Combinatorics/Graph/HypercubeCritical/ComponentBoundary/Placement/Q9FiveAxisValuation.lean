/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisValuation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisValuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The valuation stores occupancy, the parity prefix, switching signs, contact witnesses, and occupied polarities. Each range is disjoint and has the original zero-based formula indices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisContactWitnesses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisExteriorPolarity

/-! A valuation for occupancy, signed edge variables and occupied polarities. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisValuation

open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec cubeBitVec_xor_single)
open BalancedCriticalSpectrum (Q flip)
open Q9SharedContactCNF (Word Variable wordIndex)
open Q9TightDistanceTwoCNF (support)
open private valuation_index from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF
open Q9FiveAxisContactWitnesses (installWitnesses)
open Q9FiveAxisSignedNormalization (rupFlipSign)

def signIndex (b : Bool) (w : Word) : ℕ := 9216 + wordIndex b w

def polarityIndex (b : Bool) (w : Word) (p : Bool) : ℕ :=
  12288 + 2 * wordIndex b w + (if p then 1 else 0)

private def signValue (f : Q 9 → ℤ) (p : Bool) (x : Q 9) : Prop :=
  f x = if p then 1 else -1

private def wordAt (n : ℕ) : Bool × Word :=
  (decide (512 ≤ n), BitVec.ofNat 9 n)

private theorem wordAt_index (b : Bool) (w : Word) :
    wordAt (wordIndex b w) = (b, w) := by
  have hw : w.toNat < 512 := w.toFin.isLt
  cases b
  · simp [wordAt, wordIndex, hw]
  · have h : BitVec.ofNat 9 (512 + w.toNat) = w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      change (512 + w.toNat) % 512 = w.toNat
      omega
    simp [wordAt, wordIndex, h]

/-- The prefix variables are inherited from the existing cubic-support model.
The two new blocks record the positive sign and the occupied polarity. -/
noncomputable def valuation (C D : Finset (Q 9)) (f : Bool → Q 9 → ℤ) :
    Sat.Valuation := fun n =>
  if n < 9216 then Q9TightDistanceTwoCNF.valuation (support C D) n
  else if n < 10240 then
    let (b, w) := wordAt (n - 9216)
    signValue (f b) true (cubeBitVec 9 w)
  else if n < 12288 then installWitnesses C D (fun _ => False) n
  else
    let k := n - 12288
    let (b, w) := wordAt (k / 2)
    signValue (f b) (decide (k % 2 = 1)) (cubeBitVec 9 w)

theorem occupancy_value (C D : Finset (Q 9)) (f : Bool → Q 9 → ℤ) (b : Bool) (w : Word) :
    valuation C D f (Variable.occupied b w).index ↔ cubeBitVec 9 w ∈ support C D b := by
  have hw : w.toNat < 512 := w.toFin.isLt
  have hidx : (Variable.occupied b w).index < 9216 := by
    cases b <;> simp [Variable.index, wordIndex] <;> omega
  rw [valuation, if_pos hidx]
  rw [valuation_index]
  rfl

theorem sign_value (C D : Finset (Q 9)) (f : Bool → Q 9 → ℤ) (b : Bool) (w : Word) :
    valuation C D f (signIndex b w) ↔ f b (cubeBitVec 9 w) = 1 := by
  have hw : w.toNat < 512 := w.toFin.isLt
  have hidx : signIndex b w < 10240 := by cases b <;> simp [signIndex, wordIndex] <;> omega
  have hstart : ¬ signIndex b w < 9216 := by simp [signIndex]
  rw [valuation, if_neg hstart, if_pos hidx]
  simp [signIndex, wordAt_index, signValue]

theorem polarity_value (C D : Finset (Q 9)) (f : Bool → Q 9 → ℤ)
    (b : Bool) (w : Word) (p : Bool) :
    valuation C D f (polarityIndex b w p) ↔ signValue (f b) p (cubeBitVec 9 w) := by
  let offset : ℕ := if p then 1 else 0
  have hlow : 12288 ≤ polarityIndex b w p := by unfold polarityIndex; omega
  have hsub : polarityIndex b w p - 12288 = 2 * wordIndex b w + offset := by
    change 12288 + 2 * wordIndex b w + offset - 12288 = _
    omega
  have ho : offset < 2 := by cases p <;> decide
  have hdiv : (2 * wordIndex b w + offset) / 2 = wordIndex b w := by omega
  have hmod : (2 * wordIndex b w + offset) % 2 = offset := by omega
  rw [valuation, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hsub]
  dsimp only
  rw [hdiv, hmod, wordAt_index]
  cases p <;> rfl

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisValuation
