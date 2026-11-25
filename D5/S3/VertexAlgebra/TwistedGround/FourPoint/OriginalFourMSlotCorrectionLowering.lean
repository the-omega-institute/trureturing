/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same-puncture physical correction factors in the actual lowering word. -/

import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering

/-! Factor the scale at each contracted occurrence and identify the
remaining correction endpoint sum with the actual lowering recurrence. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlotCorrectionLowering

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMSpatialWickPartition (liftedScale)
open OriginalFourMSpatialWickPartition (correctionTaylor nativeTaylor
  physical_marked_coefficient_wick_partition)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalMean)
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMChartProduct (chartTau)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalFourMWickLowering (eval_word_partition pairWeight)
open HalfFock.OriginalHalfCurrentWickPolynomial (word creator eval_word_eq_lowering)
open OriginalFourMChargeCoset (oscillatorLower)
open AffineWickConvolution (partitions)
open AffineOccurrenceWick (wick)
open AffineWickBlocks (wick_blocks wick_congr_on)
open private pair_symm from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering

private theorem wick_scale {X : Type*} (s : X → ℂ) (A : Matrix X X ℂ) (μ : X → ℂ)
    (l : List X) :
    wick (Matrix.of fun i j => s i * s j * A i j) (fun i => s i * μ i) l =
      (l.map s).prod * wick A μ l := by
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => simp [wick]
    | cons a l =>
      simp only [wick, Matrix.of_apply, List.map_cons, List.prod_cons, mul_add]
      rw [ih l (Nat.lt_succ_self _)]
      rw [Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [ih (l.eraseIdx j) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))]
        have hj : s (l.get j) * ((l.eraseIdx j).map s).prod = (l.map s).prod := by
          have hj' : (j : ℕ) < (l.map s).length := by simpa only [List.length_map] using j.isLt
          have h := List.CommMonoid.mul_prod_eraseIdx (l := l.map s) hj'
          simpa only [List.getElem_map, List.eraseIdx_map, List.get_eq_getElem] using h
        linear_combination (s a * A a (l.get j) * wick A μ (l.eraseIdx j)) * hj

/-- The physical correction on any word at one puncture factors one signed
scale per occurrence, leaving the central lowering pair weight. -/
theorem same_slot_correction {X : Type*} (D : LatticeData) (c : Chart) (x : ℝ)
    (i : Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X) :
    wick (correctionTaylor D c x (fun _ => i) colour n) 0 l =
      (l.map fun a => liftedScale c x i (n a)).prod *
        wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
          (colour a, n a) (colour b, n b)) 0 l := by
  convert wick_scale (fun a => liftedScale c x i (n a))
    (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
      (colour a, n a) (colour b, n b)) 0 l using 2
  · ext a b
    simp [correctionTaylor, pairWeight]
  · funext a
    simp

/-- At any puncture the actual finite inverse lowering flow is the
correction-endpoint sum times the surviving creators, with one normalization
per lowering order. The physical correction contributes the displayed signed
scales by `same_slot_correction`. -/
theorem slot_lowering_partition {X : Type*} [Finite X] (D : LatticeData)
    (hu : IsUnit D.G.det) (c : Chart) (i : Puncture) (colour : X → Fin D.rank) (n : X → ℕ)
    (l : List X) (N : ℕ)
    (hN : (word D (l.map fun a => (colour a, n a))).natDegree < N) :
    (∑ k ∈ Finset.range N, ((-loweringParameter c i) ^ k / (k.factorial : ℂ)) •
      (oscillatorLower D ^ k) ((l.map fun a => MvPolynomial.X (colour a, n a)).prod)) =
      ((partitions l).map fun p =>
        MvPolynomial.C (wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
          (colour a, n a) (colour b, n b)) 0 p.1) *
          (p.2.map fun a => (creator D (colour a, n a)).eval
            (MvPolynomial.C (-loweringParameter c i))).prod).sum := by
  simpa only [List.map_map, Function.comp_def] using
    (eval_word_eq_lowering D hu (l.map fun a => (colour a, n a))
      (-loweringParameter c i) N hN).symm.trans
      (eval_word_partition D hu (-loweringParameter c i) (fun a => (colour a, n a)) l)

/-- For the actual four punctures, each correction endpoint contributes
its own signed scale. The central Wick sum factors into the four ordered
within-puncture contraction sums. -/
theorem physical_correction_by_slot {X : Type*} [Finite X] (D : LatticeData)
    (hu : IsUnit D.G.det) (c : Chart) (x : ℝ) (slot : X → Puncture)
    (colour : X → Fin D.rank) (n : X → ℕ) (l : List X) :
    wick (correctionTaylor D c x slot colour n) 0 l =
      (l.map fun a => liftedScale c x (slot a) (n a)).prod *
        (open Classical in ∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
          wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
            (colour a, n a) (colour b, n b)) 0 (l.filter fun a => decide (slot a = i))) := by
  classical
  let s a := liftedScale c x (slot a) (n a)
  let C : Matrix X X ℂ := Matrix.of fun a b => if slot a = slot b then
    pairWeight D (-loweringParameter c (slot a)) (colour a, n a) (colour b, n b) else 0
  let slots : Finset Puncture := {.P, .Q, .R, .S}
  have he : correctionTaylor D c x slot colour n = Matrix.of (fun a b => s a * s b * C a b) := by
    ext a b
    by_cases hab : slot a = slot b <;> simp [correctionTaylor, s, C, pairWeight, hab]
  have hs (a b : X) : C a b = C b a := by
    by_cases hab : slot a = slot b
    · simp only [C, Matrix.of_apply, hab, ite_true, pairWeight,
        pair_symm D hu (colour a, n a) (colour b, n b)]
    · simp [C, hab, Ne.symm hab]
  have hz (a b : X) (h : slot a ≠ slot b) : C a b = 0 := by simp [C, h]
  have hcoverage (a : X) : slot a ∈ slots := by
    cases slot a <;> simp [slots]
  have hw := wick_scale s C 0 l
  simp only [Pi.zero_apply, mul_zero] at hw
  change wick (Matrix.of (fun a b => s a * s b * C a b)) 0 l = _ at hw
  rw [he, hw]
  rw [wick_blocks C slot hs hz slots l (fun a _ => hcoverage a)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply wick_congr_on
  intro a ha b hb
  have h₁ : slot a = i := by simpa using (List.mem_filter.mp ha).2
  have h₂ : slot b = i := by simpa using (List.mem_filter.mp hb).2
  simp [C, h₁, h₂]

open Classical in
/-- In the literal fixed-charge physical Taylor coefficient, the
correction endpoints contribute their signed scales and four independent
central Wick sums. The complement retains the entire native affine factor. -/
theorem physical_marked_coefficient_by_slot {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) (q : Charge D) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
      (physicalChargeSummand D slot colour upperA c x q) 0 =
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        ((partitions l).map fun p =>
          (p.1.map fun a => liftedScale c x (slot a) (n a)).prod *
          (open Classical in ∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
            wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
              (colour a, n a) (colour b, n b)) 0 (p.1.filter fun a => decide (slot a = i))) *
          wick (nativeTaylor D upperA c x slot colour n)
            (fun i => coefficient (n i) (fun u =>
              physicalMean D q upperA c x slot colour i u * relative c (slot i))) p.2).sum := by
  rw [physical_marked_coefficient_wick_partition D slot colour upperA c hx hx₁ q n l hl]
  simp only [physical_correction_by_slot D hu c x slot colour n]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlotCorrectionLowering
