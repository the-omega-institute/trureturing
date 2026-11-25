/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Correction-edge regrouping for the literal physical marked jet. -/

import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick

/-! Partition the physical marked jet into correction and native Wick factors
before taking the spatial Taylor coefficients. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMOccurrenceWick

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags rawLocal)
open OriginalFourMPhysicalCovariance (jac slotCorrection relative physicalCovariance
  physical_covariance_swap)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalEntry physicalMean physicalProduct)
open OriginalFourMSignedOverlap (chartCovariance)
open OriginalFourMChartProduct (chartTau chartPeriod chart_charge_data)
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open OriginalFourMSpatialWick (spatialCoefficient spatialCoefficient_split_marks
  spatialCoefficient_const_mul physical_chart_jet_hasSum)
open NativeAffineExternalCoefficient (coordinateJet)
open AffineOccurrenceWick (affineMoment_eq_wick wick)
open AffineWickConvolution (partitions wick_add_covariance)
open private mark_jet_eq_moment from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick
open private same_flags freeCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

variable {X : Type*}

/-- The signed Gram-weighted inverse-coordinate correction in the actual
physical covariance. Each endpoint carries its own relative sign. -/
def correctionEntry (D : LatticeData) (c : Chart) (x : ℝ) (slot : X → Puncture)
    (colour : X → Fin D.rank) (u : X → ℂ) : Matrix X X ℂ :=
  fun i j => (D.G (colour i) (colour j) : ℂ) *
    (-(slotCorrection c x (slot i) (slot j) (u i) (u j)) /
      (jac c x (slot i) (u i) * jac c x (slot j) (u j))) *
    relative c (slot i) * relative c (slot j)

/-- The signed native chart covariance pulled through each inverse coordinate
and divided by the two half-Jacobians. -/
def nativeEntry (D : LatticeData) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (u : X → ℂ) : Matrix X X ℂ :=
  fun i j => (D.G (colour i) (colour j) : ℂ) *
    (chartCovariance upperA c x (flags c (slot i)).1 (flags c (slot j)).1
      (flags c (slot i)).2 (flags c (slot j)).2
      (rawLocal c x (slot i) (u i)) (rawLocal c x (slot j) (u j)) /
      (jac c x (slot i) (u i) * jac c x (slot j) (u j))) *
    relative c (slot i) * relative c (slot j)

private theorem correction_zero (D : LatticeData) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (u : X → ℂ) {i j : X}
    (h : slot i ≠ slot j) : correctionEntry D c x slot colour u i j = 0 := by
  have hn : ¬ ((flags c (slot i)).1 = (flags c (slot j)).1 ∧
      (flags c (slot i)).2 = (flags c (slot j)).2) := fun he => h (same_flags c he)
  simp only [correctionEntry, slotCorrection, ite_eq_right hn, neg_zero, zero_div, mul_zero, zero_mul]

private theorem correction_symm (D : LatticeData) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (u : X → ℂ) (i j : X) :
    correctionEntry D c x slot colour u i j = correctionEntry D c x slot colour u j i := by
  by_cases h : slot i = slot j
  · simp only [correctionEntry, h, D.symmetric (colour j) (colour i),
      slotCorrection, and_self, ite_true, freeCorrection]
    ring
  · rw [correction_zero D c x slot colour u h, correction_zero D c x slot colour u (Ne.symm h)]

private theorem physicalEntry_split (D : LatticeData) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (u : X → ℂ) (i j : X) :
    physicalEntry D upperA c x slot colour i j (u i) (u j) *
      relative c (slot i) * relative c (slot j) =
      nativeEntry D upperA c x slot colour u i j + correctionEntry D c x slot colour u i j := by
  simp only [physicalEntry, physicalCovariance, nativeEntry, correctionEntry, sub_div, neg_div]
  ring

/-- Wick regrouping of the actual fixed-charge marked summand. The partition
left word consists entirely of same-puncture correction endpoints. -/
theorem physical_mark_jet_partition [Fintype X] [DecidableEq X] (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (q : Charge D) (l : List X) (u : X → ℂ) :
    coordinateJet l (fun v => physicalChargeSummand D slot colour upperA c x q (Sum.elim u v)) 0 =
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        ((partitions l).map fun p => wick (correctionEntry D c x slot colour u) 0 p.1 *
          wick (nativeEntry D upperA c x slot colour u)
            (fun i => physicalMean D q upperA c x slot colour i (u i) * relative c (slot i)) p.2).sum := by
  classical
  let N := nativeEntry D upperA c x slot colour u
  let C := correctionEntry D c x slot colour u
  let μ := fun i => physicalMean D q upperA c x slot colour i (u i) * relative c (slot i)
  have hc : ∀ i j, C i j = C j i := correction_symm D c x slot colour u
  have he (i j : X) : physicalEntry D upperA c x slot colour i j (u i) (u j) *
      relative c (slot i) * relative c (slot j) = (N + C) i j :=
    physicalEntry_split D upperA c x slot colour u i j
  have hn (i j : X) : N i j = N j i := by
    have hs : physicalEntry D upperA c x slot colour i j (u i) (u j) *
          relative c (slot i) * relative c (slot j) =
        physicalEntry D upperA c x slot colour j i (u j) (u i) *
          relative c (slot j) * relative c (slot i) := by
      simp only [physicalEntry, D.symmetric (colour j) (colour i),
        physical_covariance_swap upperA c x (slot i) (slot j) (u i) (u j)]
      ring
    rw [he i j, he j i, Matrix.add_apply, Matrix.add_apply, hc i j] at hs
    exact add_right_cancel hs
  let P := Matrix.of fun i j => physicalEntry D upperA c x slot colour i j (u i) (u j) *
    relative c (slot i) * relative c (slot j)
  have hA : P = N + C := by
    funext i j
    exact he i j
  rw [mark_jet_eq_moment]
  change _ * OriginalChargedRowSource.affineMoment P μ _ = _
  rw [hA]
  have hW := affineMoment_eq_wick (N + C) μ
    (fun i j => by simp only [Matrix.add_apply, hn i j, hc i j]) id l
  simp only [List.map_id, Matrix.submatrix_id_id, Function.comp_id] at hW
  rw [hW, wick_add_covariance N C μ hn hc]

/-- The literal independent mark and spatial Taylor coefficient is the
spatial extraction of the correction-endpoint partition at fixed charge. -/
theorem physical_marked_coefficient_partition [Fintype X] [DecidableEq X] (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
      (physicalChargeSummand D slot colour upperA c x q) 0 =
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        spatialCoefficient n l (fun u =>
          ((partitions l).map fun p => wick (correctionEntry D c x slot colour u) 0 p.1 *
            wick (nativeEntry D upperA c x slot colour u)
              (fun i => physicalMean D q upperA c x slot colour i (u i) *
                relative c (slot i)) p.2).sum) 0 := by
  rw [spatialCoefficient_split_marks n l hl]
  simp only [physical_mark_jet_partition D slot colour upperA c x q l,
    spatialCoefficient_const_mul]

/-- The correction-endpoint partition holds in each charge summand of the
convergent physical marked coefficient on the real overlap. -/
theorem physical_marked_partition_hasSum [Fintype X] [DecidableEq X] (D : LatticeData)
    (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) (a : ModTwoCharge D) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) :
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
          (bilinear D q.val q.val : ℂ) / 2) *
        spatialCoefficient n l (fun u =>
          ((partitions l).map fun p => wick (correctionEntry D c x slot colour u) 0 p.1 *
            wick (nativeEntry D upperA c x slot colour u)
              (fun i => physicalMean D q.val upperA c x slot colour i (u i) *
                relative c (slot i)) p.2).sum) 0))
      (spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
        (fun z => physicalProduct D hu slot colour upperA x c a
          (z ∘ Sum.inl) (z ∘ Sum.inr)) 0) := by
  obtain ⟨hp, hτ⟩ := chart_charge_data upperA c hx hx₁
  have hs := physical_chart_jet_hasSum D hu hD slot colour upperA c hx hx₁ hp hτ a
    (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
  simpa only [physical_marked_coefficient_partition D slot colour upperA c x _ n l hl] using hs

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMOccurrenceWick
