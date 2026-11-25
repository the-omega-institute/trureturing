/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier overlap for the native assignments of arbitrary physical marked jets. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick

/-! Normal convergence and Fourier overlap apply to the fixed-charge
expansion with independent native mode assignments. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOverlap

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open FourPoint.OriginalFourMActualChart
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMChartProduct (chartTau chartPeriod chart_charge_data)
open OriginalFourMSpatialWick (spatialCoefficient physical_chart_jet_hasSum
  physical_chart_coefficient_overlap)
open OriginalFourMFixedChargeWick
open OriginalFourMWickLowering (pairWeight)
open OriginalFourMSpatialWickPartition (liftedScale)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)
open AffineWickAssignments (assign)

variable {X : Type*} [Fintype X] [DecidableEq X]

open Classical in
/-- One charge summand of the physical coefficient written in native
assigned modes with the actual chart normalization. -/
def assignedChargeTerm (D : LatticeData) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) (x : ℝ) (q : Charge D) (n : X → ℕ) (l : List X) : ℂ :=
  (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
    (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
      ((partitions l).map fun p =>
        (p.1.map fun a => liftedScale c x (slot a) (n a)).prod *
        (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
          wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
            (colour a, n a) (colour b, n b)) 0 (p.1.filter fun a => decide (slot a = i))) *
        assign (modeMatrix c x slot n) p.2
          (wick (nativeModeCovariance D c x slot colour n)
            (nativeModeMean D q c x slot colour n))).sum)

/-- Sum the native assignments on the specified charge fibre. -/
def assignedSector (D : LatticeData) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) (x : ℝ) (a : ModTwoCharge D) (n : X → ℕ) (l : List X) : ℂ :=
  ∑' q : {q : Charge D // reduceCharge D q = a},
    assignedChargeTerm D slot colour upperA c x q.val n l

/-- The native mode assignment formula can be summed over the actual
charge fibre using the existing normal-convergence result. -/
theorem assigned_charge_hasSum (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (a : ModTwoCharge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      assignedChargeTerm D slot colour upperA c x q.val n l)
      (spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
        (fun z => physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0) := by
  obtain ⟨hp, hτ⟩ := chart_charge_data upperA c hx hx₁
  have hs := physical_chart_jet_hasSum D hu hD slot colour upperA c hx hx₁ hp hτ a
    (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
  simpa only [assignedChargeTerm,
    physical_marked_coefficient_assign D hu slot colour upperA c hx hx₁ hc _ n l hl] using hs

/-- The native assigned charge expansion is absolutely summable on each charge fibre. -/
theorem assigned_charge_summable_norm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (a : ModTwoCharge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    Summable (fun q : {q : Charge D // reduceCharge D q = a} =>
      ‖assignedChargeTerm D slot colour upperA c x q.val n l‖) :=
  (assigned_charge_hasSum D hu hD slot colour upperA c hx hx₁ hc a n l hl).summable.norm

/-- The true D lip and B chart obey the physical Fourier overlap on the
complete finite assignments of an arbitrary occurrence word. -/
theorem assigned_fourier_overlap (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {w : ℂ}
    (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (a : ModTwoCharge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    let F := fun c b => assignedSector D slot colour true c x b n l
    F .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * F .A b) ∧
    F .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * F .A b) := by
  classical
  have hA : ‖parameter .A (x : ℂ)‖ < 1 := by
    rw [← hwA, norm_pow]
    nlinarith [norm_nonneg w]
  have hB : ‖parameter .B (x : ℂ)‖ < 1 := by
    simpa [parameter, Complex.norm_real, abs_of_pos hx] using hx₁
  have hs (c : Chart) (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨
      c = .D ∧ true = true) (b : ModTwoCharge D) :=
    (assigned_charge_hasSum D hu hD slot colour true c hx hx₁ hc b n l hl).tsum_eq
  have eA := hs .A (Or.inl ⟨Or.inl rfl, hA⟩)
  have eB := hs .B (Or.inl ⟨Or.inr rfl, hB⟩)
  have eD := hs .D (Or.inr ⟨rfl, rfl⟩)
  have h := physical_chart_coefficient_overlap D hu hD hr slot colour true hx hx₁ hwA hw
    (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl) a
  dsimp only at h ⊢
  simpa only [← eA, ← eB, ← eD, assignedSector] using h

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOverlap
