/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMFixedChargeWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMFixedChargeWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-charge Wick transport by native mode assignment. -/

import D5.S3.VertexAlgebra.TwistedGround.AffineWickAssignments
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries

/-! The finite fixed-charge Wick expansion retains every independent
surviving mode choice and all four puncture correction factors. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMFixedChargeWick

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalMean)
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMChartProduct (chartTau)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMOccurrenceWick (liftedScale)
open OriginalFourMSlotCorrectionLowering (physical_marked_coefficient_by_slot)
open OriginalFourMSpatialWickPartition (nativeTaylor)
open OriginalFourMNativeWickEntries (nativeTaylor_ab nativeTaylor_d meanTaylor_ab meanTaylor_d)
open OriginalFourMWickLowering (pairWeight)
open OriginalFourMInverseJets (inverseJetWeight)
open OriginalFourMSlitMean (slitMeanEntry slitCovarianceEntry)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalGaussianExternalBlocks (External)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)
open AffineWickAssignments (assign wick_transport)
open NativeAffineTransport (transportCovariance transportMean)
open private dLipCovarianceEntry dLipMeanEntry from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel

variable {X : Type*}

/-- Each surviving occurrence chooses a mode from zero to its requested mode. -/
abbrev Mode (n : X → ℕ) := Σ i : X, Fin (n i + 1)

private def external (D : LatticeData) (c : Chart) (slot : X → Puncture)
    (colour : X → Fin D.rank) {n : X → ℕ} (a : Mode n) : External D :=
  ((flags c (slot a.1)).2, colour a.1, a.2)

/-- Gram-weighted entries of the literal slit or true-lip covariance. -/
def nativeModeCovariance (D : LatticeData) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) :
    Matrix (Mode n) (Mode n) ℂ :=
  Matrix.of fun a b =>
    let l := (flags c (slot a.1)).1
    let k := (flags c (slot b.1)).1
    let e := external D c slot colour a
    let f := external D c slot colour b
    match c with
    | .A | .B => slitCovarianceEntry D l k e f (parameter c x)
    | .D => dLipCovarianceEntry D true l k e f (parameter c x)

/-- Charge-linear entries of the literal slit or true-lip source. -/
def nativeModeMean (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) : Mode n → ℂ :=
  fun a =>
    let l := (flags c (slot a.1)).1
    let e := (flags c (slot a.1)).2
    (bilinear D (unitCharge D (colour a.1)) q : ℂ) *
      match c with
      | .A | .B => slitMeanEntry l e a.2 (parameter c x)
      | .D => dLipMeanEntry true l e a.2 (parameter c x)

/-- The diagonal occurrence weights, with both the relative sign and the
lifted inverse scale on the occurrence selecting the mode. -/
def modeMatrix [DecidableEq X] (c : Chart) (x : ℝ) (slot : X → Puncture) (n : X → ℕ) :
    Matrix X (Mode n) ℂ :=
  Matrix.of fun i a => if i = a.1 then
    relative c (slot a.1) * inverseJetWeight c x (slot a.1) (n a.1) a.2 else 0

variable [Fintype X] [DecidableEq X]

private theorem sum_mode (c : Chart) (x : ℝ) (slot : X → Puncture) (n : X → ℕ) (i : X)
    (f : Mode n → ℂ) :
    (∑ a, modeMatrix c x slot n i a * f a) =
      relative c (slot i) *
        ∑ k : Fin (n i + 1), inverseJetWeight c x (slot i) (n i) k * f ⟨i, k⟩ := by
  simp only [Fintype.sum_sigma, modeMatrix, Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, mul_assoc, Finset.mul_sum]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem transport_mode_covariance (D : LatticeData) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i j : X) :
    transportCovariance (modeMatrix c x slot n) (nativeModeCovariance D c x slot colour n) i j =
      (relative c (slot i) * relative c (slot j)) *
        ∑ a : Fin (n i + 1), ∑ b : Fin (n j + 1),
          nativeModeCovariance D c x slot colour n ⟨i, a⟩ ⟨j, b⟩ *
            inverseJetWeight c x (slot i) (n i) a * inverseJetWeight c x (slot j) (n j) b := by
  let U := modeMatrix c x slot n
  let K := nativeModeCovariance D c x slot colour n
  change (∑ a, ∑ b, U i a * K a b * U j b) = _
  have he (a : Mode n) : (∑ b, U i a * K a b * U j b) =
      U i a * (relative c (slot j) * ∑ k : Fin (n j + 1),
        inverseJetWeight c x (slot j) (n j) k * K a ⟨j, k⟩) := by
    rw [← sum_mode c x slot n j]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [he]
  rw [sum_mode c x slot n i (fun a => relative c (slot j) *
    ∑ k : Fin (n j + 1), inverseJetWeight c x (slot j) (n j) k * K a ⟨j, k⟩)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem double_sum_range (m n : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ a : Fin m, ∑ b : Fin n, f a b) =
      ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, f a b := by
  calc
    _ = ∑ a : Fin m, ∑ b ∈ Finset.range n, f a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fin.sum_univ_eq_sum_range (f a) n
    _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range n, f a b) m

private theorem native_covariance_transport (D : LatticeData) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (h : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) :
    nativeTaylor D upperA c x slot colour n =
      transportCovariance (modeMatrix c x slot n) (nativeModeCovariance D c x slot colour n) := by
  ext i j
  rw [transport_mode_covariance]
  let F (a b : ℕ) : ℂ :=
    let l := (flags c (slot i)).1
    let k := (flags c (slot j)).1
    let e := ((flags c (slot i)).2, colour i, a)
    let f := ((flags c (slot j)).2, colour j, b)
    (match c with
      | .A | .B => slitCovarianceEntry D l k e f (parameter c x)
      | .D => dLipCovarianceEntry D true l k e f (parameter c x)) *
      inverseJetWeight c x (slot i) (n i) a * inverseJetWeight c x (slot j) (n j) b
  have hF (a : Fin (n i + 1)) (b : Fin (n j + 1)) :
      nativeModeCovariance D c x slot colour n ⟨i, a⟩ ⟨j, b⟩ *
        inverseJetWeight c x (slot i) (n i) a * inverseJetWeight c x (slot j) (n j) b =
        F a b := by
    cases c <;> rfl
  simp only [hF]
  rw [double_sum_range (n i + 1) (n j + 1) F]
  rcases h with ⟨hc, hr⟩ | ⟨rfl, rfl⟩
  · have he := nativeTaylor_ab D upperA c hx hx₁ hc hr slot colour n i j
    rcases hc with rfl | rfl <;> exact he
  · exact nativeTaylor_d D hx hx₁ slot colour n i j

private theorem native_mean_transport (D : LatticeData) (q : Charge D) (upperA : Bool)
    (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (h : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) :
    (fun i => coefficient (n i) (fun u =>
      physicalMean D q upperA c x slot colour i u * relative c (slot i))) =
      transportMean (modeMatrix c x slot n) (nativeModeMean D q c x slot colour n) := by
  funext i
  change _ = ∑ a, modeMatrix c x slot n i a * nativeModeMean D q c x slot colour n a
  rw [sum_mode c x slot n i]
  let M (a : ℕ) : ℂ :=
    let l := (flags c (slot i)).1
    let e := (flags c (slot i)).2
    match c with
    | .A | .B => slitMeanEntry l e a (parameter c x)
    | .D => dLipMeanEntry true l e a (parameter c x)
  let B : ℂ := (bilinear D (unitCharge D (colour i)) q : ℂ)
  let W := inverseJetWeight c x (slot i) (n i)
  have hM (k : Fin (n i + 1)) : nativeModeMean D q c x slot colour n ⟨i, k⟩ =
      B * M k := by
    cases c <;> rfl
  simp only [hM]
  rw [Fin.sum_univ_eq_sum_range (fun k => W k * (B * M k)) (n i + 1)]
  have he : coefficient (n i) (fun u => physicalMean D q upperA c x slot colour i u *
      relative c (slot i)) =
      (B * relative c (slot i)) * ∑ a ∈ Finset.range (n i + 1), M a * W a := by
    rcases h with ⟨hc, hr⟩ | ⟨rfl, rfl⟩
    · have he := meanTaylor_ab D q upperA c hx hx₁ hc hr slot colour n i
      rcases hc with rfl | rfl <;> exact he
    · exact meanTaylor_d D q hx hx₁ slot colour n i
  rw [he]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

open Classical in
/-- Fixed-charge transport to the original slit and true-lip Wick arrays,
with one independent finite mode assignment per surviving occurrence. -/
theorem physical_marked_coefficient_assign (D : LatticeData) (hu : IsUnit D.G.det)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (h : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
      (physicalChargeSummand D slot colour upperA c x q) 0 =
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        ((partitions l).map fun p =>
          (p.1.map fun a => liftedScale c x (slot a) (n a)).prod *
          (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
            wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
              (colour a, n a) (colour b, n b)) 0 (p.1.filter fun a => decide (slot a = i))) *
          assign (modeMatrix c x slot n) p.2
            (wick (nativeModeCovariance D c x slot colour n)
              (nativeModeMean D q c x slot colour n))).sum := by
  rw [physical_marked_coefficient_by_slot D hu slot colour upperA c hx hx₁ q n l hl]
  simp only [native_covariance_transport D upperA c hx hx₁ h slot colour n,
    native_mean_transport D q upperA c hx hx₁ h slot colour n, wick_transport]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMFixedChargeWick
