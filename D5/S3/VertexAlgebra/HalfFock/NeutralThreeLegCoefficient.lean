/- GID: D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite neutral corrected-field coefficient identity with repeated occupations. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
import D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal

/-!
The source side is the actual `correctedField` and its literal finite Corr;
normal coefficients remain pointwise finite sums in the actual tensor module.
The Gaussian coefficient is the native Corr moment, with repeated labelled
positions retained. This file does not introduce a replacement field or an
analytic evaluation of an unrestricted Hahn series.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

open private current_identity_coefficient from D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
open private current_charged_zero_identity from D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal

namespace D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient

open MvPolynomial
open LatticeGeneratingFieldLocality
open LatticeHalfFockFockNormalField
open LatticeHalfFock
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField
open LatticeHalfFockChargedTensorCoefficients
open D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
open D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate

/-- The actual neutral source with an arbitrary repeated oscillator occupation. -/
def neutralSource (D : LatticeData) (d : Index D →₀ ℕ) : Carrier D :=
  Finsupp.single 0 (monomial d 1)

/-- The native vector-valued coefficient of the actual corrected neutral field. -/
def nativeNeutralCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (d : Index D →₀ ℕ) (e : ℤ) (x : ActualTensor D hu) : ActualTensor D hu :=
  (correctedField D hu (neutralSource D d)).coeff e x

/-- Taking the source component of the actual corrected field exposes the
literal corrected polynomial. -/
theorem nativeNeutralCoefficient_source
    (D : LatticeData) (hu : IsUnit D.G.det) (d : Index D →₀ ℕ)
    (e : ℤ) (x : ActualTensor D hu) :
    nativeNeutralCoefficient D hu d e x =
      (correctedPolynomial D hu 0 (monomial d 1)).coeff e x := by
  rw [nativeNeutralCoefficient, neutralSource, correctedField, Finsupp.lsum_single]

/-- The actual neutral Corr readout has the factorial Gaussian coefficient for
an arbitrary finite family of oscillator linear forms and arbitrary repeated
occupations. -/
theorem nativeNeutralCorrection_gaussian
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (z : ℂ) (c : I → Index D →₀ ℂ) (d : I →₀ ℕ) :
    sourceVacuum D z (∏ i, linearForm D (c i) ^ d i) =
      (FactorialFockMetric.weight d : ℂ) *
        gaussianCoefficient (covarianceMatrix D z c) d := by
  exact sourceVacuum_linearForms D z c d

/-- With the genuine zero-charge seed, the native normal recursion is the
literal creation-left/annihilation-right product and its integer exponent
selector. -/
theorem flatCoefficient_neutral_identity
    (D : LatticeData) (hu : IsUnit D.G.det) (word : List (Index D))
    (modes : ModeTuple D word) (e : ℤ) (x : ActualTensor D hu) :
    flatCoefficient D hu FieldNormalProduct.identityField word modes e x =
      if e + 2 * modeSum D word modes + jetShift D word = 0 then
        (leftAction D hu word modes * rightAction D hu word modes) x else 0 := by
  rw [flatCoefficient_factorization]
  simp only [Module.End.mul_apply]
  rw [current_identity_coefficient]
  by_cases hzero : e + 2 * modeSum D word modes + jetShift D word = 0
  · rw [if_pos hzero]
    simp [hzero]
  · rw [if_neg hzero]
    simp [hzero]

/-- Shift extraction is performed on the actual Corr support before any native
coefficient is read. -/
theorem nativeNeutralCoefficient_shift_expansion
    (D : LatticeData) (hu : IsUnit D.G.det) (d : Index D →₀ ℕ)
    (e : ℤ) (x : ActualTensor D hu) :
    nativeNeutralCoefficient D hu d e x =
      ∑ shift ∈ (Corr D 0 (monomial d 1)).support,
        (polynomialField D hu 0 ((Corr D 0 (monomial d 1)) shift)).coeff
          (e + 2 * (shift : ℤ)) x := by
  rw [nativeNeutralCoefficient_source]
  change coefficientAt D hu e x
      ((Finsupp.lsum ℂ (fun shift : ℕ =>
        (shiftField D hu shift).comp (polynomialField D hu 0)))
        (Corr D 0 (monomial d 1))) = _
  rw [Finsupp.lsum_apply]
  simp only [Finsupp.sum, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro shift hshift
  exact LinearMap.congr_fun (shiftField_coefficient_public D hu shift
    (polynomialField D hu 0 ((Corr D 0 (monomial d 1)) shift)) e) x

private theorem polynomialField_expansion
    (D : LatticeData) (hu : IsUnit D.G.det) (p : Oscillator D) :
    polynomialField D hu 0 p =
      ∑ monomial ∈ p.support,
        p.coeff monomial •
          wordField D hu (chargedField D hu 0) (occurrences D monomial) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro monomial hmonomial
  have hmono : MvPolynomial.monomial monomial (p.coeff monomial) =
      p.coeff monomial • MvPolynomial.monomial monomial (1 : ℂ) := by
    simp [smul_monomial]
  rw [hmono, map_smul, polynomialField_monomial_public]

/-- The native coefficient is a finite sum of actual normal word coefficients,
with the literal Corr shift and the pointwise finite mode sum retained. -/
theorem nativeNeutralCoefficient_native_expansion
    (D : LatticeData) (hu : IsUnit D.G.det) (d : Index D →₀ ℕ)
    (e : ℤ) (x : ActualTensor D hu) :
    nativeNeutralCoefficient D hu d e x =
      ∑ shift ∈ (Corr D 0 (MvPolynomial.monomial d 1)).support,
        ∑ monomial ∈ ((Corr D 0 (MvPolynomial.monomial d 1)) shift).support,
          ((Corr D 0 (MvPolynomial.monomial d 1)) shift).coeff monomial •
            ∑ᶠ modes : ModeTuple D (occurrences D monomial),
              flatTerm D hu (chargedField D hu 0) (occurrences D monomial)
                (e + 2 * (shift : ℤ)) x modes := by
  rw [nativeNeutralCoefficient_shift_expansion]
  apply Finset.sum_congr rfl
  intro shift hshift
  rw [polynomialField_expansion D hu
    ((Corr D 0 (MvPolynomial.monomial d 1)) shift)]
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro monomial hmonomial
  have hw := wordField_coefficient D hu (chargedField D hu 0)
    (occurrences D monomial) (e + 2 * (shift : ℤ)) x
  change ((Corr D 0 (MvPolynomial.monomial d 1)) shift).coeff monomial •
      ((wordField D hu (chargedField D hu 0) (occurrences D monomial)).coeff
        (e + 2 * (shift : ℤ)) x) = _
  exact congrArg (fun value =>
    ((Corr D 0 (MvPolynomial.monomial d 1)) shift).coeff monomial • value) hw

/-! The following bookkeeping is on the actual mode tuples appearing in the
native pointwise `flatTerm` sum.  It records the output and input frequency
occupations separately, so the colour mixing in `G` never changes the finite
mode projection. -/

def nativeSourceEnergy (D : LatticeData) (d : Index D →₀ ℕ) : ℤ :=
  (Finsupp.weight (sourceWeight D) d : ℤ)

def nativeTwistedDoubleEnergy (D : LatticeData) (h : Index D →₀ ℕ) : ℤ :=
  h.sum (fun index multiplicity =>
    (multiplicity : ℤ) * (2 * (index.2 : ℤ) + 1))

def nativeNegativeOccupation (D : LatticeData) :
    (word : List (Index D)) → ModeTuple D word → Index D →₀ ℕ
  | [], _ => 0
  | index :: tail, modes =>
      (if modes.1 < 0 then
        Finsupp.single (index.1, (-modes.1 - 1).toNat) 1 else 0) +
        nativeNegativeOccupation D tail modes.2

def nativePositiveOccupation (D : LatticeData) :
    (word : List (Index D)) → ModeTuple D word → Index D →₀ ℕ
  | [], _ => 0
  | index :: tail, modes =>
      (if 0 ≤ modes.1 then
        Finsupp.single (index.1, modes.1.toNat) 1 else 0) +
        nativePositiveOccupation D tail modes.2

theorem nativeTwistedDoubleEnergy_add (D : LatticeData)
    (first second : Index D →₀ ℕ) :
    nativeTwistedDoubleEnergy D (first + second) =
      nativeTwistedDoubleEnergy D first + nativeTwistedDoubleEnergy D second := by
  classical
  simp only [nativeTwistedDoubleEnergy]
  rw [Finsupp.sum_add_index (by simp) (by intros; push_cast; ring)]

theorem nativeTwistedDoubleEnergy_single (D : LatticeData)
    (index : Index D) (multiplicity : ℕ) :
    nativeTwistedDoubleEnergy D (Finsupp.single index multiplicity) =
      (multiplicity : ℤ) * (2 * (index.2 : ℤ) + 1) := by
  classical
  simp [nativeTwistedDoubleEnergy]

theorem native_mode_energy_balance
    (D : LatticeData) (word : List (Index D))
    (modes : ModeTuple D word) :
    nativeTwistedDoubleEnergy D (nativeNegativeOccupation D word modes) -
        nativeTwistedDoubleEnergy D (nativePositiveOccupation D word modes) =
      -(2 * modeSum D word modes + (word.length : ℤ)) := by
  induction word with
  | nil =>
      cases modes
      simp [nativeNegativeOccupation, nativePositiveOccupation, modeSum]
  | cons index tail ih =>
      rcases modes with ⟨mode, modes⟩
      by_cases negative : mode < 0
      ·
        simp only [nativeNegativeOccupation, nativePositiveOccupation, modeSum,
          List.length_cons, if_pos negative, if_neg (not_le_of_gt negative),
          nativeTwistedDoubleEnergy_add, nativeTwistedDoubleEnergy_single]
        have hzero : nativeTwistedDoubleEnergy D (0 : Index D →₀ ℕ) = 0 := by
          simp [nativeTwistedDoubleEnergy]
        rw [hzero]
        have nonnegative : 0 ≤ -mode - 1 := by omega
        rw [Int.toNat_of_nonneg nonnegative]
        have htail := ih modes
        simp only [zero_add, add_zero] at *
        push_cast at *
        linear_combination htail
      · have nonnegative : 0 ≤ mode := by omega
        simp only [nativeNegativeOccupation, nativePositiveOccupation, modeSum,
          List.length_cons, if_neg negative, if_pos nonnegative,
          nativeTwistedDoubleEnergy_add, nativeTwistedDoubleEnergy_single]
        have hzero : nativeTwistedDoubleEnergy D (0 : Index D →₀ ℕ) = 0 := by
          simp [nativeTwistedDoubleEnergy]
        rw [hzero]
        rw [Int.toNat_of_nonneg nonnegative]
        have htail := ih modes
        simp only [zero_add, add_zero] at *
        push_cast at *
        linear_combination htail

theorem native_jetShift_wordWeight
    (D : LatticeData) (word : List (Index D)) :
    jetShift D word = 2 * (wordWeight D word : ℤ) + (word.length : ℤ) := by
  induction word with
  | nil => simp [jetShift, wordWeight]
  | cons index tail ih =>
      simp only [jetShift, wordWeight, sourceWeight, List.map_cons, List.sum_cons,
        List.length_cons, ih]
      push_cast
      ring

theorem nativeNeutralCoefficient_term_selector
    (D : LatticeData) (hu : IsUnit D.G.det)
    (monomial : Index D →₀ ℕ) (shift e : ℤ)
    (x : ActualTensor D hu)
    (modes : ModeTuple D (occurrences D monomial))
    (nonzero : flatTerm D hu (chargedField D hu 0) (occurrences D monomial)
      e x modes ≠ 0) :
    e + 2 * modeSum D (occurrences D monomial) modes +
        jetShift D (occurrences D monomial) = 0 := by
  have identity := current_charged_zero_identity D hu
  rw [identity] at nonzero
  rw [flatTerm, flatCoefficient_neutral_identity] at nonzero
  by_contra hne
  simp [hne] at nonzero

theorem nativeNeutralCoefficient_exponent_regrouping
    (D : LatticeData) (hu : IsUnit D.G.det)
    (d monomial : Index D →₀ ℕ) (shift : ℕ) (e : ℤ)
    (x : ActualTensor D hu)
    (modes : ModeTuple D (occurrences D monomial))
    (hshift : shift ∈ (Corr D 0 (MvPolynomial.monomial d 1)).support)
    (hmonomial : ((Corr D 0 (MvPolynomial.monomial d 1)) shift).coeff monomial ≠ 0)
    (hterm : flatTerm D hu (chargedField D hu 0) (occurrences D monomial)
      (e + 2 * (shift : ℤ)) x modes ≠ 0) :
    e = nativeTwistedDoubleEnergy D
        (nativeNegativeOccupation D (occurrences D monomial) modes) -
      nativeTwistedDoubleEnergy D
        (nativePositiveOccupation D (occurrences D monomial) modes) -
      2 * nativeSourceEnergy D d := by
  have hb := D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance.Corr_coefficient_bidegree
    D 0 (MvPolynomial.monomial d 1)
      (Finsupp.weight (sourceWeight D) d)
      (isWeightedHomogeneous_monomial (sourceWeight D) d (1 : ℂ) rfl)
      shift monomial hmonomial
  have hs := nativeNeutralCoefficient_term_selector D hu monomial
    (shift : ℤ) (e + 2 * (shift : ℤ)) x modes hterm
  have hbalance := native_mode_energy_balance D (occurrences D monomial) modes
  have hword := wordWeight_occurrences D monomial
  have hword' : wordWeight D (occurrences D monomial) =
      Finsupp.weight (sourceWeight D) monomial := by
    simpa [occurrences, LatticeAllStateField.occurrences] using hword
  have hsource : nativeSourceEnergy D d =
      (shift : ℤ) + (Finsupp.weight (sourceWeight D) monomial : ℤ) := by
    dsimp [nativeSourceEnergy]
    have hc := congrArg (fun value : ℕ => (value : ℤ)) hb
    push_cast at hc
    omega
  have hjet := native_jetShift_wordWeight D (occurrences D monomial)
  rw [hjet, hword'] at hs
  linear_combination hs - hbalance + 2 * hsource

def nativeNeutralModeProjection
    (D : LatticeData) (output input : Index D →₀ ℕ) : Finset ℤ :=
  (output.support.image (fun index => -(index.2 : ℤ) - 1)) ∪
    (input.support.image (fun index => (index.2 : ℤ)))

def nativeModeBox (D : LatticeData) (B : Finset ℤ) :
    (word : List (Index D)) → Finset (ModeTuple D word)
  | [] => {()}
  | _ :: tail => B.product (nativeModeBox D B tail)

theorem nativeModeBox_mem
    (D : LatticeData) (B : Finset ℤ) (word : List (Index D))
    (modes : ModeTuple D word) :
    modes ∈ nativeModeBox D B word ↔
      allModes D (fun mode => mode ∈ B) word modes := by
  induction word with
  | nil =>
      cases modes
      simp [nativeModeBox, allModes]
  | cons index tail ih =>
      rcases modes with ⟨mode, modes⟩
      simp [nativeModeBox, allModes, ih]

theorem nativeNeutralCoefficient_projected_mode_sum
    (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (e : ℤ) (x : ActualTensor D hu)
    (B : Finset ℤ)
    (support_condition : ∀ modes,
      flatTerm D hu (chargedField D hu 0) word e x modes ≠ 0 →
        allModes D (fun mode => mode ∈ B) word modes) :
    (∑ᶠ modes : ModeTuple D word,
      flatTerm D hu (chargedField D hu 0) word e x modes) =
        ∑ modes ∈ nativeModeBox D B word,
        flatTerm D hu (chargedField D hu 0) word e x modes := by
  apply finsum_eq_sum_of_support_subset
  intro modes hmode
  exact (nativeModeBox_mem D B word modes).mpr
    (support_condition modes hmode)

theorem nativeNeutralCoefficient_frequency_projected_mode_sum
    (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (e : ℤ) (x : ActualTensor D hu)
    (output input : Index D →₀ ℕ)
    (support_condition : ∀ modes,
      flatTerm D hu (chargedField D hu 0) word e x modes ≠ 0 →
        allModes D
          (fun mode => mode ∈ nativeNeutralModeProjection D output input)
          word modes) :
    (∑ᶠ modes : ModeTuple D word,
      flatTerm D hu (chargedField D hu 0) word e x modes) =
        ∑ modes ∈ nativeModeBox D
          (nativeNeutralModeProjection D output input) word,
          flatTerm D hu (chargedField D hu 0) word e x modes := by
  exact nativeNeutralCoefficient_projected_mode_sum D hu word e x
    (nativeNeutralModeProjection D output input) support_condition

/-! The four raw finite bilinear pieces are recorded directly in the native
coordinates.  These are coefficient symbols, rather than a replacement
field: the corrected field and its finite mode expansion above remain the
source of every coefficient. -/

def nativeSourceSourceKernel (D : LatticeData) (T : ℂ)
    (a b : Index D) : ℂ :=
  pairScalar (sourceWeight D a) (sourceWeight D b) *
    (D.G a.1 b.1 : ℂ) *
      T ^ (-2 * (sourceWeight D a : ℤ) - 2 * (sourceWeight D b : ℤ))

theorem nativeSourceSourceKernel_eq_covariance
    (D : LatticeData) (T : ℂ) (hT : T ≠ 0) (a b : Index D) :
    nativeSourceSourceKernel D T a b =
      covariance D (T ^ (-2 : ℤ)) a b := by
  unfold nativeSourceSourceKernel covariance
  rw [← zpow_natCast, ← zpow_mul]
  congr 3
  simp only [sourceWeight, Nat.cast_add, Nat.cast_one]
  push_cast
  ring

def nativeSourceOutputKernel (D : LatticeData) (T : ℂ)
    (a b : Index D) : ℂ :=
  if a.1 = b.1 then
    jetScalar a.2 (-(b.2 : ℤ) - 1) *
      T ^ (2 * (b.2 : ℤ) - 2 * (sourceWeight D a : ℤ) + 1)
  else 0

def nativeSourceInputKernel (D : LatticeData) (T : ℂ)
    (a b : Index D) : ℂ :=
  LatticeHalfFock.frequency (b.2 : ℤ) * (D.G a.1 b.1 : ℂ) *
    jetScalar a.2 (b.2 : ℤ) *
      T ^ (-2 * (b.2 : ℤ) - 2 * (sourceWeight D a : ℤ) - 1)

def nativeIdentityPropagationKernel (D : LatticeData)
    (a b : Index D) : ℂ :=
  if a = b then 1 else 0

/-- The explicit raw coefficient kernel.  Its four summands are source-source,
source-output, source-input, and identity propagation, in that order. -/
def nativeNeutralRawKernel (D : LatticeData) (T : ℂ)
    (source input output : Index D →₀ ℂ) : ℂ :=
  (1 / 2 : ℂ) *
      ∑ a ∈ source.support, ∑ b ∈ source.support,
        source a * source b * nativeSourceSourceKernel D T a b +
    ∑ a ∈ source.support, ∑ b ∈ output.support,
      source a * output b * nativeSourceOutputKernel D T a b +
    ∑ a ∈ source.support, ∑ b ∈ input.support,
      source a * input b * nativeSourceInputKernel D T a b +
    ∑ b ∈ input.support, input b * output b *
      nativeIdentityPropagationKernel D b b

theorem nativeNeutralRawKernel_components (D : LatticeData) (T : ℂ)
    (source input output : Index D →₀ ℂ) :
    nativeNeutralRawKernel D T source input output =
      ((1 / 2 : ℂ) *
        ∑ a ∈ source.support, ∑ b ∈ source.support,
          source a * source b * nativeSourceSourceKernel D T a b) +
      (∑ a ∈ source.support, ∑ b ∈ output.support,
        source a * output b * nativeSourceOutputKernel D T a b) +
      (∑ a ∈ source.support, ∑ b ∈ input.support,
        source a * input b * nativeSourceInputKernel D T a b) +
      (∑ b ∈ input.support, input b * output b *
        nativeIdentityPropagationKernel D b b) := by
  rfl

/- The finite Wick readout is stated with an arbitrary finite labelled source
family.  Taking each c i to a coordinate linear form gives the displayed
source-source piece above; the theorem keeps the exact factorial occupation
weight and does not collapse repeated labels. -/
theorem nativeNeutralFiniteWickIdentity
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂ) (c : I → Index D →₀ ℂ)
    (d : I →₀ ℕ) :
    sourceVacuum D (T ^ (-2 : ℤ))
        (∏ i, linearForm D (c i) ^ d i) =
      (FactorialFockMetric.weight d : ℂ) *
        gaussianCoefficient (covarianceMatrix D (T ^ (-2 : ℤ)) c) d := by
  exact sourceVacuum_linearForms D (T ^ (-2 : ℤ)) c d

#print axioms nativeNeutralCoefficient_source
#print axioms nativeNeutralCorrection_gaussian
#print axioms nativeNeutralCoefficient_shift_expansion
#print axioms nativeNeutralCoefficient_native_expansion

end D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
