/- GID: D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual neutral-field finite mode support, energy selection and raw Laurent expansion. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
import D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal

/-!
The actual neutral corrected field has a common finite mode box after output
projection. Its coefficients are finite scalar Laurent entries acting by the
identity on arbitrary ground tensors. Literal raw mixed-mode operators give
the normal expansion; evaluating the original correction lift constructs its
source insertion law. The coefficient module consumes these constructions in
the full raw three-leg Gaussian identity.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct


namespace D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient

open MvPolynomial
open LatticeGeneratingFieldLocality
open LatticeHalfFockFockNormalField
open LatticeHalfFock
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField
open LatticeHalfFockCorrectedConformal
open LatticeHalfFockChargedTensorCoefficients
open HalfFockSpectralFiberSource
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

/- Output extraction retains the entire ground vector. -/
def nativeOutputProjection (D : LatticeData) (hu : IsUnit D.G.det)
    (output : Index D →₀ ℕ) : ActualTensor D hu →ₗ[ℂ] ActualGround D hu :=
  (TensorProduct.lid ℂ (ActualGround D hu)).toLinearMap.comp
    (TensorProduct.map (lcoeff ℂ output) LinearMap.id)

@[simp] private theorem nativeOutputProjection_tmul
    (D : LatticeData) (hu : IsUnit D.G.det) (output : Index D →₀ ℕ)
    (p : Oscillator D) (g : ActualGround D hu) :
    nativeOutputProjection D hu output (p ⊗ₜ[ℂ] g) = p.coeff output • g := by
  simp [nativeOutputProjection]

private def creationPolynomial (D : LatticeData) :
    (word : List (Index D)) → ModeTuple D word → Oscillator D
  | [], _ => 1
  | a :: w, m => if m.1 < 0 then
      (jetScalar a.2 m.1 • X (a.1, (-m.1 - 1).toNat)) * creationPolynomial D w m.2
    else creationPolynomial D w m.2

private def creationScalar (D : LatticeData) :
    (word : List (Index D)) → ModeTuple D word → ℂ
  | [], _ => 1
  | a :: w, m => if m.1 < 0 then jetScalar a.2 m.1 * creationScalar D w m.2
    else creationScalar D w m.2

private def rightPolynomial (D : LatticeData) :
    (word : List (Index D)) → ModeTuple D word → Module.End ℂ (Oscillator D)
  | [], _ => 1
  | a :: w, m => if m.1 < 0 then rightPolynomial D w m.2
    else rightPolynomial D w m.2 * (jetScalar a.2 m.1 • current D a.1 m.1)

private theorem creationPolynomial_monomial (D : LatticeData)
    (word : List (Index D)) (m : ModeTuple D word) :
    creationPolynomial D word m =
      creationScalar D word m • monomial (nativeNegativeOccupation D word m) 1 := by
  induction word with
  | nil => simp [creationPolynomial, creationScalar, nativeNegativeOccupation]
  | cons a w ih =>
    simp only [creationPolynomial, creationScalar, nativeNegativeOccupation]
    split_ifs with h
    · rw [ih]
      simp [X, smul_monomial, monomial_mul_monomial, smul_eq_mul]
    · simpa using ih m.2

private theorem leftAction_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (m : ModeTuple D word)
    (p : Oscillator D) (g : ActualGround D hu) :
    leftAction D hu word m (p ⊗ₜ[ℂ] g) =
      (creationPolynomial D word m * p) ⊗ₜ[ℂ] g := by
  induction word with
  | nil => simp [leftAction, creationPolynomial]
  | cons a w ih =>
    simp only [leftAction, creationPolynomial]
    split_ifs with h
    · simp only [Module.End.mul_apply, ih, jetCurrent, LinearMap.smul_apply,
        tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
        current, if_pos h, LinearMap.mulLeft_apply]
      rw [TensorProduct.smul_tmul']
      congr 1
      simp [smul_mul_assoc, mul_assoc]
    · exact ih m.2

private theorem rightAction_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (m : ModeTuple D word)
    (p : Oscillator D) (g : ActualGround D hu) :
    rightAction D hu word m (p ⊗ₜ[ℂ] g) =
      rightPolynomial D word m p ⊗ₜ[ℂ] g := by
  induction word generalizing p with
  | nil => rfl
  | cons a w ih =>
    simp only [rightAction, rightPolynomial]
    split_ifs with h
    · exact ih m.2 p
    · simp only [Module.End.mul_apply, jetCurrent, LinearMap.smul_apply,
        tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.smul_tmul']
      exact ih m.2 _

private theorem flatTerm_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (m : ModeTuple D word) (e : ℤ)
    (p : Oscillator D) (g : ActualGround D hu) :
    flatTerm D hu (chargedField D hu 0) word e (p ⊗ₜ[ℂ] g) m =
      if e + 2 * modeSum D word m + jetShift D word = 0 then
        (creationPolynomial D word m * rightPolynomial D word m p) ⊗ₜ[ℂ] g
      else 0 := by
  rw [current_charged_zero_identity, flatTerm, flatCoefficient_neutral_identity]
  split_ifs
  · rw [Module.End.mul_apply, rightAction_tmul, leftAction_tmul]
  · rfl

private theorem current_monomial_frequency_vanish (D : LatticeData)
    (input : Index D →₀ ℕ) (i : Fin D.rank) (m : ℤ) (hm : 0 ≤ m)
    (hout : m ∉ input.support.image (fun a => (a.2 : ℤ))) :
    current D i m (monomial input 1) = 0 := by
  have hz (j : Fin D.rank) : input (j, m.toNat) = 0 := by
    by_contra hn
    apply hout
    exact Finset.mem_image.mpr ⟨(j, m.toNat), Finsupp.mem_support_iff.mpr hn,
      Int.toNat_of_nonneg hm⟩
  simp [current, not_lt.mpr hm, LatticeActualAnnihilation.annihilate,
    LatticeSugawaraCurrents.weightedPartial, LinearMap.sum_apply, hz]

private theorem positive_current_commute (D : LatticeData)
    (i j : Fin D.rank) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (p : Oscillator D) :
    current D i m (current D j n p) = current D j n (current D i m p) := by
  exact sub_eq_zero.mp (by simpa [show m + n + 1 ≠ 0 by omega] using
    current_heisenberg_apply D i j m n p)

private theorem rightPolynomial_positive_support (D : LatticeData)
    (S : Finset ℤ) (word : List (Index D)) (m : ModeTuple D word)
    (p : Oscillator D)
    (hp : ∀ i n, 0 ≤ n → n ∉ S → current D i n p = 0)
    (hn : rightPolynomial D word m p ≠ 0) :
    allModes D (fun n => 0 ≤ n → n ∈ S) word m := by
  induction word generalizing p with
  | nil => trivial
  | cons a w ih =>
    by_cases h : m.1 < 0
    · exact ⟨by omega, ih m.2 p hp (by simpa [rightPolynomial, h] using hn)⟩
    · have hm : 0 ≤ m.1 := by omega
      have htail : rightPolynomial D w m.2 (jetScalar a.2 m.1 • current D a.1 m.1 p) ≠ 0 := by
        simpa [rightPolynomial, h] using hn
      refine ⟨?_, ih m.2 _ ?_ htail⟩
      · intro _
        by_contra outside
        exact htail (by simp [hp a.1 m.1 hm outside])
      · intro i n hn outside
        simp only [map_smul]
        rw [positive_current_commute D i a.1 n m.1 hn hm, hp i n hn outside, map_zero,
          smul_zero]

private theorem negative_modes_support (D : LatticeData)
    (output : Index D →₀ ℕ) (word : List (Index D)) (m : ModeTuple D word)
    (hle : nativeNegativeOccupation D word m ≤ output) :
    allModes D (fun n => n < 0 →
      n ∈ output.support.image (fun a => -(a.2 : ℤ) - 1)) word m := by
  induction word with
  | nil => trivial
  | cons a w ih =>
    have ht : nativeNegativeOccupation D w m.2 ≤ output := by
      exact le_trans (le_add_left le_rfl) hle
    refine ⟨?_, ih m.2 ht⟩
    intro h
    have hs : Finsupp.single (a.1, (-m.1 - 1).toNat) 1 ≤ output := by
      apply le_trans _ hle
      simp only [nativeNegativeOccupation, if_pos h]
      exact le_add_right le_rfl
    have hn : output (a.1, (-m.1 - 1).toNat) ≠ 0 := by
      have hh := (Finsupp.single_le_iff.mp hs)
      omega
    refine Finset.mem_image.mpr ⟨(a.1, (-m.1 - 1).toNat),
      Finsupp.mem_support_iff.mpr hn, ?_⟩
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -m.1 - 1)]
    omega

theorem normalPolynomial_projected_support (D : LatticeData)
    (word : List (Index D)) (input output : Index D →₀ ℕ) (m : ModeTuple D word)
    (hc : (creationPolynomial D word m * rightPolynomial D word m
      (monomial input 1)).coeff output ≠ 0) :
    allModes D (fun n => n ∈ nativeNeutralModeProjection D output input) word m := by
  have hr : rightPolynomial D word m (monomial input 1) ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hle : nativeNegativeOccupation D word m ≤ output := by
    by_contra hh
    rw [creationPolynomial_monomial, smul_mul_assoc, coeff_smul,
      coeff_monomial_mul', if_neg hh, smul_zero] at hc
    exact hc rfl
  have hp := rightPolynomial_positive_support D
    (input.support.image (fun a => (a.2 : ℤ))) word m (monomial input 1)
    (current_monomial_frequency_vanish D input) hr
  have hm := negative_modes_support D output word m hle
  have combine (w : List (Index D)) : ∀ m : ModeTuple D w,
      allModes D (fun n => 0 ≤ n →
        n ∈ input.support.image (fun a => (a.2 : ℤ))) w m →
      allModes D (fun n => n < 0 →
        n ∈ output.support.image (fun a => -(a.2 : ℤ) - 1)) w m →
      allModes D (fun n => n ∈ nativeNeutralModeProjection D output input) w m := by
    induction w with
    | nil => intros; trivial
    | cons a w ih =>
      intro m hp hm
      refine ⟨?_, ih m.2 hp.2 hm.2⟩
      by_cases h : m.1 < 0
      · exact Finset.mem_union_left _ (hm.1 h)
      · exact Finset.mem_union_right _ (hp.1 (by omega))
  exact combine word m hp hm

/-- Support is proved only after the actual output projection. Creation modes
outside the output frequency vanish there; annihilation modes outside the input
frequency vanish on the input, including arbitrary Gram colour mixing. -/
theorem nativeNeutralCoefficient_projected_support
    (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (e : ℤ) (input output : Index D →₀ ℕ)
    (g : ActualGround D hu) (m : ModeTuple D word)
    (hn : nativeOutputProjection D hu output
      (flatTerm D hu (chargedField D hu 0) word e
        (monomial input 1 ⊗ₜ[ℂ] g) m) ≠ 0) :
    allModes D (fun n => n ∈ nativeNeutralModeProjection D output input) word m := by
  rw [flatTerm_tmul] at hn
  split_ifs at hn with he
  · rw [nativeOutputProjection_tmul] at hn
    have hc : (creationPolynomial D word m * rightPolynomial D word m
        (monomial input 1)).coeff output ≠ 0 := by
      intro hz
      exact hn (by rw [hz, zero_smul])
    exact normalPolynomial_projected_support D word input output m hc
  · exact (hn (map_zero _)).elim

/-- The common finite mode set is independent of the Hahn exponent. The
projection commutes with the native pointwise finsum by its actual finite support. -/
theorem nativeNeutralCoefficient_frequency_projected_mode_sum
    (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (e : ℤ) (input output : Index D →₀ ℕ)
    (g : ActualGround D hu) :
    nativeOutputProjection D hu output
      ((wordField D hu (chargedField D hu 0) word).coeff e
        (monomial input 1 ⊗ₜ[ℂ] g)) =
      ∑ m ∈ nativeModeBox D (nativeNeutralModeProjection D output input) word,
        nativeOutputProjection D hu output
          (flatTerm D hu (chargedField D hu 0) word e
            (monomial input 1 ⊗ₜ[ℂ] g) m) := by
  rw [wordField_coefficient,
    map_finsum _ (flatTerm_finite D hu (chargedField D hu 0) word e _)]
  apply finsum_eq_sum_of_support_subset
  intro m hm
  exact (nativeModeBox_mem D _ word m).mpr
    (nativeNeutralCoefficient_projected_support D hu word e input output g m hm)

private theorem neutralSource_grade (D : LatticeData) (d : Index D →₀ ℕ) :
    neutralSource D d ∈ LatticePositiveEnergy.grade D (nativeSourceEnergy D d) := by
  rw [LatticePositiveEnergy.grade_eq_span]
  apply Submodule.subset_span
  refine ⟨(0, d), ?_, ?_⟩
  · simp [LatticePositiveEnergy.energy, LatticePositiveEnergy.chargeEnergy,
      LatticeGeneratingFieldLocality.bilinear, nativeSourceEnergy,
      LatticePositiveEnergy.oscillatorEnergy, sourceWeight] <;> rfl
  · simp [LatticePositiveEnergy.carrierBasis_apply, neutralSource]

private theorem monomial_tensor_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (d : Index D →₀ ℕ) (g : ActualGround D hu) :
    LatticeHalfFockGradedTrace.actualTensorL0 D hu (monomial d 1 ⊗ₜ[ℂ] g) =
      ((D.rank : ℂ) / 16 + (LatticeHalfFockGradedTrace.oddWeight D d : ℂ) / 2) •
        (monomial d 1 ⊗ₜ[ℂ] g) := by
  simp only [LatticeHalfFockGradedTrace.actualTensorL0, tensorL, tensorEnd,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [L_zero_monomial_coeff D (actualInverse D)
    (actualInverse_left D hu) (actualInverse_right D hu) d 1,
    LatticeHalfFockGradedTrace.oddWeight_eq_two_energy, TensorProduct.smul_tmul']

private theorem outputProjection_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (output : Index D →₀ ℕ) (x : ActualTensor D hu) :
    nativeOutputProjection D hu output (LatticeHalfFockGradedTrace.actualTensorL0 D hu x) =
      ((D.rank : ℂ) / 16 + (LatticeHalfFockGradedTrace.oddWeight D output : ℂ) / 2) •
        nativeOutputProjection D hu output x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy, smul_add]
  | tmul p g =>
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq => simp [TensorProduct.add_tmul, map_add, hp, hq, smul_add]
    | monomial d c =>
      have hm : (monomial d c : Oscillator D) = c • monomial d 1 := by
        simp [smul_monomial]
      rw [hm, ← TensorProduct.smul_tmul', map_smul, monomial_tensor_energy,
        map_smul, map_smul]
      by_cases h : d = output
      · subst d
        simp [smul_smul, mul_comm]
      · simp [coeff_monomial, h, Ne.symm h]

/-- The entire projected corrected entry has one Laurent exponent. This uses
the existing full-field energy covariance, without any Hahn evaluation. -/
theorem nativeNeutralCoefficient_output_energy_selection
    (D : LatticeData) (hu : IsUnit D.G.det)
    (d input output : Index D →₀ ℕ) (g : ActualGround D hu) (e : ℤ)
    (hne : e ≠ (LatticeHalfFockGradedTrace.oddWeight D output : ℤ) -
      (LatticeHalfFockGradedTrace.oddWeight D input : ℤ) - 2 * nativeSourceEnergy D d) :
    nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu d e (monomial input 1 ⊗ₜ[ℂ] g)) = 0 := by
  have he := ActualEnergyCovariance.correctedField_signed_output D hu
    (nativeSourceEnergy D d) (LatticeHalfFockGradedTrace.oddWeight D input : ℤ) e
    (neutralSource D d) (neutralSource_grade D d) _ (by
      simpa using monomial_tensor_energy D hu input g)
  have hp := congrArg (nativeOutputProjection D hu output) he
  rw [outputProjection_energy, map_smul] at hp
  change _ • nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu d e (monomial input 1 ⊗ₜ[ℂ] g)) =
    _ • nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu d e (monomial input 1 ⊗ₜ[ℂ] g)) at hp
  have hc : ((D.rank : ℂ) / 16 + (LatticeHalfFockGradedTrace.oddWeight D output : ℂ) / 2) ≠
      ((D.rank : ℂ) / 16 +
        (((LatticeHalfFockGradedTrace.oddWeight D input : ℤ) + e +
          2 * nativeSourceEnergy D d : ℤ) : ℂ) / 2) := by
    intro hz
    apply hne
    have hz' : ((e : ℤ) : ℂ) =
        (LatticeHalfFockGradedTrace.oddWeight D output : ℂ) -
        (LatticeHalfFockGradedTrace.oddWeight D input : ℂ) -
        2 * (nativeSourceEnergy D d : ℂ) := by
      push_cast at hz
      linear_combination -2 * hz
    exact_mod_cast hz'
  exact ((smul_eq_zero).mp (by rw [sub_smul, hp, sub_self])).resolve_left
    (sub_ne_zero.mpr hc)

/-- A finite expression for the actual full corrected coefficient, after
output projection and with the original ground tensor unchanged. -/
theorem nativeNeutralCoefficient_finite_projected_expansion
    (D : LatticeData) (hu : IsUnit D.G.det) (d input output : Index D →₀ ℕ)
    (e : ℤ) (g : ActualGround D hu) :
    nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu d e (monomial input 1 ⊗ₜ[ℂ] g)) =
      ∑ shift ∈ (Corr D 0 (monomial d 1)).support,
        ∑ mon ∈ ((Corr D 0 (monomial d 1)) shift).support,
          ((Corr D 0 (monomial d 1)) shift).coeff mon •
            ∑ m ∈ nativeModeBox D (nativeNeutralModeProjection D output input)
                (occurrences D mon),
              if e + 2 * (shift : ℤ) + 2 * modeSum D (occurrences D mon) m +
                  jetShift D (occurrences D mon) = 0 then
                ((creationPolynomial D (occurrences D mon) m *
                  rightPolynomial D (occurrences D mon) m (monomial input 1)).coeff output) • g
              else 0 := by
  rw [nativeNeutralCoefficient_native_expansion]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro shift hs
  apply Finset.sum_congr rfl
  intro mon hm
  congr 1
  rw [← wordField_coefficient]
  rw [nativeNeutralCoefficient_frequency_projected_mode_sum]
  apply Finset.sum_congr rfl
  intro m hmem
  rw [flatTerm_tmul]
  split_ifs <;> simp

/-- Finite scalar Laurent entries obtained from the actual Corr and normal
actions. Their exponent is collected before scalar evaluation. -/
def nativeNeutralLaurentCoefficients (D : LatticeData)
    (d input output : Index D →₀ ℕ) : ℤ →₀ ℂ :=
  ∑ shift ∈ (Corr D 0 (monomial d 1)).support,
    ∑ mon ∈ ((Corr D 0 (monomial d 1)) shift).support,
      ∑ m ∈ nativeModeBox D (nativeNeutralModeProjection D output input) (occurrences D mon),
        Finsupp.single
          (-2 * (shift : ℤ) - 2 * modeSum D (occurrences D mon) m -
            jetShift D (occurrences D mon))
          (((Corr D 0 (monomial d 1)) shift).coeff mon *
            (creationPolynomial D (occurrences D mon) m *
              rightPolynomial D (occurrences D mon) m (monomial input 1)).coeff output)

/-- Every coefficient of the genuine full corrected field is a scalar entry
of one finite Laurent polynomial tensored with the identity on the whole ground
module. No ground vacuum or positivity assumption is used. -/
theorem nativeNeutralCoefficient_eq_laurent_coefficients
    (D : LatticeData) (hu : IsUnit D.G.det) (d input output : Index D →₀ ℕ)
    (e : ℤ) (g : ActualGround D hu) :
    nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu d e (monomial input 1 ⊗ₜ[ℂ] g)) =
      nativeNeutralLaurentCoefficients D d input output e • g := by
  rw [nativeNeutralCoefficient_finite_projected_expansion]
  simp only [nativeNeutralLaurentCoefficients, Finsupp.finsetSum_apply, Finset.sum_smul,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro shift hs
  apply Finset.sum_congr rfl
  intro mon hm
  apply Finset.sum_congr rfl
  intro m hmem
  have he : (e + 2 * (shift : ℤ) + 2 * modeSum D (occurrences D mon) m +
      jetShift D (occurrences D mon) = 0) ↔
      -2 * (shift : ℤ) - 2 * modeSum D (occurrences D mon) m -
        jetShift D (occurrences D mon) = e := by omega
  simp only [he, Finsupp.single_apply]
  split_ifs <;> simp [smul_smul]

/-- Evaluation is defined only on the proved finite scalar Laurent entries. -/
def nativeNeutralLaurentEntry (D : LatticeData) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) : ℂ :=
  (nativeNeutralLaurentCoefficients D d input output).sum (fun e c => c * (T : ℂ) ^ e)

/-- Scalar evaluation of the finite actual entries retains the full ground
identity. This is a finite sum, with no evaluation map on Hahn series. -/
theorem nativeNeutralLaurentEntry_ground_identity
    (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (g : ActualGround D hu) :
    nativeNeutralLaurentEntry D T d input output • g =
      ∑ e ∈ (nativeNeutralLaurentCoefficients D d input output).support,
        (T : ℂ) ^ e • nativeOutputProjection D hu output
          (nativeNeutralCoefficient D hu d e (monomial input 1 ⊗ₜ[ℂ] g)) := by
  simp only [nativeNeutralLaurentEntry, Finsupp.sum, Finset.sum_smul,
    nativeNeutralCoefficient_eq_laurent_coefficients, smul_smul, mul_comm]

/-- The finite actual Laurent evaluation is the single allowed energy
coefficient, on the whole ground module. All other terms vanish by the native
full-field energy theorem. -/
theorem nativeNeutralLaurentEntry_at_energy
    (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (g : ActualGround D hu) :
    let E : ℤ := (LatticeHalfFockGradedTrace.oddWeight D output : ℤ) -
      (LatticeHalfFockGradedTrace.oddWeight D input : ℤ) - 2 * nativeSourceEnergy D d
    nativeNeutralLaurentEntry D T d input output • g =
      (T : ℂ) ^ E • nativeOutputProjection D hu output
        (nativeNeutralCoefficient D hu d E (monomial input 1 ⊗ₜ[ℂ] g)) := by
  classical
  dsimp only
  rw [nativeNeutralLaurentEntry_ground_identity]
  apply Finset.sum_eq_single
  · intro e he hne
    rw [nativeNeutralCoefficient_output_energy_selection D hu d input output g e hne,
      smul_zero]
  · intro hnot
    rw [nativeNeutralCoefficient_eq_laurent_coefficients,
      Finsupp.notMem_support_iff.mp hnot, zero_smul, smul_zero]

/-! The four raw finite bilinear pieces are recorded directly in the native
coordinates.  These are coefficient symbols, rather than a replacement
field: the corrected field and its finite mode expansion above remain the
source of every coefficient. -/

def nativeSourceSourceKernel (D : LatticeData) (T : ℂ)
    (a b : Index D) : ℂ :=
  pairScalar (sourceWeight D a) (sourceWeight D b) *
    (D.G a.1 b.1 : ℂ) *
      T ^ (-2 * (sourceWeight D a : ℤ) - 2 * (sourceWeight D b : ℤ))

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

def rawModeOperator (D : LatticeData) (T : ℂˣ)
    (a : Index D) (m : ℤ) : Module.End ℂ (Oscillator D) :=
  if m < 0 then
    nativeSourceOutputKernel D T a (a.1, (-m - 1).toNat) •
      LinearMap.mulLeft ℂ (X (a.1, (-m - 1).toNat))
  else ∑ j : Fin D.rank,
    nativeSourceInputKernel D T a (j, m.toNat) • (pderiv (j, m.toNat)).toLinearMap

theorem rawModeOperator_eq (D : LatticeData) (T : ℂˣ)
    (a : Index D) (m : ℤ) :
    rawModeOperator D T a m =
      (T : ℂ) ^ (-2 * m - 2 * (a.2 : ℤ) - 3) • (jetScalar a.2 m • current D a.1 m) := by
  by_cases h : m < 0
  · have he : 2 * (((-m - 1).toNat : ℕ) : ℤ) -
        2 * (sourceWeight D a : ℤ) + 1 = -2 * m - 2 * (a.2 : ℤ) - 3 := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -m - 1)]
      simp only [sourceWeight, Nat.cast_add, Nat.cast_one]
      ring
    have hm : -((((-m - 1).toNat : ℕ) : ℤ)) - 1 = m := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -m - 1)]
      omega
    simp only [rawModeOperator, if_pos h, nativeSourceOutputKernel, if_true,
      hm, he, current, smul_smul]
    rw [mul_comm]
  · have hm : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
    have he : -2 * m - 2 * (sourceWeight D a : ℤ) - 1 =
        -2 * m - 2 * (a.2 : ℤ) - 3 := by
      simp only [sourceWeight, Nat.cast_add, Nat.cast_one]
      ring
    simp only [rawModeOperator, if_neg h, nativeSourceInputKernel, hm, he, current,
      LatticeActualAnnihilation.annihilate, LatticeSugawaraCurrents.weightedPartial,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring

/-- The raw source/output and source/input symbols act in literal normal
order: creation on the left and annihilation on the original input. -/
def nativeRawNormalTerm (D : LatticeData) (T : ℂˣ) :
    (word : List (Index D)) → ModeTuple D word → Module.End ℂ (Oscillator D)
  | [], _ => 1
  | a :: w, m => if m.1 < 0 then
      rawModeOperator D T a m.1 * nativeRawNormalTerm D T w m.2
    else nativeRawNormalTerm D T w m.2 * rawModeOperator D T a m.1

theorem nativeRawNormalTerm_eq (D : LatticeData) (T : ℂˣ)
    (word : List (Index D)) (m : ModeTuple D word) (p : Oscillator D) :
    nativeRawNormalTerm D T word m p =
      (T : ℂ) ^ (-2 * modeSum D word m - jetShift D word) •
        (creationPolynomial D word m * rightPolynomial D word m p) := by
  induction word generalizing p with
  | nil => simp [nativeRawNormalTerm, modeSum, jetShift, creationPolynomial, rightPolynomial]
  | cons a w ih =>
    have he : -2 * modeSum D (a :: w) m - jetShift D (a :: w) =
        (-2 * m.1 - 2 * (a.2 : ℤ) - 3) +
          (-2 * modeSum D w m.2 - jetShift D w) := by
      simp only [modeSum, jetShift]
      ring
    rw [he, zpow_add₀ (Units.ne_zero T)]
    simp only [nativeRawNormalTerm, creationPolynomial, rightPolynomial]
    split_ifs with h
    · rw [Module.End.mul_apply, rawModeOperator_eq, ih]
      simp only [LinearMap.smul_apply, map_smul, current, if_pos h,
        LinearMap.mulLeft_apply, smul_mul_assoc, smul_smul]
      simp [smul_mul_assoc, smul_smul, mul_assoc, mul_comm, mul_left_comm]
    · rw [Module.End.mul_apply, ih, rawModeOperator_eq]
      simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul,
        mul_smul_comm, smul_smul]
      simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

/-- The actual full corrected-field Laurent entry is the finite Corr sum
of the raw normal-mode operators. Both mixed raw blocks are consumed here,
with arbitrary repeated source/input/output occupations and ground identity. -/
theorem nativeNeutralLaurentEntry_raw_normal_expansion
    (D : LatticeData) (T : ℂˣ) (d input output : Index D →₀ ℕ) :
    nativeNeutralLaurentEntry D T d input output =
      ∑ shift ∈ (Corr D 0 (monomial d 1)).support,
        ∑ mon ∈ ((Corr D 0 (monomial d 1)) shift).support,
          ((Corr D 0 (monomial d 1)) shift).coeff mon * (T : ℂ) ^ (-2 * (shift : ℤ)) *
            ∑ m ∈ nativeModeBox D (nativeNeutralModeProjection D output input) (occurrences D mon),
              (nativeRawNormalTerm D T (occurrences D mon) m (monomial input 1)).coeff output := by
  classical
  let ev : (ℤ →₀ ℂ) →ₗ[ℂ] ℂ :=
    Finsupp.lsum ℂ (fun e => (T : ℂ) ^ e • LinearMap.id)
  have hev (q : ℤ →₀ ℂ) : ev q = q.sum (fun e c => c * (T : ℂ) ^ e) := by
    rw [Finsupp.lsum_apply]
    apply Finset.sum_congr rfl
    intro e he
    simp [mul_comm]
  rw [nativeNeutralLaurentEntry, ← hev]
  simp only [nativeNeutralLaurentCoefficients, ev, map_sum, Finsupp.lsum_single,
    LinearMap.smul_apply, LinearMap.id_apply, nativeRawNormalTerm_eq, coeff_smul,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro shift hs
  apply Finset.sum_congr rfl
  intro mon hm
  apply Finset.sum_congr rfl
  intro m hmem
  have he : -2 * (shift : ℤ) - 2 * modeSum D (occurrences D mon) m -
        jetShift D (occurrences D mon) =
      -2 * (shift : ℤ) + (-2 * modeSum D (occurrences D mon) m -
        jetShift D (occurrences D mon)) := by ring
  rw [he, zpow_add₀ (Units.ne_zero T)]
  ring

open LatticeHalfFockCurrentCorrection
open private pairDerivation_source_partials from
  D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

def correctionEvaluation (D : LatticeData) (T : ℂˣ) :
    CorrectionPolynomial D →ₐ[ℂ] Oscillator D :=
  aeval (fun a => a.elim (C ((T : ℂ) ^ (-2 : ℤ))) X)

def correctionAt (D : LatticeData) (T : ℂˣ) :
    Oscillator D →ₗ[ℂ] Oscillator D :=
  (correctionEvaluation D T).toLinearMap.comp (correctionLift D 0)

private theorem correctionEvaluation_option (D : LatticeData) (T : ℂˣ)
    (q : CorrectionPolynomial D) :
    correctionEvaluation D T q =
      Polynomial.eval (C ((T : ℂ) ^ (-2 : ℤ))) (optionEquivLeft ℂ (Index D) q) := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [correctionEvaluation, algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p a hp =>
      simp only [map_mul, Polynomial.eval_mul, hp]
      congr 1
      cases a <;> simp [correctionEvaluation, algebraMap_eq]

theorem correctionAt_shift_sum (D : LatticeData) (T : ℂˣ)
    (p : Oscillator D) :
    correctionAt D T p =
      ∑ s ∈ (Corr D 0 p).support, (T : ℂ) ^ (-2 * (s : ℤ)) • Corr D 0 p s := by
  change correctionEvaluation D T (correctionLift D 0 p) = _
  rw [correctionEvaluation_option]
  change Polynomial.eval (C ((T : ℂ) ^ (-2 : ℤ))) (correctionPolynomial D 0 p) = _
  rw [Polynomial.eval_eq_sum]
  change (∑ s ∈ (Corr D 0 p).support,
    (Corr D 0 p s) * C ((T : ℂ) ^ (-2 : ℤ)) ^ s) = _
  apply Finset.sum_congr rfl
  intro s hs
  have hexp : ((T : ℂ) ^ (-2 : ℤ)) ^ s = (T : ℂ) ^ (-2 * (s : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
  rw [← map_pow, hexp, mul_comm, C_mul']

private theorem correctionEvaluation_pair (D : LatticeData) (T : ℂˣ)
    (a b : Index D) :
    correctionEvaluation D T (pairPolynomial D a b) = C (nativeSourceSourceKernel D T a b) := by
  have hexp : ((T : ℂ) ^ (-2 : ℤ)) ^ (sourceWeight D a + sourceWeight D b) =
      (T : ℂ) ^ (-2 * (sourceWeight D a : ℤ) - 2 * (sourceWeight D b : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  simp only [pairPolynomial, correctionEvaluation, map_mul, aeval_C, aeval_X,
    Option.elim_none, map_pow, algebraMap_eq]
  simp only [← map_pow, ← map_mul]
  rw [hexp]
  rfl

theorem correctionAt_X_mul (D : LatticeData) (T : ℂˣ)
    (p : Oscillator D) (a : Index D) :
    correctionAt D T (p * X a) =
      X a * correctionAt D T p + ∑ b ∈ p.vars,
        nativeSourceSourceKernel D T a b • correctionAt D T (pderiv b p) := by
  change correctionEvaluation D T (correctionLift D 0 (p * X a)) = _
  rw [correctionLift_X_mul]
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, add_mul, pairDerivation_source_partials, map_add,
    map_mul, map_sum, correctionEvaluation_pair]
  have hsingleton : correctionEvaluation D T (singletonPolynomial D 0 a) = 0 := by
    simp [singletonPolynomial, LatticeGeneratingFieldLocality.bilinear,
      correctionEvaluation, algebraMap_eq]
  rw [hsingleton, zero_mul, add_zero]
  simp only [correctionEvaluation, aeval_X, Option.elim_some, C_mul']
  rfl

end D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
