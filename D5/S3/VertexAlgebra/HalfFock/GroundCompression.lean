/- GID: D5/S3/VertexAlgebra/HalfFock/GroundCompression
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/GroundCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical augmentation of the full native neutral corrected field. -/

/- The native half-Fock suppliers retain Kalle Kytölä (c) 2025 and the
   additional half-integer implementation (c) 2026, Apache 2.0.
   Classical context: Dong–Nagatomo math/9808088v1 §3.2 and
   Bakalov–Kac math/0402315v1 §4.4. The compression proof connects the
   actual pointwise normal-word construction to polynomial augmentation. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal

/-! Canonical constant-coefficient compression of the native algebraic fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundCompression

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFiniteCorrection LatticeHalfFockCorrectedField
open LatticeHalfFockCorrectedConformal MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

/-- The genuine oscillator constant coefficient, with no chosen dual vector. -/
def epsilon (D : LatticeData) : Oscillator D →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ 0

/-- Include every actual ground vector as the oscillator vacuum tensor. -/
def iota (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualGround D hu →ₗ[ℂ] ActualTensor D hu :=
  TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu) 1

/-- The canonical tensor augmentation, using the tensor unit equivalence. -/
def pi (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualTensor D hu →ₗ[ℂ] ActualGround D hu :=
  (TensorProduct.lid ℂ (ActualGround D hu)).toLinearMap.comp
    (TensorProduct.map (epsilon D) LinearMap.id)

private theorem pi_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (r : Oscillator D) (g : ActualGround D hu) :
    pi D hu (r ⊗ₜ[ℂ] g) = epsilon D r • g := by
  simp [pi]

/- proof_shape: ground_retraction: bind-only
   consumed by polynomialField_ground_compression through the empty word. -/
theorem ground_retraction (D : LatticeData) (hu : IsUnit D.G.det) :
    (pi D hu).comp (iota D hu) = LinearMap.id := by
  ext g
  simp [iota, pi_tmul, epsilon, MvPolynomial.lcoeff]

/-- Compression is linear in the actual operator. -/
def compression (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (ActualTensor D hu) →ₗ[ℂ] Module.End ℂ (ActualGround D hu) where
  toFun A := (pi D hu).comp (A.comp (iota D hu))
  map_add' A B := by ext g; simp
  map_smul' c A := by ext g; simp

private theorem negative_current_augmentation (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (mode : ℤ) (negative : mode < 0) (v : ActualTensor D hu) :
    pi D hu (jetCurrent D hu index mode v) = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul r g =>
    simp only [jetCurrent, LinearMap.smul_apply, map_smul,
      LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd, TensorProduct.map_tmul,
      LinearMap.id_apply, LatticeHalfFock.current, ite_eq_left negative,
      LinearMap.mulLeft_apply, pi_tmul]
    have aug : epsilon D (X (index.1, (-mode-1).toNat) * r) = 0 := by
      change MvPolynomial.constantCoeff (X (index.1, (-mode-1).toNat) * r) = 0
      simp
    rw [aug, zero_smul, smul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

private theorem nonnegative_current_vacuum (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (mode : ℤ) (nonnegative : 0 ≤ mode) (g : ActualGround D hu) :
    jetCurrent D hu index mode (iota D hu g) = 0 := by
  have annihilate_one : LatticeActualAnnihilation.annihilate D index.1 mode.toNat 1 = 0 := by
    rw [← LatticeActualAnnihilation.annihilation_apply, Derivation.map_one_eq_zero]
  simp [iota, jetCurrent, LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
    LatticeHalfFock.current, show ¬ mode < 0 by omega, annihilate_one]

/- The negative-current statement is for EVERY tensor, including an arbitrary
   seed output. No multiplicativity, commutation or left/right induction is used. -/
private theorem nonempty_flatTerm_augmentation (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (index : Index D) (tail : List (Index D))
    (e : ℤ) (g : ActualGround D hu) (modes : ModeTuple D (index :: tail)) :
    pi D hu (flatTerm D hu field (index :: tail) e (iota D hu g) modes) = 0 := by
  rcases modes with ⟨mode, rest⟩
  by_cases negative : mode < 0
  · simp only [flatTerm, flatCoefficient, ite_eq_left negative, Module.End.mul_apply]
    exact negative_current_augmentation D hu index mode negative _
  · simp only [flatTerm, flatCoefficient, ite_eq_right negative, Module.End.mul_apply,
      nonnegative_current_vacuum D hu index mode (by omega) g, map_zero]

private theorem nonempty_word_augmentation (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (index : Index D) (tail : List (Index D))
    (e : ℤ) (g : ActualGround D hu) :
    pi D hu ((wordField D hu field (index :: tail)).coeff e (iota D hu g)) = 0 := by
  rw [wordField_coefficient,
    map_finsum _ (flatTerm_finite D hu field (index :: tail) e (iota D hu g))]
  simp only [nonempty_flatTerm_augmentation, finsum_zero]

private theorem monomial_augmentation (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Index D →₀ ℕ) (e : ℤ) (g : ActualGround D hu) :
    pi D hu ((polynomialField D hu 0 (monomial a 1)).coeff e (iota D hu g)) =
      (if e = 0 then epsilon D (monomial a 1) else 0) • g := by
  classical
  rw [polynomialField_monomial_public]
  by_cases zero : a = 0
  · subst a
    rw [show occurrences D 0 = [] by simp [occurrences], wordField_coefficient]
    change pi D hu (∑ᶠ _ : Unit, (chargedField D hu 0).coeff e (iota D hu g)) = _
    rw [finsum_unique, current_charged_zero_identity, current_identity_coefficient]
    have retract := LinearMap.congr_fun (ground_retraction D hu) g
    change pi D hu (iota D hu g) = g at retract
    split_ifs <;> simp [epsilon, MvPolynomial.lcoeff, retract]
  · have nonempty : occurrences D a ≠ [] := by
      intro empty
      have multisetZero : a.toMultiset = 0 := by
        have h := congrArg (fun w : List (Index D) => (w : Multiset (Index D))) empty
        simpa [occurrences] using h
      exact zero (by simpa using congrArg Multiset.toFinsupp multisetZero)
    cases word : occurrences D a with
    | nil => exact (nonempty word).elim
    | cons index tail =>
      rw [nonempty_word_augmentation]
      simp [epsilon, MvPolynomial.lcoeff, zero]

/- proof_shape: polynomialField_ground_compression: content
   admission_basis: escape-witness
   escape_witness: The head sign split in the actual flatCoefficient kills each
   nonempty normal term under canonical tensor augmentation; flatTerm_finite
   transports this through the actual vector-valued mode sum. -/
theorem polynomialField_ground_compression (D : LatticeData) (hu : IsUnit D.G.det)
    (r : Oscillator D) (e : ℤ) :
    (pi D hu).comp (((polynomialField D hu 0 r).coeff e).comp (iota D hu)) =
      (if e = 0 then epsilon D r else 0) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro g
  change pi D hu ((polynomialField D hu 0 r).coeff e (iota D hu g)) =
    (if e = 0 then epsilon D r else 0) • g
  induction r using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hp, hq]
    split_ifs <;> simp [add_smul]
  | monomial a c =>
    rw [show monomial a c = c • (monomial a 1 : Oscillator D) by
      simp [MvPolynomial.smul_monomial]]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
      monomial_augmentation, smul_smul]
    split_ifs <;> simp

/- proof_shape: correctedField_ground_compression: content
   admission_basis: escape-witness
   escape_witness: The actual finite Corr, Hahn shift and full normal supplier
   are composed with the proved normal augmentation law, retaining the vacuum
   term and all inhomogeneous correction coefficients. -/
theorem correctedField_ground_compression (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Oscillator D) (e : ℤ) :
    (pi D hu).comp (((correctedField D hu (Finsupp.single 0 p)).coeff e).comp (iota D hu)) =
      (∑ s ∈ (Corr D 0 p).support,
        if e = -2 * (s : ℤ) then epsilon D ((Corr D 0 p) s) else 0) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro g
  change pi D hu ((correctedField D hu (Finsupp.single 0 p)).coeff e (iota D hu g)) =
    (∑ s ∈ (Corr D 0 p).support,
      if e = -2 * (s : ℤ) then epsilon D ((Corr D 0 p) s) else 0) • g
  rw [correctedField, Finsupp.lsum_single]
  simp only [correctedPolynomial, LinearMap.comp_apply, correctedSum,
    Finsupp.lsum_apply, Finsupp.sum]
  change pi D hu ((∑ s ∈ (Corr D 0 p).support,
    shiftField D hu s (polynomialField D hu 0 ((Corr D 0 p) s))).coeff e (iota D hu g)) = _
  change pi D hu (coefficientAt D hu e (iota D hu g)
    (∑ s ∈ (Corr D 0 p).support, shiftField D hu s (polynomialField D hu 0 ((Corr D 0 p) s)))) = _
  simp only [map_sum]
  change (∑ s ∈ (Corr D 0 p).support, pi D hu
    ((shiftField D hu s (polynomialField D hu 0 ((Corr D 0 p) s))).coeff e (iota D hu g))) = _
  simp only [shiftField_coefficient_public, LinearMap.smul_apply, LinearMap.id_apply]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro s hs
  have normal := LinearMap.congr_fun (polynomialField_ground_compression D hu
    ((Corr D 0 p) s) (e + 2 * (s : ℤ))) g
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    show e + 2 * (s : ℤ) = 0 ↔ e = -2 * (s : ℤ) by omega] using normal

private theorem compressed_support (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Oscillator D) :
    Function.support (fun e => compression D hu
      ((correctedField D hu (Finsupp.single 0 p)).coeff e)) ⊆
      (Corr D 0 p).support.image (fun s : ℕ => -2 * (s : ℤ)) := by
  classical
  intro e nonzero
  by_contra outside
  have absent : ∀ s ∈ (Corr D 0 p).support, e ≠ -2 * (s : ℤ) := by
    intro s hs equal
    exact outside (Finset.mem_image.mpr ⟨s, hs, equal.symm⟩)
  apply nonzero
  change (pi D hu).comp (((correctedField D hu (Finsupp.single 0 p)).coeff e).comp (iota D hu)) = 0
  rw [correctedField_ground_compression]
  have zeroSum : (∑ s ∈ (Corr D 0 p).support,
      if e = -2 * (s : ℤ) then epsilon D ((Corr D 0 p) s) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    exact ite_eq_right (absent s hs)
  rw [zeroSum, zero_smul]

private theorem compressed_odd (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Oscillator D) (e : ℤ) (odd : e % 2 = 1) :
    compression D hu ((correctedField D hu (Finsupp.single 0 p)).coeff e) = 0 := by
  classical
  by_contra nonzero
  obtain ⟨s, hs, equal⟩ := Finset.mem_image.mp (compressed_support D hu p nonzero)
  omega

/-- The full compressed field as a finite Laurent coefficient family, with its
    odd coefficients proved zero. Its values are the actual compressed operators. -/
def compressedLaurent (D : LatticeData) (hu : IsUnit D.G.det) (p : Oscillator D) :
    {f : ℤ →₀ Module.End ℂ (ActualGround D hu) // ∀ e : ℤ, e % 2 = 1 → f e = 0} :=
  ⟨Finsupp.ofSupportFinite
    (fun e => compression D hu ((correctedField D hu (Finsupp.single 0 p)).coeff e))
    (((Corr D 0 p).support.image (fun s : ℕ => -2 * (s : ℤ))).finite_toSet.subset
      (compressed_support D hu p)),
    compressed_odd D hu p⟩

end
end D5.S3.VertexAlgebra.LatticeHalfFockGroundCompression
