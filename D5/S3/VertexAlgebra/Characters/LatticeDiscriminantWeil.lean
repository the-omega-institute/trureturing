/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original shifted theta inversion and finite negative Fourier Weil operators. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Group.Integral

/-! # The original discriminant theta transformation and Weil operators

The Fourier identities and Milgram formula are classical. The analytic inputs
are the coordinate-volume matrix Gaussian and coordinate Poisson theorems;
translation uses Mathlib's bilinear Fourier integral. The quadratic data and
literal sectors are those of `LatticeDiscriminantTheta`.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix MeasureTheory

namespace D5.S3.VertexAlgebra.LatticeDiscriminantWeil
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeDiscriminantTheta
open D5.S3.Fourier.MatrixGaussian
open private class_representative shift_eq phase_mk pairRaw pairing_mk pairing_symm
  pairing_add pairing_neg pairing_zero character_orthogonality zero_sector
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

noncomputable section

private def translatedGaussian {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (s : Fin r → ℝ) : C(Fin r → ℝ, ℂ) :=
  (gaussianMap A b).comp (ContinuousMap.addRight s)

private lemma translated_integrable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ) :
    Integrable (translatedGaussian A b s) := by
  have hf : Integrable (gaussianMap A b) := by
    convert integrable_gaussian_linear A hA ((Real.pi : ℂ) * b)
      (by simpa using mul_pos Real.pi_pos hb) 0 0 using 1
    funext x
    simp [gaussianMap, neg_mul]
  exact hf.comp_add_right s

private lemma translated_locally_summable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ)
    (K : TopologicalSpace.Compacts (Fin r → ℝ)) :
    Summable (fun a : Fin r → ℤ =>
      ‖((translatedGaussian A b s).comp
        (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖) := by
  let Ks := K.map (fun x => x + s) (continuous_id.add continuous_const)
  refine (locally_summable_norm_gaussian A hA b hb Ks).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun a => ?_)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  let y : Ks := ⟨(x : Fin r → ℝ) + s, ⟨x, x.property, rfl⟩⟩
  have h := ContinuousMap.norm_coe_le_norm
    (((gaussianMap A b).comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict Ks) y
  have he : ((translatedGaussian A b s).comp
      (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K x =
      ((gaussianMap A b).comp (ContinuousMap.addRight
        (fun i => (a i : ℝ)))).restrict Ks y := by
    change gaussianMap A b (((x : Fin r → ℝ) + (fun i => (a i : ℝ))) + s) =
      gaussianMap A b (((x : Fin r → ℝ) + s) + (fun i => (a i : ℝ)))
    congr 1
    abel
  rw [he]
  exact h

private lemma dot_fourier {r : ℕ} (f : (Fin r → ℝ) → ℂ) (w : Fin r → ℝ) :
    VectorFourier.fourierIntegral Real.fourierChar volume
      (1 : Matrix (Fin r) (Fin r) ℝ).toBilin' f w =
      ∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) * f x := by
  unfold VectorFourier.fourierIntegral
  congr 1
  funext x
  simp only [Matrix.toBilin'_apply', one_mulVec, Circle.smul_def,
    smul_eq_mul, Real.fourierChar_apply]
  congr 2
  rw [dotProduct_comm]
  push_cast
  ring

private lemma translated_fourier {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s w : Fin r → ℝ) :
    (∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      translatedGaussian A b s x) =
      Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ)) *
        ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ))) := by
  rw [← dot_fourier]
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    volume (1 : Matrix (Fin r) (Fin r) ℝ).toBilin' (gaussianMap A b) s) w
  change VectorFourier.fourierIntegral _ _ _ (translatedGaussian A b s) w = _ at h
  rw [h, dot_fourier]
  simp only [Matrix.toBilin'_apply', one_mulVec, Circle.smul_def, smul_eq_mul,
    Real.fourierChar_apply]
  rw [show Complex.exp (((2 * Real.pi * (s ⬝ᵥ w) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ)) by
    congr 1; rw [dotProduct_comm]; push_cast; ring]
  congr 1
  simpa only [gaussianMap, ContinuousMap.coe_mk, Fintype.card_fin] using
    integral_fourier_gaussian A hA b hb w

private lemma translation_phase_norm {r : ℕ} (w s : Fin r → ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private lemma translated_poisson {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ) :
    (∑' n : Fin r → ℤ, Complex.exp
      (-Real.pi * b * (quadratic A ((fun i => (n i : ℝ)) + s) : ℂ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
      ∑' k : Fin r → ℤ, Complex.exp
        (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ)) := by
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  have hs : Summable (fun k : Fin r → ℤ =>
      Complex.exp (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))) := by
    apply Summable.of_norm
    simpa only [norm_mul, translation_phase_norm, one_mul, div_eq_mul_inv, neg_mul] using
      summable_norm_gaussian A⁻¹ hA.inv b⁻¹ hbi
  have hFT (k : Fin r → ℤ) := translated_fourier A hA b hb s (fun i => (k i : ℝ))
  have hsf := hs.mul_left ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2))
  have hp := D5.S3.Fourier.CoordinatePoisson.tsum_eq_tsum_integral
    (translated_integrable A hA b hb s) (translated_locally_summable A hA b hb s)
    (hsf.congr (fun k => by simpa only [mul_left_comm, dotProduct] using (hFT k).symm))
  calc
    _ = ∑' k : Fin r → ℤ, ∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i, (k i : ℝ) * x i : ℝ)) * translatedGaussian A b s x := hp
    _ = ∑' k : Fin r → ℤ, (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        (Complex.exp (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))) := by
      apply tsum_congr
      intro k
      simpa only [dotProduct, mul_left_comm] using hFT k
    _ = _ := tsum_mul_left

private lemma shift_phase (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (k : Charge D) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((fun i => (k i : ℝ)) ⬝ᵥ shift D (representative D a) : ℝ)) =
      pairingCharacter D hD a (classOf D k) := by
  change _ = phase (pairing D a (classOf D k))
  have hp := pairing_mk D hD (representative D a) k
  rw [class_representative D a] at hp
  rw [hp, phase_mk]
  congr 1
  have hc : ((pairRaw D (representative D a) k : ℚ) : ℝ) =
      (fun i => (k i : ℝ)) ⬝ᵥ shift D (representative D a) := by
    rw [dotProduct_comm]
    exact (Rat.castHom ℝ).map_dotProduct _ _
  rw [← hc]
  push_cast
  rfl

private lemma quadratic_neg {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (x : Fin r → ℝ) : quadratic A (-x) = quadratic A x := by
  simp only [quadratic, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

private lemma sector_inverseCoefficient (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    sectorTheta D a (-1 / τ) = (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
      (Real.sqrt (gramReal D).det : ℂ) * inverseCoefficient D hD a τ := by
  let z := -Complex.I * τ
  have hz : 0 < z.re := by simpa [z] using hτ
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hτ0 : τ ≠ 0 := by intro h; simpa [h] using hτ
  have hzi : 0 < (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have harg : z.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have h := translated_poisson (gramReal D) hD z⁻¹ hzi
    (shift D (representative D a))
  have hleft : -(Real.pi : ℂ) * z⁻¹ = Real.pi * Complex.I * (-1 / τ) := by
    dsimp [z]
    field_simp
    simp [Complex.I_sq]
    <;> ring
  have hright : -(Real.pi : ℂ) / z⁻¹ = Real.pi * Complex.I * τ := by
    dsimp [z]
    rw [div_inv_eq_mul]
    ring
  rw [hleft, hright, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg] at h
  have he : -(-(D.rank : ℂ) / 2) = (D.rank : ℂ) / 2 := by ring
  rw [he] at h
  have habs := ((inverse_theta_fourier D hD τ hτ).1 a).1
  have hreindex : (∑' k : Charge D, Complex.exp (2 * Real.pi * Complex.I *
      ((fun i => (k i : ℝ)) ⬝ᵥ shift D (representative D a) : ℝ)) *
        Complex.exp (Real.pi * Complex.I * τ *
          (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))) =
      inverseCoefficient D hD a τ := by
    simp_rw [shift_phase D hD]
    rw [← (Equiv.neg (Charge D)).tsum_eq]
    unfold inverseCoefficient
    apply tsum_congr
    intro k
    have hcast : (fun i => ((-k) i : ℝ)) = -(fun i => (k i : ℝ)) := by ext i; simp
    simp only [Equiv.neg_apply]
    rw [hcast, quadratic_neg]
    rfl
  rw [hreindex] at h
  simpa only [sectorTheta, representativeTheta, div_eq_mul_inv,
    mul_comm (Real.sqrt (gramReal D).det : ℂ)⁻¹] using h

/-- Every original shifted sector transforms by the negative discriminant Fourier kernel. -/
theorem sector_S (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    sectorTheta D a (-1 / τ) = (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
      (Real.sqrt (gramReal D).det : ℂ) * ∑ c : Discriminant D,
        pairingCharacter D hD a (-c) * sectorTheta D c τ := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  rw [sector_inverseCoefficient D hD a τ hτ,
    ((inverse_theta_fourier D hD τ hτ).1 a).2]

#print axioms sector_S

/-- Positive square-root normalization of the original discriminant cardinality. -/
def rho (D : LatticeData) : ℂ := (Real.sqrt (Nat.card (Discriminant D) : ℝ) : ℂ)

section FiniteOperators
variable (D : LatticeData) [hD : Fact (gramReal D).PosDef]
local instance : Fintype (Discriminant D) := Fintype.ofFinite _

/-- Negative finite Fourier transform on the whole complex function space. -/
def weilS : (Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ) where
  toFun f a := (rho D)⁻¹ * ∑ b, pairingCharacter D hD.out a (-b) * f b
  map_add' f g := by ext a; simp [mul_add, Finset.sum_add_distrib]
  map_smul' z f := by ext a; simp [Finset.mul_sum, mul_left_comm, mul_assoc]

/-- Positive Fourier transform on the same whole function space. -/
def weilSplus : (Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ) where
  toFun f a := (rho D)⁻¹ * ∑ b, pairingCharacter D hD.out a b * f b
  map_add' f g := by ext a; simp [mul_add, Finset.sum_add_distrib]
  map_smul' z f := by ext a; simp [Finset.mul_sum, mul_left_comm, mul_assoc]

/-- The original half-norm multiplier. -/
def weilT : (Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ) where
  toFun f a := phase (quadraticClass D a) * f a
  map_add' f g := by ext a; simp [mul_add]
  map_smul' z f := by ext a; simp [mul_left_comm]

/-- Charge conjugation on all functions. -/
def chargeConjugation : (Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ) where
  toFun f a := f (-a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The positive normalized quadratic Gauss sum. -/
def gaussPhase : ℂ := (rho D)⁻¹ * ∑ a : Discriminant D, phase (quadraticClass D a)

private lemma rho_ne_zero : rho D ≠ 0 := by
  have hc := (dual_lattice_realization D hD.out).2.2.1
  unfold rho
  rw [hc]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD.out.det_pos).ne'

private lemma rho_mul_self : rho D * rho D = (Nat.card (Discriminant D) : ℂ) := by
  unfold rho
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

private lemma orthogonality (x : Discriminant D) :
    letI : DecidableEq (Discriminant D) := Classical.decEq _;
    ∑ b : Discriminant D, pairingCharacter D hD.out b x =
      if x = 0 then (Nat.card (Discriminant D) : ℂ) else 0 := by
  classical
  rw [(dual_lattice_realization D hD.out).2.1]
  exact character_orthogonality D hD.out x

private lemma pairing_neg_right (a b : Discriminant D) :
    pairing D a (-b) = -pairing D a b := by
  rw [pairing_symm D a (-b), pairing_neg D hD.out, pairing_symm D b a]

private lemma negative_character_symm (a b : Discriminant D) :
    pairingCharacter D hD.out a (-b) = pairingCharacter D hD.out b (-a) := by
  change phase (pairing D a (-b)) = phase (pairing D b (-a))
  rw [pairing_neg_right D, pairing_neg_right D, pairing_symm D a b]

private lemma kernel_mul (a b c : Discriminant D) :
    pairingCharacter D hD.out a (-b) * pairingCharacter D hD.out b (-c) =
      pairingCharacter D hD.out b (-(a+c)) := by
  rw [negative_character_symm D a b, ← AddChar.map_add_eq_mul, neg_add]

private lemma raw_square (f : Discriminant D → ℂ) (a : Discriminant D) :
    (∑ b : Discriminant D, pairingCharacter D hD.out a (-b) *
      ∑ c : Discriminant D, pairingCharacter D hD.out b (-c) * f c) =
      (Nat.card (Discriminant D) : ℂ) * f (-a) := by
  classical
  simp_rw [Finset.mul_sum, ← mul_assoc, kernel_mul D]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, orthogonality D]
  have he (c : Discriminant D) : -(a+c) = 0 ↔ c = -a := by
    simp only [neg_eq_zero, add_eq_zero_iff_eq_neg']
  simp_rw [he]
  simp

private lemma S_square_apply (f : Discriminant D → ℂ) (a : Discriminant D) :
    weilS D (weilS D f) a = f (-a) := by
  change (rho D)⁻¹ * (∑ b, pairingCharacter D hD.out a (-b) *
    ((rho D)⁻¹ * ∑ c, pairingCharacter D hD.out b (-c) * f c)) = _
  simp_rw [mul_left_comm _ (rho D)⁻¹, ← Finset.mul_sum]
  rw [raw_square D]
  have hr := rho_mul_self D
  rw [← hr]
  field_simp [rho_ne_zero D]

private lemma Splus_eq_CS : weilSplus D =
    (chargeConjugation D).comp (weilS D) := by
  ext f a
  change (rho D)⁻¹ * ∑ b, pairingCharacter D hD.out a b * f b =
    (rho D)⁻¹ * ∑ b, pairingCharacter D hD.out (-a) (-b) * f b
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change phase (pairing D a b) = phase (pairing D (-a) (-b))
  rw [pairing_neg D hD.out, pairing_neg_right D, neg_neg]

private lemma S_commutes_C (f : Discriminant D → ℂ) :
    weilS D (chargeConjugation D f) = chargeConjugation D (weilS D f) := by
  ext a
  change (rho D)⁻¹ * ∑ b, pairingCharacter D hD.out a (-b) * f (-b) =
    (rho D)⁻¹ * ∑ b, pairingCharacter D hD.out (-a) (-b) * f b
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg (Discriminant D))]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Equiv.neg_apply, neg_neg]
  congr 1
  change phase (pairing D a b) = phase (pairing D (-a) (-b))
  rw [pairing_neg D hD.out, pairing_neg_right D, neg_neg]

private lemma q_neg (a : Discriminant D) : quadraticClass D (-a) = quadraticClass D a := by
  simpa using (discriminant_quadratic D hD.out).2.1 a (-1 : ℤ)

private lemma q_sub (b x : Discriminant D) :
    quadraticClass D (b-x) = quadraticClass D b + quadraticClass D x - pairing D b x := by
  rw [sub_eq_add_neg, (discriminant_quadratic D hD.out).1, q_neg D,
    pairing_symm D b, pairing_neg D hD.out, pairing_symm D x]
  simp only [sub_eq_add_neg]

private lemma completed_square (x : Discriminant D) :
    ∑ b : Discriminant D, phase (quadraticClass D b) * pairingCharacter D hD.out b (-x) =
      phase (-quadraticClass D x) * ∑ b : Discriminant D, phase (quadraticClass D b) := by
  have ht (b : Discriminant D) :
      phase (quadraticClass D b) * pairingCharacter D hD.out b (-x) =
        phase (-quadraticClass D x) * phase (quadraticClass D (b-x)) := by
    change phase (quadraticClass D b) * phase (pairing D b (-x)) = _
    rw [← phase.map_add_eq_mul, ← phase.map_add_eq_mul, q_sub D,
      pairing_symm D b, pairing_neg D hD.out, pairing_symm D x]
    congr 1
    abel
  simp_rw [ht]
  rw [← Finset.mul_sum]
  congr 1
  exact (Equiv.subRight x).sum_comp (fun b : Discriminant D => phase (quadraticClass D b))

private lemma quadratic_kernel (a c : Discriminant D) :
    (∑ b : Discriminant D, pairingCharacter D hD.out a (-b) *
      phase (quadraticClass D b) * pairingCharacter D hD.out b (-c)) *
        phase (quadraticClass D c) =
      (∑ b : Discriminant D, phase (quadraticClass D b)) *
        phase (-quadraticClass D a) * pairingCharacter D hD.out a (-c) := by
  have hk (b : Discriminant D) : pairingCharacter D hD.out a (-b) *
      phase (quadraticClass D b) * pairingCharacter D hD.out b (-c) =
      phase (quadraticClass D b) * pairingCharacter D hD.out b (-(a+c)) := by
    rw [mul_right_comm, kernel_mul D, mul_comm]
  simp_rw [hk]
  rw [completed_square D]
  have he : phase (-quadraticClass D (a+c)) * phase (quadraticClass D c) =
      phase (-quadraticClass D a) * pairingCharacter D hD.out a (-c) := by
    change _ = phase (-quadraticClass D a) * phase (pairing D a (-c))
    rw [← phase.map_add_eq_mul, ← phase.map_add_eq_mul,
      pairing_neg_right D, (discriminant_quadratic D hD.out).1]
    congr 1
    abel
  calc
    _ = (∑ b : Discriminant D, phase (quadraticClass D b)) *
        (phase (-quadraticClass D (a+c)) * phase (quadraticClass D c)) := by ring
    _ = _ := by rw [he]; ring

private lemma ST_square_apply (f : Discriminant D → ℂ) (a : Discriminant D) :
    weilS D (weilT D (weilS D (weilT D f))) a =
      gaussPhase D * phase (-quadraticClass D a) * weilS D f a := by
  have hraw : (∑ b : Discriminant D, pairingCharacter D hD.out a (-b) *
      (phase (quadraticClass D b) * ∑ c : Discriminant D,
        pairingCharacter D hD.out b (-c) * (phase (quadraticClass D c) * f c))) =
      (∑ b : Discriminant D, phase (quadraticClass D b)) *
        phase (-quadraticClass D a) * ∑ c, pairingCharacter D hD.out a (-c) * f c := by
    calc
      _ = ∑ c : Discriminant D,
          ((∑ b : Discriminant D, pairingCharacter D hD.out a (-b) *
            phase (quadraticClass D b) * pairingCharacter D hD.out b (-c)) *
              phase (quadraticClass D c)) * f c := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by
        simp_rw [quadratic_kernel D, mul_assoc, ← Finset.mul_sum]
  change (rho D)⁻¹ * (∑ b, pairingCharacter D hD.out a (-b) *
      (phase (quadraticClass D b) * ((rho D)⁻¹ *
        ∑ c, pairingCharacter D hD.out b (-c) * (phase (quadraticClass D c) * f c)))) =
    gaussPhase D * phase (-quadraticClass D a) *
      ((rho D)⁻¹ * ∑ c, pairingCharacter D hD.out a (-c) * f c)
  simp_rw [mul_left_comm _ (rho D)⁻¹, ← Finset.mul_sum]
  rw [hraw]
  unfold gaussPhase
  ring

private lemma ST_cube_apply (f : Discriminant D → ℂ) (a : Discriminant D) :
    weilS D (weilT D (weilS D (weilT D (weilS D (weilT D f))))) a =
      gaussPhase D * f (-a) := by
  rw [ST_square_apply D, S_square_apply D]
  change gaussPhase D * phase (-quadraticClass D a) *
    (phase (quadraticClass D (-a)) * f (-a)) = _
  rw [q_neg D, ← mul_assoc, mul_assoc (gaussPhase D),
    ← phase.map_add_eq_mul, neg_add_cancel, phase.map_zero_eq_one, mul_one]

/-- Full-space negative Fourier identities, with the positive Gauss factor in the cubic law. -/
theorem finite_weil_relations :
    rho D ≠ 0 ∧ rho D * rho D = (Nat.card (Discriminant D) : ℂ) ∧
    (weilS D).comp (weilS D) = chargeConjugation D ∧
    (weilS D).comp ((weilS D).comp ((weilS D).comp (weilS D))) =
      LinearMap.id ∧
    (weilS D).comp (weilSplus D) = LinearMap.id ∧
    (weilSplus D).comp (weilS D) = LinearMap.id ∧
    ((weilS D).comp (weilT D)).comp
      (((weilS D).comp (weilT D)).comp ((weilS D).comp (weilT D))) =
      gaussPhase D • chargeConjugation D := by
  refine ⟨rho_ne_zero D, rho_mul_self D, ?_, ?_, ?_, ?_, ?_⟩
  · ext f a; exact S_square_apply D f a
  · ext f a
    change weilS D (weilS D (weilS D (weilS D f))) a = f a
    rw [S_square_apply D, S_square_apply D, neg_neg]
  · rw [Splus_eq_CS D]
    ext f a
    change weilS D (chargeConjugation D (weilS D f)) a = f a
    rw [S_commutes_C D]
    change weilS D (weilS D f) (-a) = f a
    rw [S_square_apply D, neg_neg]
  · rw [Splus_eq_CS D]
    ext f a
    change weilS D (weilS D f) (-a) = f a
    rw [S_square_apply D, neg_neg]
  · ext f a; exact ST_cube_apply D f a

#print axioms finite_weil_relations

end FiniteOperators

private lemma principal_ST_product (r : ℕ) :
    (1 : ℂ) ^ ((r : ℂ) / 2) *
      (((1-Complex.I)/2 : ℂ) ^ ((r : ℂ) / 2) *
        ((1-Complex.I : ℂ) ^ ((r : ℂ) / 2))) =
      Complex.exp (-Real.pi * Complex.I * (r : ℂ) / 4) := by
  let a : ℂ := 1-Complex.I
  let b : ℂ := (1-Complex.I)/2
  have ha : a ≠ 0 := by dsimp [a]; norm_num [Complex.ext_iff]
  have hb : b ≠ 0 := by dsimp [b]; norm_num [Complex.ext_iff]
  have haL : -(Real.pi/2) < a.arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl (by norm_num [a]))
  have hbL : -(Real.pi/2) < b.arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl (by norm_num [b]))
  have haU : a.arg < 0 := Complex.arg_neg_iff.mpr (by norm_num [a])
  have hbU : b.arg < 0 := Complex.arg_neg_iff.mpr (by norm_num [b])
  have hlog := (Complex.log_mul_eq_add_log_iff ha hb).mpr
    (show a.arg + b.arg ∈ Set.Ioc (-Real.pi) Real.pi from
      ⟨by linarith, by linarith [Real.pi_pos]⟩)
  have hab : a*b = -Complex.I := by dsimp [a,b]; norm_num [Complex.ext_iff]
  have hs : Complex.log a + Complex.log b = -(Real.pi/2) * Complex.I := by
    rw [← hlog, hab, Complex.log_neg_I]
  rw [Complex.one_cpow, one_mul]
  change b ^ ((r : ℂ)/2) * a ^ ((r : ℂ)/2) = _
  rw [Complex.cpow_def_of_ne_zero hb, Complex.cpow_def_of_ne_zero ha, ← Complex.exp_add]
  congr 1
  calc
    _ = (Complex.log a + Complex.log b) * ((r : ℂ)/2) := by ring
    _ = _ := by rw [hs]; ring

private lemma original_zero_theta_positive (D : LatticeData) (hD : (gramReal D).PosDef) :
    1 ≤ (sectorTheta D 0 Complex.I).re := by
  rw [zero_sector D hD Complex.I (by simp)]
  let f : Charge D → ℝ := fun n => Real.exp
    (-Real.pi * quadratic (gramReal D) (fun i => (n i : ℝ)))
  have he (n : Charge D) : Complex.exp (Real.pi * Complex.I * Complex.I *
      (quadratic (gramReal D) (fun i => (n i : ℝ)) : ℂ)) = (f n : ℂ) := by
    rw [mul_assoc (Real.pi : ℂ) Complex.I Complex.I, ← pow_two Complex.I, Complex.I_sq]
    simp only [mul_neg_one, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      Complex.ofReal_exp, f]
  have hs : Summable (fun n : Charge D => (f n : ℂ)) := by
    simpa only [he] using (summable_norm_theta (gramReal D) hD Complex.I (by simp)).of_norm
  have hr : Summable f := Complex.summable_ofReal.mp hs
  have ht := hr.le_tsum (0 : Charge D) (fun n _ => (Real.exp_pos _).le)
  unfold theta
  simp_rw [he]
  rw [Complex.re_tsum hs]
  simp only [Complex.ofReal_re]
  have hf0 : f 0 = 1 := by
    simp [f, quadratic, dotProduct]
  rw [hf0] at ht
  exact ht

private lemma theta_ST (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩;
    (fun a : Discriminant D => sectorTheta D a (-1/(τ+1))) =
      (-Complex.I*(τ+1)) ^ ((D.rank : ℂ)/2) •
        ((weilS D).comp (weilT D)) (fun a => sectorTheta D a τ) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  ext a
  rw [sector_S D hD a (τ+1) (by simpa using hτ)]
  simp_rw [sector_T D hD _ τ hτ]
  have hc := (dual_lattice_realization D hD).2.2.1
  change _ = (-Complex.I * (τ+1)) ^ ((D.rank : ℂ)/2) *
    ((rho D)⁻¹ * ∑ b, pairingCharacter D hD a (-b) *
      (phase (quadraticClass D b) * sectorTheta D b τ))
  have hr : rho D = (Real.sqrt (gramReal D).det : ℂ) := by unfold rho; rw [hc]
  rw [hr, div_eq_mul_inv, mul_assoc]

/-- Milgram's positive phase for every natural rank of the original positive even lattice. -/
theorem milgram (D : LatticeData) (hD : (gramReal D).PosDef) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩;
    gaussPhase D = Complex.exp (Real.pi * Complex.I * (D.rank : ℂ) / 4) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  let Θ : ℂ → (Discriminant D → ℂ) := fun τ a => sectorTheta D a τ
  let U := (weilS D).comp (weilT D)
  let t₁ : ℂ := (-1+Complex.I)/2
  let t₂ : ℂ := -1+Complex.I
  let j₀ : ℂ := (1-Complex.I) ^ ((D.rank : ℂ)/2)
  let j₁ : ℂ := ((1-Complex.I)/2) ^ ((D.rank : ℂ)/2)
  have ht₁ : 0 < t₁.im := by norm_num [t₁]
  have ht₂ : 0 < t₂.im := by norm_num [t₂]
  have hg₀ : -1/(Complex.I+1) = t₁ := by
    norm_num [t₁, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
  have hg₁ : -1/(t₁+1) = t₂ := by
    norm_num [t₁, t₂, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
  have hg₂ : -1/(t₂+1) = Complex.I := by
    norm_num [t₂, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
  have hb₀ : -Complex.I*(Complex.I+1) = 1-Complex.I := by
    norm_num [Complex.ext_iff]
  have hb₁ : -Complex.I*(t₁+1) = (1-Complex.I)/2 := by
    norm_num [t₁, Complex.ext_iff]
  have hb₂ : -Complex.I*(t₂+1) = 1 := by norm_num [t₂, Complex.ext_iff]
  have h₀ : Θ t₁ = j₀ • U (Θ Complex.I) := by
    simpa only [hg₀, hb₀, Θ, U, j₀] using theta_ST D hD Complex.I (by simp)
  have h₁ : Θ t₂ = j₁ • U (Θ t₁) := by
    simpa only [hg₁, hb₁, Θ, U, j₁] using theta_ST D hD t₁ ht₁
  have h₂ : Θ Complex.I = U (Θ t₂) := by
    simpa only [hg₂, hb₂, Complex.one_cpow, one_smul, Θ, U] using theta_ST D hD t₂ ht₂
  have hcycle : Θ Complex.I = (j₁*j₀) • U (U (U (Θ Complex.I))) := by
    calc
      Θ Complex.I = U (Θ t₂) := h₂
      _ = U (j₁ • U (j₀ • U (Θ Complex.I))) := by rw [h₁, h₀]
      _ = _ := by rw [map_smul, map_smul, map_smul, smul_smul]
  have hp : j₁*j₀ = Complex.exp (-Real.pi * Complex.I * (D.rank : ℂ)/4) := by
    simpa only [Complex.one_cpow, one_mul, j₁, j₀] using principal_ST_product D.rank
  have hz := congrFun hcycle 0
  change sectorTheta D 0 Complex.I = (j₁*j₀) *
    weilS D (weilT D (weilS D (weilT D
      (weilS D (weilT D (Θ Complex.I)))))) 0 at hz
  rw [ST_cube_apply D, neg_zero, hp] at hz
  have hn : sectorTheta D 0 Complex.I ≠ 0 := by
    intro h
    have hpos := original_zero_theta_positive D hD
    rw [h] at hpos
    norm_num at hpos
  have hc : (1 : ℂ) = Complex.exp (-Real.pi * Complex.I * (D.rank : ℂ)/4) *
      gaussPhase D := by
    apply mul_right_cancel₀ hn
    simpa only [one_mul, mul_assoc, Θ] using hz
  let w : ℂ := Real.pi * Complex.I * (D.rank : ℂ)/4
  have hexp : Complex.exp w * Complex.exp (-w) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hc' : (1 : ℂ) = Complex.exp (-w) * gaussPhase D := by
    have he : -w = -Real.pi * Complex.I * (D.rank : ℂ)/4 := by dsimp [w]; ring
    rw [he]
    exact hc
  calc
    gaussPhase D = (Complex.exp w * Complex.exp (-w)) * gaussPhase D := by rw [hexp, one_mul]
    _ = Complex.exp w := by rw [mul_assoc, ← hc', mul_one]

#print axioms milgram

end
end D5.S3.VertexAlgebra.LatticeDiscriminantWeil
