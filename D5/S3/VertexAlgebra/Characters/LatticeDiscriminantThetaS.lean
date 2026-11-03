/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantThetaS
   generality: I
   mirror-B: none(source-only)
   mirror-E: none(source-only)
   anchors: []
   utility: none
   digest: Shifted coordinate Poisson summation supplies every original discriminant S row. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

/-!
The missing analytic step after `inverse_theta_fourier` is Poisson summation
for the literal real translate of `MatrixGaussian.gaussianMap`.  The Fourier
translation phase is identified with the original rational inverse-Gram
pairing, before negating the unbounded integer Fourier index.

The Gaussian integral, compact normal convergence, coordinate Poisson theorem,
and finite discriminant Fourier dissection are reused from the imported source.
No complex-vector extension of `integral_gaussian_linear` is used.  Its real
vector and common complex scalar suffice for the unshifted Fourier integral;
translation of the integral supplies the real shift.

This module is source-only and uncompiled.  It supplies no original four-point
`identityK`, exterior half-mode gluing, oscillator/source extraction, or
Monster/VOA/CFT/string/AdS-CFT completion.  Native integration, kernel and
standard-axiom checks, independent review, the current audit obligations, and
official delivery remain to be performed by the native owner.
-/

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open D5.S3.Fourier.MatrixGaussian
noncomputable section

-- Reuse the original quotient/phase proof rather than re-creating a quotient
-- pairing or a dual-lattice realization.  These are precisely the private
-- declarations in the supplied LatticeDiscriminantTheta module.
open private pairRaw pairing_mk phase_mk class_representative
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

private lemma norm_real_fourier_phase (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

-- Translate the compact set, not the integer index.  This supplies exactly
-- the local normal-convergence hypothesis of CoordinatePoisson.
private lemma locally_summable_shifted_gaussian {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ)
    (K : TopologicalSpace.Compacts (Fin r → ℝ)) :
    Summable (fun a : Fin r → ℤ =>
      ‖(((gaussianMap A b).comp (ContinuousMap.addRight s)).comp
        (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖) := by
  let Ks : TopologicalSpace.Compacts (Fin r → ℝ) :=
    ⟨(fun x : Fin r → ℝ => x + s) '' (K : Set (Fin r → ℝ)),
      K.isCompact.image (continuous_id.add continuous_const)⟩
  have hs := locally_summable_norm_gaussian A hA b hb Ks
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  have hx : (x : Fin r → ℝ) + s ∈ (Ks : Set (Fin r → ℝ)) :=
    ⟨(x : Fin r → ℝ), x.property, rfl⟩
  have hbound :=
    (((gaussianMap A b).comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict
      (Ks : Set (Fin r → ℝ))).norm_coe_le_norm
        ⟨(x : Fin r → ℝ) + s, hx⟩
  change ‖gaussianMap A b (((x : Fin r → ℝ) + (fun i => (a i : ℝ))) + s)‖ ≤ _
  rw [add_right_comm (x : Fin r → ℝ) (fun i => (a i : ℝ)) s]
  exact hbound

-- This is a genuine translation of the Fourier integral.  In particular it
-- does not treat a real-vector/common-scalar API as a complex-vector API.
private lemma integral_fourier_shifted_gaussian {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (s w : Fin r → ℝ) :
    (∫ x : Fin r → ℝ,
      Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
        gaussianMap A b (x + s)) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ)) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ))) := by
  let F : (Fin r → ℝ) → ℂ := fun y =>
    Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ (y - s) : ℝ)) *
      gaussianMap A b y
  calc
    _ = ∫ x : Fin r → ℝ, F (x + s) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp [F]
        rw [add_sub_cancel_right])
    _ = ∫ y : Fin r → ℝ, F y := integral_add_right_eq_self F s
    _ = Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ)) *
        ∫ y : Fin r → ℝ,
          Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ y : ℝ)) *
            gaussianMap A b y := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [F]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      apply congrArg Complex.exp
      rw [dotProduct_sub, Complex.ofReal_sub]
      ring
    _ = _ := by
      rw [show (∫ y : Fin r → ℝ,
          Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ y : ℝ)) *
            gaussianMap A b y) =
          (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
            Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ)) from by
        simpa [gaussianMap] using integral_fourier_gaussian A hA b hb w]
      ring

private lemma poisson_shifted_gaussian {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (s : Fin r → ℝ) :
    (∑' n : Fin r → ℤ, Complex.exp
      (-Real.pi * b * (quadratic A ((fun i => (n i : ℝ)) + s) : ℂ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        ∑' k : Fin r → ℤ,
          Complex.exp (2 * Real.pi * Complex.I *
            ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
          Complex.exp (-Real.pi / b *
            (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ)) := by
  let f : C(Fin r → ℝ, ℂ) :=
    (gaussianMap A b).comp (ContinuousMap.addRight s)
  have hg : Integrable (gaussianMap A b) := by
    convert integrable_gaussian_linear A hA ((Real.pi : ℂ) * b)
      (by simpa using mul_pos Real.pi_pos hb) 0 0 using 1
    funext x
    simp [gaussianMap, neg_mul]
  have hf : Integrable f := by
    change Integrable (fun x : Fin r → ℝ => gaussianMap A b (x + s))
    simpa only [Function.comp_def] using
      (measurePreserving_add_right volume s).integrable_comp_of_integrable hg
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  have hdual : Summable (fun k : Fin r → ℤ =>
      ‖Complex.exp (-Real.pi / b *
        (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))‖) := by
    simpa [div_eq_mul_inv, neg_mul] using
      summable_norm_gaussian A⁻¹ hA.inv b⁻¹ hbi
  have hphase : Summable (fun k : Fin r → ℤ =>
      ‖Complex.exp (2 * Real.pi * Complex.I *
          ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
        Complex.exp (-Real.pi / b *
          (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))‖) := by
    simpa only [norm_mul, norm_real_fourier_phase, one_mul] using hdual
  have hFT (k : Fin r → ℤ) :
      (∫ x : Fin r → ℝ,
        Complex.exp (-2 * Real.pi * Complex.I *
          (∑ i, (k i : ℝ) * x i : ℝ)) * f x) =
        (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
          (Complex.exp (2 * Real.pi * Complex.I *
              ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
            Complex.exp (-Real.pi / b *
              (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))) := by
    simpa [f, dotProduct] using
      integral_fourier_shifted_gaussian A hA b hb s (fun i => (k i : ℝ))
  have hfourier := hphase.of_norm.mul_left
    ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2))
  have hp := D5.S3.Fourier.CoordinatePoisson.tsum_eq_tsum_integral hf
    (locally_summable_shifted_gaussian A hA b hb s)
    (hfourier.congr (fun k => (hFT k).symm))
  calc
    _ = ∑' k : Fin r → ℤ, ∫ x : Fin r → ℝ,
        Complex.exp (-2 * Real.pi * Complex.I *
          (∑ i, (k i : ℝ) * x i : ℝ)) * f x := hp
    _ = ∑' k : Fin r → ℤ,
        (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
          (Complex.exp (2 * Real.pi * Complex.I *
              ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
            Complex.exp (-Real.pi / b *
              (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))) := tsum_congr hFT
    _ = _ := tsum_mul_left

-- The real shift is the cast of the actual rational inverse-Gram vector.
-- `pairing_mk` removes only the choice of quotient representative; it is not
-- a chosen sign convention or an additional pairing hypothesis.
private lemma shift_phase_character (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Discriminant D) (k : Charge D) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((fun i => (k i : ℝ)) ⬝ᵥ shift D (representative D a) : ℝ)) =
      pairingCharacter D hD a (classOf D k) := by
  have hp : pairing D a (classOf D k) =
      (pairRaw D (representative D a) k : QmodZ) := by
    simpa only [class_representative] using
      pairing_mk D hD (representative D a) k
  have hr : (pairRaw D (representative D a) k : ℝ) =
      (fun i => (k i : ℝ)) ⬝ᵥ shift D (representative D a) := by
    calc
      (pairRaw D (representative D a) k : ℝ) =
          shift D (representative D a) ⬝ᵥ (fun i => (k i : ℝ)) :=
        (Rat.castHom ℝ).map_dotProduct _ _
      _ = _ := dotProduct_comm _ _
  have hc : (((fun i => (k i : ℝ)) ⬝ᵥ
      shift D (representative D a) : ℝ) : ℂ) =
        (pairRaw D (representative D a) k : ℂ) := by
    rw [← hr]
    simp
  change _ = phase (pairing D a (classOf D k))
  rw [hp, phase_mk, hc]

private lemma inverse_quadratic_neg (D : LatticeData) (k : Charge D) :
    quadratic (gramReal D)⁻¹ (fun i => ((-k) i : ℝ)) =
      quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) := by
  have hk : (fun i => ((-k) i : ℝ)) = -(fun i => (k i : ℝ)) := by
    ext i
    simp
  simp only [hk, quadratic, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

-- Consume the live countable Fourier series before applying its existing
-- finite character resolution.  Negation is a bijection of all Charge D.
private lemma sector_S_inverseCoefficient (D : LatticeData)
    (hD : (gramReal D).PosDef) (a : Discriminant D)
    (τ : ℂ) (hτ : 0 < τ.im) :
    sectorTheta D a (-1 / τ) =
      (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
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
  have hleft : -(Real.pi : ℂ) * z⁻¹ =
      Real.pi * Complex.I * (-1 / τ) := by
    dsimp [z]
    field_simp
    simp [Complex.I_sq]
    <;> ring
  have hright : -(Real.pi : ℂ) / z⁻¹ = Real.pi * Complex.I * τ := by
    dsimp [z]
    rw [div_inv_eq_mul]
    ring
  have hsum :
      (∑' k : Charge D,
        Complex.exp (2 * Real.pi * Complex.I *
            ((fun i => (k i : ℝ)) ⬝ᵥ shift D (representative D a) : ℝ)) *
          Complex.exp (Real.pi * Complex.I * τ *
            (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))) =
        inverseCoefficient D hD a τ := by
    simp_rw [shift_phase_character D hD a]
    let g : Charge D → ℂ := fun k =>
      pairingCharacter D hD a (classOf D k) *
        Complex.exp (Real.pi * Complex.I * τ *
          (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))
    calc
      _ = ∑' k : Charge D, g (-k) := ((Equiv.neg (Charge D)).tsum_eq g).symm
      _ = inverseCoefficient D hD a τ := by
        unfold inverseCoefficient
        apply tsum_congr
        intro k
        dsimp only [g]
        rw [show classOf D (-k) = -classOf D k from rfl, inverse_quadratic_neg]
  have hp := poisson_shifted_gaussian (gramReal D) hD z⁻¹ hzi
    (shift D (representative D a))
  rw [hleft, hright, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg] at hp
  have he : -(-(D.rank : ℂ) / 2) = (D.rank : ℂ) / 2 := by ring
  rw [he, hsum] at hp
  simpa only [sectorTheta, representativeTheta, div_eq_mul_inv,
    mul_comm (Real.sqrt (gramReal D).det : ℂ)⁻¹] using hp

/-- The actual original discriminant theta S transformation in every finite
rank, including rank zero, with the principal complex power and the negative
original inverse-Gram pairing character. -/
theorem sector_S (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    sectorTheta D a (-1 / τ) =
      (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
        (Real.sqrt (gramReal D).det : ℂ) *
          ∑ c : Discriminant D,
            pairingCharacter D hD a (-c) * sectorTheta D c τ := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  rw [sector_S_inverseCoefficient D hD a τ hτ,
    ((inverse_theta_fourier D hD τ hτ).1 a).2]

end
end D5.S3.VertexAlgebra.LatticeDiscriminantTheta
