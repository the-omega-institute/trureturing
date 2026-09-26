/- GID: D5/S3/Quantum/Dynamics/MetaplecticChirp
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/MetaplecticChirp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct measurable phase multipliers as actual L2 unitaries and prove the quadratic shear covariance of the Schrodinger Weyl action. -/

import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-!
The Hilbert-space phase multiplier is constructed on actual L2 equivalence
classes, including its measurable representative, inverse, and norm identity.
The quadratic phase implements the elementary symplectic shear on the actual
Schrodinger Weyl functions. Fourier's L2 unitary is imported from Mathlib.

This is a constructed metaplectic generator, not a proof that every symplectic
matrix has already been factored, that all word relations reduce to the
metaplectic double cover, or that Williamson diagonalization is completed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Dynamics.MetaplecticChirp

open MeasureTheory
open scoped ENNReal ComplexInnerProductSpace

def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem phase_neg_mul (t : ℝ) : phase (-t) * phase t = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

section PhaseL2
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem phase_memLp (θ : X → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    MemLp (fun x => phase (θ x) * f x) 2 μ := by
  apply (Lp.memLp f).norm.mono'
  · have hm : Measurable (fun x => phase (θ x)) := by unfold phase; fun_prop
    exact hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · exact Filter.Eventually.of_forall (fun x => by simp [norm_mul])

/-- Multiplication by a measurable unit-modulus phase on actual L2 classes. -/
def phaseAction (θ : X → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (phase_memLp μ θ hθ f).toLp (fun x => phase (θ x) * f x)

theorem phaseAction_coe (θ : X → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    phaseAction μ θ hθ f =ᵐ[μ] fun x => phase (θ x) * f x :=
  (phase_memLp μ θ hθ f).coeFn_toLp

theorem phaseAction_norm (θ : X → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    ‖phaseAction μ θ hθ f‖ = ‖f‖ := by
  change (eLpNorm (phaseAction μ θ hθ f) 2 μ).toReal = (eLpNorm f 2 μ).toReal
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [phaseAction_coe μ θ hθ f] with x hx
  rw [hx, norm_mul, phase_norm, one_mul]

theorem phaseAction_add (θ : X → ℝ) (hθ : Measurable θ) (f g : Lp ℂ 2 μ) :
    phaseAction μ θ hθ (f + g) = phaseAction μ θ hθ f + phaseAction μ θ hθ g := by
  apply Lp.ext
  filter_upwards [phaseAction_coe μ θ hθ (f + g),
    phaseAction_coe μ θ hθ f, phaseAction_coe μ θ hθ g,
    Lp.coeFn_add f g, Lp.coeFn_add (phaseAction μ θ hθ f) (phaseAction μ θ hθ g)]
    with x hx hf hg hfg hout
  rw [hx, hout, hfg, hf, hg]
  exact mul_add _ _ _

theorem phaseAction_smul (θ : X → ℝ) (hθ : Measurable θ) (c : ℂ) (f : Lp ℂ 2 μ) :
    phaseAction μ θ hθ (c • f) = c • phaseAction μ θ hθ f := by
  apply Lp.ext
  filter_upwards [phaseAction_coe μ θ hθ (c • f), phaseAction_coe μ θ hθ f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (phaseAction μ θ hθ f)] with x hx hf hcf hout
  rw [hx, hout, hcf, hf]
  exact mul_left_comm _ _ _

theorem phaseAction_comp (θ η : X → ℝ) (hθ : Measurable θ) (hη : Measurable η)
    (f : Lp ℂ 2 μ) :
    phaseAction μ θ hθ (phaseAction μ η hη f) =
      phaseAction μ (fun x => θ x + η x) (hθ.add hη) f := by
  apply Lp.ext
  filter_upwards [phaseAction_coe μ θ hθ (phaseAction μ η hη f),
    phaseAction_coe μ η hη f,
    phaseAction_coe μ (fun x => θ x + η x) (hθ.add hη) f] with x h1 h2 h3
  rw [h1, h2, h3, phase_add, mul_assoc]

@[simp] theorem phaseAction_zero (f : Lp ℂ 2 μ) :
    phaseAction μ (fun _ => 0) measurable_const f = f := by
  apply Lp.ext
  filter_upwards [phaseAction_coe μ (fun _ => 0) measurable_const f] with x hx
  simpa using hx

theorem phaseAction_inverse (θ : X → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    phaseAction μ (fun x => -θ x) hθ.neg (phaseAction μ θ hθ f) = f := by
  rw [phaseAction_comp]
  simpa using phaseAction_zero μ f

/-- A genuine complex-linear isometric equivalence; no unitarity axiom is supplied. -/
def phaseUnitary (θ : X → ℝ) (hθ : Measurable θ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := phaseAction μ θ hθ
  invFun := phaseAction μ (fun x => -θ x) hθ.neg
  left_inv := phaseAction_inverse μ θ hθ
  right_inv f := by
    simpa only [neg_neg] using phaseAction_inverse μ (fun x => -θ x) hθ.neg f
  map_add' := phaseAction_add μ θ hθ
  map_smul' := phaseAction_smul μ θ hθ
  norm_map' := phaseAction_norm μ θ hθ

end PhaseL2

section SymplecticShear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev SymmetricForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

def quadratic (B : SymmetricForm E) (x : E) : ℝ := B x x / 2

def chirpFunction (B : SymmetricForm E) (f : E → ℂ) (x : E) : ℂ :=
  phase (quadratic B x) * f x

/-- Weyl's actual Schrodinger translation/modulation formula, with hbar=1. -/
def weylFunction (q : E) (p : E →L[ℝ] ℝ) (f : E → ℂ) (x : E) : ℂ :=
  phase (p x - p q / 2) * f (x - q)

private theorem quadratic_difference (B : SymmetricForm E)
    (hB : ∀ x y, B x y = B y x) (x q : E) :
    quadratic B x - quadratic B (x - q) = B q x - B q q / 2 := by
  unfold quadratic
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hB x q]
  ring

/-- The constructed quadratic multiplier implements the canonical shear.
The identity is pointwise for every function, so no smoothness domain is hidden. -/
theorem chirp_weyl_covariance (B : SymmetricForm E) (hB : ∀ x y, B x y = B y x)
    (q : E) (p : E →L[ℝ] ℝ) (f : E → ℂ) :
    chirpFunction B (weylFunction q p (chirpFunction (-B) f)) =
      weylFunction q (p + B q) f := by
  funext x
  have hq := quadratic_difference B hB x q
  have hphase : quadratic B x + (p x - p q / 2) + quadratic (-B) (x - q) =
      (p + B q) x - (p + B q) q / 2 := by
    simp only [quadratic, ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply] at *
    linarith
  unfold chirpFunction weylFunction
  rw [← mul_assoc, ← mul_assoc, ← phase_add, ← phase_add, hphase]

/-- The classical phase-space shear preserves the canonical alternating pairing. -/
theorem shear_symplectic (B : SymmetricForm E) (hB : ∀ x y, B x y = B y x)
    (q r : E) (p s : E →L[ℝ] ℝ) :
    (p + B q) r - (s + B r) q = p r - s q := by
  simp only [ContinuousLinearMap.add_apply]
  rw [hB q r]
  ring

variable [MeasurableSpace E] [BorelSpace E]

/-- The same quadratic phase as an actual unitary on L2 of the given measure. -/
def chirpUnitary (μ : Measure E) (B : SymmetricForm E) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  phaseUnitary μ (quadratic B) (by unfold quadratic; fun_prop)

end SymplecticShear

#print axioms phaseUnitary
#print axioms chirp_weyl_covariance
#print axioms shear_symplectic
end D5.S3.Quantum.Dynamics.MetaplecticChirp
