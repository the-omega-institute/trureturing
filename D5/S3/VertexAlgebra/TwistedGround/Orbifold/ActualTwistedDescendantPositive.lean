/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualTwistedDescendantPositive
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualTwistedDescendantPositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.TensorProduct]
   utility: none
   digest: The original twisted tensor pairing is Hermitian positive on the selected tensor
   and its negative Leech parity sector. -/

import Mathlib.Analysis.InnerProductSpace.TensorProduct
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualHalfWickPositive

/-!
The signed half-Wick identity identifies the reflected coefficient conjugation
with the original oscillator metric. The selected ground real form supplies
the second metric and the positive scale in the literal tensor BPZ form.
The tensor product here is algebraic, so the result applies to every finite
oscillator descendant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualTwistedDescendantPositive

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality (Oscillator)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor)
open LatticeHalfFockParityT (actualParity)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeInvolution (sigma sigmaLinear sigma_smul sigma_involutive)
open SourceBPZ.OriginalMatterHermitian
  (kappaOsc kappaOsc_add kappaOsc_smul kappaOsc_sigma kappaOsc_involutive)
open SignedOscillatorWick (wick wick_sigma_kappa_eq_oscillatorInner)
open ActualChargedAdjoint (actualForm)
open ActualPairingSymmetry (actualForm_symmetric)
open ActualGroundRealForm
  (GroundRealForm actual_ground_real_form selectedGroundForm hermitianAverage)
open OriginalCurrentMetric (oscillatorCore oscillatorInner)

local notation "D" => leechData
local notation "hu" => (And.left (And.right leech_spec))
local notation "hpos" => (And.left (And.right (And.right leech_spec)))
local notation "O" => Oscillator D
local notation "G" => ActualGround D hu
local notation "T" => ActualTensor D hu
local notation "N" => paritySpace D hu (-1)
local notation "B" => actualForm D hu

/-- The witness for the selected ground factor of the actual Leech tensor form. -/
def groundRealForm : GroundRealForm D hu (selectedGroundForm D hu) :=
  Classical.choice (actual_ground_real_form ⟨D, hu⟩)

private def oscillatorConjugation : O →ₗ⋆[ℂ] O where
  toFun p := sigma D (kappaOsc p)
  map_add' p q := by rw [kappaOsc_add, map_add]
  map_smul' c p := by rw [kappaOsc_smul, sigma_smul]

/-- Reflected coefficient conjugation tensored with the selected ground conjugation. -/
def actualConjugation : T →ₗ⋆[ℂ] T :=
  TensorProduct.map oscillatorConjugation groundRealForm.conjugation

theorem actualConjugation_tmul (p : O) (u : G) :
    actualConjugation (p ⊗ₜ[ℂ] u) =
      sigma D (kappaOsc p) ⊗ₜ[ℂ] groundRealForm.conjugation u := rfl

theorem actualConjugation_involutive : Function.Involutive actualConjugation := by
  have oscillatorSquare :
      oscillatorConjugation.comp oscillatorConjugation = (LinearMap.id : O →ₗ[ℂ] O) := by
    apply LinearMap.ext
    intro p
    change sigma D (kappaOsc (sigma D (kappaOsc p))) = p
    rw [kappaOsc_sigma, sigma_involutive D (kappaOsc (kappaOsc p)), kappaOsc_involutive]
  have groundSquare :
      groundRealForm.conjugation.comp groundRealForm.conjugation = (LinearMap.id : G →ₗ[ℂ] G) :=
    LinearMap.ext groundRealForm.involutive
  have square : actualConjugation.comp actualConjugation = (LinearMap.id : T →ₗ[ℂ] T) := by
    simp only [actualConjugation, ← TensorProduct.map_comp, oscillatorSquare, groundSquare,
      TensorProduct.map_id]
  intro x
  exact LinearMap.congr_fun square x

theorem actualConjugation_parity (x : T) :
    actualConjugation (actualParity D hu x) = actualParity D hu (actualConjugation x) := by
  have oscillatorCommutes :
      oscillatorConjugation.comp (sigmaLinear D) = (sigmaLinear D).comp oscillatorConjugation := by
    apply LinearMap.ext
    intro p
    change sigma D (kappaOsc (sigma D p)) = sigma D (sigma D (kappaOsc p))
    rw [kappaOsc_sigma]
  have commutes :
      actualConjugation.comp (actualParity D hu) = (actualParity D hu).comp actualConjugation := by
    simp only [actualConjugation, actualParity, ← TensorProduct.map_comp, oscillatorCommutes,
      LinearMap.id_comp, LinearMap.comp_id]
  exact LinearMap.congr_fun commutes x

@[instance_reducible]
private def groundCore : InnerProductSpace.Core ℂ G where
  inner x y := hermitianAverage D hu x y
  conj_inner_symm x y := groundRealForm.hermitian_symm y x
  re_inner_nonneg x := by
    change 0 ≤ (hermitianAverage D hu x x).re
    by_cases hx : x = 0
    · subst x
      simp
    · exact (groundRealForm.hermitian_pos x hx).le
  add_left x y z := LinearMap.map_add₂ (hermitianAverage D hu) x y z
  smul_left x y c := by
    change hermitianAverage D hu (c • x) y =
      starRingEnd ℂ c * hermitianAverage D hu x y
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
  definite x hz := by
    change hermitianAverage D hu x x = 0 at hz
    by_contra hx
    have h := groundRealForm.hermitian_pos x hx
    rw [hz, Complex.zero_re] at h
    exact (lt_irrefl 0) h

section

local instance : InnerProductSpace.Core ℂ O := oscillatorCore D hpos
local instance : InnerProductSpace.Core ℂ G := groundCore

local instance (priority := 2000) : NormedAddCommGroup O :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

local instance (priority := 2000) : NormedAddCommGroup G :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

-- The selected ground is a function space with its own default seminorm.
-- Use the seminorm of the Hermitian average consistently in the tensor metric.
local instance (priority := 2000) : SeminormedAddCommGroup G :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

local instance : InnerProductSpace ℂ O :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ O)

local instance : InnerProductSpace ℂ G :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ G)

/-- The exact BPZ normalization on the whole algebraic tensor product. -/
theorem actualForm_conjugation_eq (x y : T) :
    B (actualConjugation x) y = (groundRealForm.scale : ℂ) * inner ℂ x y := by
  induction x using TensorProduct.inductionOn generalizing y with
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, inner_add_left, hx, hz, mul_add]
  | tmul p u =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz, mul_add]
      | tmul q v =>
          rw [actualConjugation_tmul, TensorProduct.inner_tmul]
          change selectedGroundForm D hu (groundRealForm.conjugation u) v *
              wick D (sigma D (kappaOsc p)) q =
            (groundRealForm.scale : ℂ) *
              (oscillatorInner D hpos p q * hermitianAverage D hu u v)
          rw [groundRealForm.normalization, wick_sigma_kappa_eq_oscillatorInner D hpos]
          ac_rfl

theorem actualForm_conjugation_hermitian (x y : T) :
    star (B (actualConjugation x) y) = B (actualConjugation y) x := by
  simp only [actualForm_conjugation_eq, Complex.star_def, map_mul, Complex.conj_ofReal,
    inner_conj_symm]

theorem actualForm_conjugation_positive (x : T) (hx : x ≠ 0) :
    (B (actualConjugation x) x).im = 0 ∧ 0 < (B (actualConjugation x) x).re := by
  refine ⟨Complex.conj_eq_iff_im.mp (actualForm_conjugation_hermitian x x), ?_⟩
  rw [actualForm_conjugation_eq, Complex.re_ofReal_mul]
  exact mul_pos groundRealForm.scale_pos ((re_inner_self_pos (𝕜 := ℂ)).2 hx)

end

/-- Simultaneous conjugation on both slots gives the complex conjugate of the BPZ value. -/
theorem actualForm_conjugation_reality (x y : T) :
    B (actualConjugation x) (actualConjugation y) = star (B x y) := by
  calc
    _ = B (actualConjugation y) (actualConjugation x) :=
      (actualForm_symmetric D hu).eq _ _
    _ = star (B (actualConjugation (actualConjugation x)) y) :=
      (actualForm_conjugation_hermitian (actualConjugation x) y).symm
    _ = _ := by rw [actualConjugation_involutive]

theorem actualConjugation_mem_negative (x : T) (hx : x ∈ N) :
    actualConjugation x ∈ N := by
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hx ⊢
  rw [← actualConjugation_parity, hx, actualConjugation.map_smulₛₗ, map_neg, map_one]

/-- The conjugation on the literal negative Leech parity submodule. -/
def negativeConjugation : N →ₗ⋆[ℂ] N :=
  actualConjugation.restrict actualConjugation_mem_negative

theorem negativeConjugation_involutive : Function.Involutive negativeConjugation := by
  intro x
  apply Subtype.ext
  exact actualConjugation_involutive (x : T)

/-- The Hermitian form obtained from the repository's negative-sector BPZ pairing. -/
def negativeHermitian : N →ₗ⋆[ℂ] N →ₗ[ℂ] ℂ :=
  LinearMap.comp ((actualForm D hu).restrict (paritySpace D hu (-1))) negativeConjugation

theorem negativeHermitian_conj_symm (x y : N) :
    star (negativeHermitian x y) = negativeHermitian y x :=
  actualForm_conjugation_hermitian (x : T) (y : T)

theorem negativeHermitian_positive (x : N) (hx : x ≠ 0) :
    (negativeHermitian x x).im = 0 ∧ 0 < (negativeHermitian x x).re :=
  actualForm_conjugation_positive (x : T) (fun h => hx (Subtype.ext h))

#print axioms actualConjugation_tmul
#print axioms actualConjugation_involutive
#print axioms actualConjugation_parity
#print axioms actualForm_conjugation_eq
#print axioms actualForm_conjugation_hermitian
#print axioms actualForm_conjugation_positive
#print axioms actualForm_conjugation_reality
#print axioms actualConjugation_mem_negative
#print axioms negativeConjugation_involutive
#print axioms negativeHermitian_conj_symm
#print axioms negativeHermitian_positive

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualTwistedDescendantPositive
