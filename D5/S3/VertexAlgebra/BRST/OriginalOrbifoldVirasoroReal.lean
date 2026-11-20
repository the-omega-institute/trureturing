import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.OriginalBRSTWeightPositive
import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal

/-!
Coefficient conjugation fixes the integer lattice currents. Reflected coefficient
conjugation negates each half-current, so its signs cancel in a quadratic mode.
The inverse Gram entries and the half-Fock vacuum shift are real. The twisted
sector combines the oscillator map with the existing ground conjugation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct
open ComplexConjugate

namespace D5.S3.VertexAlgebra.OriginalOrbifoldVirasoroReal

open ActualLeechHyperbolic (leechData leech_spec)
open OriginalBRSTWeightPositive (orbifoldConjugation)
open OriginalOrbifoldCriticalMatter
  (Orbifold Hyperbolic Matter orbifoldMode hyperbolicData hyperbolicMode mode hyperbolicInverse
    hyperbolic_inverse_left hyperbolic_inverse_right)
open LatticeGeneratingFieldLocality (LatticeData Carrier Oscillator)
open LatticeInvolution (sigma sigma_smul)
open LatticeSugawaraCurrents
  (gramComplex normalSummand normalSummand_finite sugawaraMode sugawaraMode_finsum)
open LatticeHalfFock (current frequency normalPair normalPair_finite rawL tensorL tensorEnd)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open SourceBPZ.OriginalMatterHermitian
  (kappaCarrier kappaCarrier_add kappaCarrier_smul kappaCarrier_neutralMode
    kappaCarrier_involutive conjugateH_eq_H
    kappaOsc kappaOsc_add kappaOsc_smul kappaOsc_X kappaOsc_mul
    kappaOsc_annihilate kappaOsc_involutive)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor)
open TwistedGround.OriginalOrbifoldConformal (L_fixed_apply L_twisted_apply)
open TwistedGround.Orbifold.ActualTwistedDescendantPositive
  (actualConjugation actualConjugation_tmul groundRealForm)
open private tensorEnd_tmul from D5.S3.VertexAlgebra.LatticeHalfFockTensorFields
open private sigma_current from D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
open private rawL_apply from D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal

/-- An injective additive map preserves the exact set of nonzero summands. -/
private theorem map_finsum_of_termwise {V : Type*} [AddCommGroup V]
    (F : V →+ V) (hF : Function.Injective F)
    {f g : ℤ → V} (hf : Function.HasFiniteSupport f)
    (h : ∀ j, F (f j) = g j) :
    F (∑ᶠ j, f j) = ∑ᶠ j, g j := by
  classical
  have hsupport : Function.support g = Function.support f := by
    ext j
    change g j ≠ 0 ↔ f j ≠ 0
    rw [← h j]
    constructor
    · intro hn hz
      exact hn (by rw [hz, map_zero])
    · intro hn hz
      exact hn (hF (hz.trans (map_zero F).symm))
  let s := hf.toFinset
  have hs : (s : Set ℤ) = Function.support f := hf.coe_toFinset
  have hfs : Function.support f ⊆ (s : Set ℤ) := hs.ge
  have hgs : Function.support g ⊆ (s : Set ℤ) := hsupport.le.trans hfs
  rw [finsum_eq_finsetSum_of_support_subset f hfs,
    finsum_eq_finsetSum_of_support_subset g hgs, map_sum]
  exact Finset.sum_congr rfl (fun j _ => h j)

section Lattice

variable {D : LatticeData}

private theorem inverse_entry_real (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (i j : Fin D.rank) :
    starRingEnd ℂ (H i j) = H i j :=
  congrArg (fun H : Matrix (Fin D.rank) (Fin D.rank) ℂ => H i j)
    (conjugateH_eq_H H hHG hGH)

private theorem halfFactor_real : starRingEnd ℂ ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  simp [map_inv₀, map_ofNat]

private def carrierConjugation (D : LatticeData) : Carrier D →ₗ⋆[ℂ] Carrier D where
  toFun := kappaCarrier
  map_add' := kappaCarrier_add
  map_smul' := kappaCarrier_smul

private theorem kappaCarrier_normalSummand (i j : Fin D.rank) (k l : ℤ)
    (x : Carrier D) :
    kappaCarrier (normalSummand D i j k l x) =
      normalSummand D i j k l (kappaCarrier x) := by
  unfold normalSummand
  split_ifs <;> simp only [Module.End.mul_apply, kappaCarrier_neutralMode]

/-- Coefficient conjugation commutes with every original inverse-Gram Sugawara mode. -/
private theorem kappaCarrier_sugawaraMode (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m : ℤ) (x : Carrier D) :
    kappaCarrier (sugawaraMode D H m x) = sugawaraMode D H m (kappaCarrier x) := by
  change carrierConjugation D (sugawaraMode D H m x) =
    sugawaraMode D H m (carrierConjugation D x)
  simp only [sugawaraMode_finsum, LinearMap.map_smulₛₗ, map_sum, halfFactor_real,
    inverse_entry_real H hHG hGH]
  apply congrArg (fun v : Carrier D => (2 : ℂ)⁻¹ • v)
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  apply congrArg (fun v : Carrier D => H i j • v)
  have hK : Function.Involutive (carrierConjugation D) := kappaCarrier_involutive
  exact map_finsum_of_termwise (carrierConjugation D).toAddMonoidHom hK.injective
    (normalSummand_finite D i j m x) (fun k => kappaCarrier_normalSummand i j k (m - k) x)

private def reflectedOscillatorConjugation (D : LatticeData) :
    Oscillator D →ₗ⋆[ℂ] Oscillator D where
  toFun p := sigma D (kappaOsc p)
  map_add' p q := by rw [kappaOsc_add, map_add]
  map_smul' c p := by rw [kappaOsc_smul, sigma_smul]

private theorem reflectedOscillatorConjugation_injective :
    Function.Injective (reflectedOscillatorConjugation D) := by
  intro p q h
  have hk : kappaOsc p = kappaOsc q := (LatticeInvolution.sigma_involutive D).injective h
  simpa only [kappaOsc_involutive] using
    congrArg (fun v : Oscillator D => kappaOsc v) hk

private theorem kappaOsc_current (i : Fin D.rank) (j : ℤ) (p : Oscillator D) :
    kappaOsc (current D i j p) = current D i j (kappaOsc p) := by
  by_cases hj : j < 0
  · simp only [current, ite_eq_left hj, LinearMap.mulLeft_apply, kappaOsc_mul, kappaOsc_X]
  · have hf : conj (frequency j) = frequency j := by
      simp [frequency, map_ofNat]
    simp only [current, ite_eq_right hj, LinearMap.smul_apply, kappaOsc_smul,
      kappaOsc_annihilate, hf]

private theorem reflectedOscillatorConjugation_current
    (i : Fin D.rank) (j : ℤ) (p : Oscillator D) :
    reflectedOscillatorConjugation D (current D i j p) =
      -current D i j (reflectedOscillatorConjugation D p) := by
  change sigma D (kappaOsc (current D i j p)) = -current D i j (sigma D (kappaOsc p))
  rw [kappaOsc_current, sigma_current]

private theorem reflectedOscillatorConjugation_normalPair
    (i l : Fin D.rank) (j k : ℤ) (p : Oscillator D) :
    reflectedOscillatorConjugation D (normalPair D i l j k p) =
      normalPair D i l j k (reflectedOscillatorConjugation D p) := by
  unfold normalPair
  split_ifs <;> simp only [Module.End.mul_apply, reflectedOscillatorConjugation_current,
    map_neg, neg_neg]

private theorem reflectedOscillatorConjugation_rawL (hu : IsUnit D.G.det)
    (m : ℤ) (p : Oscillator D) :
    reflectedOscillatorConjugation D (rawL D (actualInverse D) m p) =
      rawL D (actualInverse D) m (reflectedOscillatorConjugation D p) := by
  simp only [rawL_apply, LinearMap.map_smulₛₗ, map_sum, halfFactor_real,
    inverse_entry_real (actualInverse D) (actualInverse_left D hu) (actualInverse_right D hu)]
  apply congrArg (fun v : Oscillator D => (2 : ℂ)⁻¹ • v)
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  apply congrArg (fun v : Oscillator D => actualInverse D i l • v)
  exact map_finsum_of_termwise (reflectedOscillatorConjugation D).toAddMonoidHom
    reflectedOscillatorConjugation_injective (normalPair_finite D i l m p)
    (fun j => reflectedOscillatorConjugation_normalPair i l j (m - j - 1) p)

private theorem reflectedOscillatorConjugation_halfL (hu : IsUnit D.G.det)
    (m : ℤ) (p : Oscillator D) :
    reflectedOscillatorConjugation D (LatticeHalfFock.L D (actualInverse D) m p) =
      LatticeHalfFock.L D (actualInverse D) m (reflectedOscillatorConjugation D p) := by
  have hshift : starRingEnd ℂ (if m = 0 then (D.rank : ℂ) / 16 else 0) =
      (if m = 0 then (D.rank : ℂ) / 16 else 0) := by
    by_cases hm : m = 0 <;> simp [hm, map_div₀, map_ofNat]
  simp only [LatticeHalfFock.L, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, LinearMap.map_smulₛₗ, hshift,
    reflectedOscillatorConjugation_rawL hu]

end Lattice

local notation "D" => leechData
local notation "hu" => (And.left (And.right leech_spec))

/-- Covariance on the actual tensor uses only the ground map in the pure-tensor formula. -/
private theorem actualConjugation_tensorL (m : ℤ) (x : ActualTensor D hu) :
    actualConjugation (tensorL D (ActualGround D hu) (actualInverse D) m x) =
      tensorL D (ActualGround D hu) (actualInverse D) m (actualConjugation x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p u =>
      simp only [tensorL, tensorEnd_tmul, actualConjugation_tmul]
      exact congrArg (fun q : Oscillator D => q ⊗ₜ[ℂ] groundRealForm.conjugation u)
        (reflectedOscillatorConjugation_halfL hu m p)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On the fixed sector, the BRST positivity conjugation is coefficient conjugation. -/
theorem orbifoldConjugation_fixed_apply (x : Orbifold) :
    (orbifoldConjugation x).1.val = kappaCarrier x.1.val := rfl

/-- On the twisted sector, the BRST positivity conjugation is the actual tensor conjugation. -/
theorem orbifoldConjugation_twisted_apply (x : Orbifold) :
    (orbifoldConjugation x).2.val = actualConjugation x.2.val := rfl

/-- The conjugation inducing the positive BRST form commutes with every
Virasoro mode of the original Leech orbifold field. -/
theorem orbifoldConjugation_commutes_L (m : ℤ) :
    Function.Commute orbifoldConjugation (orbifoldMode m) := by
  intro x
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [orbifoldConjugation_fixed_apply, orbifoldMode, L_fixed_apply] using
      kappaCarrier_sugawaraMode (actualInverse D) (actualInverse_left D hu)
        (actualInverse_right D hu) m x.1.val
  · simpa only [orbifoldConjugation_twisted_apply, orbifoldMode, L_twisted_apply] using
      actualConjugation_tensorL m x.2.val

/-- Coefficient conjugation commutes with each native hyperbolic Virasoro mode. -/
theorem kappaCarrier_hyperbolicMode (m : ℤ) (x : Hyperbolic) :
    kappaCarrier (hyperbolicMode m x) = hyperbolicMode m (kappaCarrier x) :=
  kappaCarrier_sugawaraMode hyperbolicInverse hyperbolic_inverse_left hyperbolic_inverse_right m x

/-- The tensor conjugation on the matter carrier used by the native BRST charge. -/
def matterConjugation : Matter →ₗ⋆[ℂ] Matter :=
  TensorProduct.map orbifoldConjugation (carrierConjugation hyperbolicData)

/-- Both Virasoro summands commute with the induced conjugation on critical matter. -/
theorem matterConjugation_commutes_mode (m : ℤ) :
    Function.Commute matterConjugation (mode m) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      have hO : orbifoldConjugation (orbifoldMode m v) =
          orbifoldMode m (orbifoldConjugation v) := orbifoldConjugation_commutes_L m v
      have hH : carrierConjugation hyperbolicData (hyperbolicMode m w) =
          hyperbolicMode m (carrierConjugation hyperbolicData w) :=
        kappaCarrier_hyperbolicMode m w
      simp only [matterConjugation, mode, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, map_add, TensorProduct.map_tmul, hO, hH]
  | add x y hx hy => simp only [map_add, hx, hy]

#print axioms orbifoldConjugation_fixed_apply
#print axioms orbifoldConjugation_twisted_apply
#print axioms orbifoldConjugation_commutes_L
#print axioms kappaCarrier_hyperbolicMode
#print axioms matterConjugation_commutes_mode

end D5.S3.VertexAlgebra.OriginalOrbifoldVirasoroReal
