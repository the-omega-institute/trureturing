/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.TensorProduct]
   utility: none
   digest: The original orbifold and hyperbolic forms transpose opposite critical matter modes. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldCriticalMatter
import D5.S3.VertexAlgebra.SourceBPZ.SugawaraTranspose
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Batteries.Tactic.OpenPrivate

/-!
The fixed and negative twisted summands are orthogonal by construction.
Virasoro transposition holds for each summand separately and therefore leaves
their relative normalization free. All-state orbifold invariance requires
matching the relative coefficients of the right intertwiner and the actual
two-twisted bracket `originalI` in the mixed adjunctions. The latter uses
`normalizedCoefficient` and the inverse of the fixed source grade pairing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMatterBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldCriticalMatter
open LatticeGeneratingFieldLocality (LatticeData Charge Oscillator)
open LatticeInvolution (fixedSpace thetaLinear theta_involutive)
open HalfFockSpectralFiberSource (actualInverse)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open LatticeHalfFockGradedTrace (actualAmbientBasis actual_basis_eigenvalue oddWeight)
open LatticeHalfFockParityT (actualParity)
open SourceBPZ.OriginalSourcePairing (sourcePairing integerWick sourcePairing_single_single
  sourcePairing_symmetric sourcePairing_nondegenerate)
open SourceBPZ.SourcePairingLaws (sourcePairing_theta)
open SourceBPZ.SugawaraTranspose (sourcePairing_sugawaraMode)
open TwistedGround.ActualChargedAdjoint (actualForm actualForm_nondegenerate)
open TwistedGround.ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open TwistedGround.ActualPairingSymmetry (actualForm_symmetric)
open private actual_stress_transpose basis_parity from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

/-- The original source pairing on the literal fixed submodule. -/
def fixedBPZ : LinearMap.BilinForm ℂ (fixedSpace leechData) :=
  (sourcePairing leechData).restrict (fixedSpace leechData)

/-- The actual half-Fock and ground form on the literal negative submodule. -/
def negativeBPZ : LinearMap.BilinForm ℂ (paritySpace leechData leech_spec.2.1 (-1)) :=
  (actualForm leechData leech_spec.2.1).restrict (paritySpace leechData leech_spec.2.1 (-1))

/-- The block diagonal form on the carrier of the original Leech sign orbifold. -/
def orbifoldBPZ : LinearMap.BilinForm ℂ Orbifold :=
  fixedBPZ.compl₁₂ (LinearMap.fst ℂ _ _) (LinearMap.fst ℂ _ _) +
    negativeBPZ.compl₁₂ (LinearMap.snd ℂ _ _) (LinearMap.snd ℂ _ _)

theorem orbifoldBPZ_apply (x y : Orbifold) :
    orbifoldBPZ x y =
      sourcePairing leechData x.1.val y.1.val +
        actualForm leechData leech_spec.2.1 x.2.val y.2.val := rfl

/-- The canonical lattice form on the genuine hyperbolic carrier. -/
abbrev hyperbolicBPZ : LinearMap.BilinForm ℂ Hyperbolic := sourcePairing hyperbolicData

/-- The form on the critical matter tensor product. -/
def matterBPZ : LinearMap.BilinForm ℂ Matter := orbifoldBPZ.tmul hyperbolicBPZ

theorem matterBPZ_tmul (x y : Orbifold) (p q : Hyperbolic) :
    matterBPZ (x ⊗ₜ[ℂ] p) (y ⊗ₜ[ℂ] q) = orbifoldBPZ x y * hyperbolicBPZ p q := by
  change hyperbolicBPZ p q * orbifoldBPZ x y = orbifoldBPZ x y * hyperbolicBPZ p q
  exact mul_comm _ _

private theorem actualInverse_transpose (D : LatticeData) :
    (actualInverse D).transpose = actualInverse D := by
  have hG : D.G.transpose = D.G := by
    apply Matrix.ext
    intro i j
    exact D.symmetric j i
  change (D.G⁻¹).transpose.map (Int.castRingHom ℂ) = (D.G⁻¹).map (Int.castRingHom ℂ)
  rw [Matrix.transpose_nonsing_inv, hG]

private theorem hyperbolicInverse_transpose : hyperbolicInverse.transpose = hyperbolicInverse := by
  apply Matrix.ext
  intro i j
  exact congrArg (fun z : ℤ => (z : ℂ)) (OrderedHyperbolicExtension.U_symmetric j i)

/-- The fixed and twisted stress-mode transposes combine on the real orbifold carrier. -/
theorem orbifoldBPZ_mode (m : ℤ) (x y : Orbifold) :
    orbifoldBPZ (orbifoldMode m x) y = orbifoldBPZ x (orbifoldMode (-m) y) := by
  simp only [orbifoldBPZ_apply, orbifoldMode, TwistedGround.OriginalOrbifoldConformal.L_fixed_apply,
    TwistedGround.OriginalOrbifoldConformal.L_twisted_apply]
  rw [sourcePairing_sugawaraMode leechData (actualInverse leechData)
    (actualInverse_transpose leechData) m x.1.val y.1.val,
    actual_stress_transpose leechData leech_spec.2.1 m x.2.val y.2.val]

/-- The hyperbolic Sugawara action uses the symmetric inverse in the ordered null basis. -/
theorem hyperbolicBPZ_mode (m : ℤ) (p q : Hyperbolic) :
    hyperbolicBPZ (hyperbolicMode m p) q = hyperbolicBPZ p (hyperbolicMode (-m) q) :=
  sourcePairing_sugawaraMode hyperbolicData hyperbolicInverse hyperbolicInverse_transpose m p q

/-- Opposite Virasoro modes are transpose on all algebraic critical matter states. -/
theorem matterBPZ_mode (m : ℤ) (x y : Matter) :
    matterBPZ (mode m x) y = matterBPZ x (mode (-m) y) := by
  induction x using TensorProduct.inductionOn generalizing y with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul x p =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul y q =>
      simp only [mode, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        map_add, matterBPZ_tmul, orbifoldBPZ_mode, hyperbolicBPZ_mode]

/-- The two actual hyperbolic charge summands pair only at opposite charge. -/
theorem matterBPZ_charge (x y : Orbifold) (a b : Charge hyperbolicData)
    (p q : Oscillator hyperbolicData) :
    matterBPZ (x ⊗ₜ[ℂ] Finsupp.single a p) (y ⊗ₜ[ℂ] Finsupp.single b q) =
      if b = -a then orbifoldBPZ x y * integerWick hyperbolicData p q else 0 := by
  rw [matterBPZ_tmul]
  change orbifoldBPZ x y * sourcePairing hyperbolicData
    (Finsupp.single a p) (Finsupp.single b q) = _
  rw [sourcePairing_single_single]
  split_ifs <;> simp

theorem fixedBPZ_symmetric : fixedBPZ.IsSymm :=
  (show (sourcePairing leechData).IsSymm from ⟨sourcePairing_symmetric leechData⟩).restrict _

theorem negativeBPZ_symmetric : negativeBPZ.IsSymm :=
  (actualForm_symmetric leechData leech_spec.2.1).restrict _

private theorem restrict_eigenspace_nondegenerate {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V) (T : Module.End ℂ V) (e : ℂ) (he : e * e = 1)
    (hT : Function.Involutive T) (hiso : ∀ x y, B (T x) (T y) = B x y)
    (hsym : B.IsSymm) (hB : B.Nondegenerate) :
    (B.restrict (LinearMap.ker (T - e • LinearMap.id))).Nondegenerate := by
  let W := LinearMap.ker (T - e • LinearMap.id)
  have left (x : W) (hr : ∀ w : W, B x.val w.val = 0) : x = 0 := by
    apply Subtype.ext
    change x.val = 0
    apply hB.1
    intro y
    have hx := x.property
    change T x.val - e • x.val = 0 at hx
    have hx' := sub_eq_zero.mp hx
    let p := (2 : ℂ)⁻¹ • (y + e • T y)
    have hp : p ∈ W := by
      change T p - e • p = 0
      apply sub_eq_zero.mpr
      calc
        T p = (2 : ℂ)⁻¹ • (T y + e • y) := by
          simp only [p, map_smul, map_add, hT y]
        _ = (2 : ℂ)⁻¹ • (e • (y + e • T y)) := by
          rw [smul_add e y, smul_smul, he, one_smul, add_comm (T y)]
        _ = e • p := smul_comm _ _ _
    have hflip : e * B x.val (T y) = B x.val y := by
      simpa only [hx', map_smul, LinearMap.smul_apply, smul_eq_mul] using hiso x.val y
    have htest : B x.val p = 0 := hr ⟨p, hp⟩
    simp only [p, map_add, map_smul, smul_eq_mul, hflip] at htest
    linear_combination htest
  refine ⟨left, fun x hx => left x ?_⟩
  intro y
  exact (hsym.eq x.val y.val).trans (hx y)

/-- Averaging with the actual Leech involution detects every nonzero fixed vector. -/
theorem fixedBPZ_nondegenerate : fixedBPZ.Nondegenerate := by
  have hsym : (sourcePairing leechData).IsSymm := ⟨sourcePairing_symmetric leechData⟩
  exact restrict_eigenspace_nondegenerate (sourcePairing leechData) (thetaLinear leechData)
    1 (by norm_num) (theta_involutive leechData) (sourcePairing_theta leechData) hsym
    (sourcePairing_nondegenerate leechData leech_spec.2.1)

private theorem actualParity_involutive (D : LatticeData) (hu : IsUnit D.G.det) :
    Function.Involutive (actualParity D hu) := by
  have heq : (actualParity D hu).comp (actualParity D hu) = LinearMap.id := by
    apply (actualAmbientBasis D hu).ext
    intro i
    change actualParity D hu (actualParity D hu (actualAmbientBasis D hu i)) = _
    rw [basis_parity, map_smul, basis_parity, smul_smul, ← mul_pow]
    norm_num
  exact LinearMap.congr_fun heq

private theorem actualForm_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (x y : ActualTensor D hu) :
    actualForm D hu (actualParity D hu x) (actualParity D hu y) = actualForm D hu x y := by
  have heq : (actualForm D hu).compl₁₂ (actualParity D hu) (actualParity D hu) =
      actualForm D hu := by
    apply (actualAmbientBasis D hu).ext
    intro i
    apply (actualAmbientBasis D hu).ext
    intro j
    simp only [LinearMap.compl₁₂_apply, basis_parity, map_smul, LinearMap.smul_apply, smul_eq_mul]
    by_cases h : oddWeight D i.1 = oddWeight D j.1
    · rw [h, ← mul_assoc, ← mul_pow]
      norm_num
    · have hzero := actualForm_oddGrade_orthogonal D hu
        (oddWeight D i.1 : ℤ) (oddWeight D j.1 : ℤ)
        (actualAmbientBasis D hu i) (actualAmbientBasis D hu j)
        (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu i.1 i.2)
        (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu j.1 j.2)
        (by exact_mod_cast h)
      rw [hzero, mul_zero, mul_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

/-- The original negative parity restriction has trivial left and right radicals. -/
theorem negativeBPZ_nondegenerate : negativeBPZ.Nondegenerate :=
  restrict_eigenspace_nondegenerate (actualForm leechData leech_spec.2.1)
    (actualParity leechData leech_spec.2.1) (-1) (by norm_num)
    (actualParity_involutive leechData leech_spec.2.1) (actualForm_parity leechData leech_spec.2.1)
    (actualForm_symmetric leechData leech_spec.2.1)
    (actualForm_nondegenerate leechData leech_spec.2.1)

#print axioms orbifoldBPZ_mode
#print axioms hyperbolicBPZ_mode
#print axioms matterBPZ_mode
#print axioms fixedBPZ_nondegenerate
#print axioms negativeBPZ_nondegenerate

end D5.S3.VertexAlgebra.OriginalOrbifoldMatterBPZ
