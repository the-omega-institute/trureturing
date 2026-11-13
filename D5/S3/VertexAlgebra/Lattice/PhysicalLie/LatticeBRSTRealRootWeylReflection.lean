/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootWeylReflection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootWeylReflection
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Actual physical real-root Weyl automorphism and full charge-fiber equivalence. -/

/-!
SOURCE_ONLY_UNCOMPILED. All proof bodies below are authored candidates, not
native elaboration or kernel evidence. The separately implemented exact
localExpLieEquiv interface is a PENDING dependency, not an axiom in this file.
The repaired positive-root integrability and independently source-reviewed
Cartan-character suppliers also retain their UNCOMPILED status.

All carriers, operators and pairings are the original suppliers. In particular
C is the original global BRST quotient, Ph is its literal physicalImage, and
Fib is Ph intersected with the range of the original charge inclusion. Incoming
boundary primitives in BOTH quotient slots remain arbitrary original State D.
No new physical hypothesis, finite-dimensional whole-image assumption, or
global involutivity assertion about the Weyl automorphism is used.

Attribution: original lattice fields retain Bakalov--Kac, Carnahan and Kytölä
attribution; BRST/current suppliers retain Becchi--Rouet--Stora--Tyutin,
Kato--Ogawa and Lian--Zuckerman attribution. The sl2 Weyl calculation is the
classical three-exponential construction. Mathlib supplies Lie derivations,
finite sums and linear algebra; Batteries supplies access to sealed private
lemmas. No literature-novelty claim or completion of string theory is made.
-/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTLocallyNilpotentExponential
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalDuality
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeRootBracket
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTCartanChargeCharacter
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

open private bilinear_sub_right from
  D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private bilinear_zsmul_right from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
open private gamma_expansion gamma_neg charge_energy_neg from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeRootBracket

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootWeylReflection

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeSugawaraCurrents (gramComplex)
open LatticePositiveEnergy (chargeEnergy two_chargeEnergy chargeEnergy_zero)
open LatticeBRSTCohomologyField (Cohomology)
open LatticeBRSTNeutralPhysicalCartan (gamma cartanPhysicalImage cartan_adjoint)
open LatticeBRSTPhysicalLie (physicalImage)
open LatticeBRSTPhysicalChargeFiber (physicalChargeFiber oppositePairing)
open LatticeBRSTPhysicalDuality (nonzeroChargeDuality)
open LatticeBRSTGlobalPhysicalBilinear (physicalBilinearForm)
open LatticeBRSTOppositeRootBracket (opposite_charge_bracket)
open LatticeBRSTPositiveRootIntegrability (positive_root_adjoint_locally_nilpotent)
open LatticeBRSTCartanChargeCharacter (mem_physicalChargeFiber_iff_cartan_adjoint)
open LatticeBRSTLocallyNilpotentExponential
  (localExpLieEquiv localExpLieEquiv_apply_of_bound)

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "Ph" => physicalImage D H h26 hHG hGH
local notation "Fib" => physicalChargeFiber D H h26 hHG hGH
local notation "hC" => cartanPhysicalImage D H h26 hHG hGH

def chargeReflection (alpha beta : Charge D) : Charge D :=
  beta - bilinear D alpha beta • alpha

def cartanReflection (alpha : Charge D) (v : Fin D.rank → ℂ) : Fin D.rank → ℂ :=
  v - gamma D v alpha • (fun i => (alpha i : ℂ))

private theorem root_length_two (alpha : Charge D)
    (hα : chargeEnergy D alpha = 1) : bilinear D alpha alpha = 2 := by
  rw [← two_chargeEnergy D alpha, hα]
  norm_num

private theorem charge_ne_zero_of_energy_one (alpha : Charge D)
    (hα : chargeEnergy D alpha = 1) : alpha ≠ 0 := by
  intro hz
  have : (0 : ℤ) = 1 := by simpa only [hz, chargeEnergy_zero] using hα
  norm_num at this

private theorem gamma_charge (alpha beta : Charge D) :
    gamma D (fun i => (alpha i : ℂ)) beta = (bilinear D alpha beta : ℂ) := by
  rw [gamma_expansion]
  simp only [bilinear, Int.cast_sum, Int.cast_mul]

private theorem gamma_sub (u v : Fin D.rank → ℂ) (beta : Charge D) :
    gamma D (u - v) beta = gamma D u beta - gamma D v beta := by
  simp only [gamma, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem gamma_smul (t : ℂ) (v : Fin D.rank → ℂ) (beta : Charge D) :
    gamma D (t • v) beta = t * gamma D v beta := by
  simp only [gamma, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem gamma_reflect_cartan (alpha beta : Charge D)
    (v : Fin D.rank → ℂ) :
    gamma D (cartanReflection D alpha v) beta =
      gamma D v beta - gamma D v alpha * (bilinear D alpha beta : ℂ) := by
  rw [cartanReflection, gamma_sub, gamma_smul, gamma_charge]

private theorem gamma_reflect_charge (alpha beta : Charge D)
    (v : Fin D.rank → ℂ) :
    gamma D v (chargeReflection D alpha beta) =
      gamma D v beta - (bilinear D alpha beta : ℂ) * gamma D v alpha := by
  unfold gamma chargeReflection
  simp only [bilinear_sub_right, bilinear_zsmul_right, Int.cast_sub,
    Int.cast_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem gamma_reflection_compatibility (alpha beta : Charge D)
    (v : Fin D.rank → ℂ) :
    gamma D (cartanReflection D alpha v) beta =
      gamma D v (chargeReflection D alpha beta) := by
  rw [gamma_reflect_cartan, gamma_reflect_charge]
  ring

private theorem chargeReflection_involutive (alpha : Charge D)
    (hα : chargeEnergy D alpha = 1) (beta : Charge D) :
    chargeReflection D alpha (chargeReflection D alpha beta) = beta := by
  have hb : bilinear D alpha (chargeReflection D alpha beta) =
      -bilinear D alpha beta := by
    rw [chargeReflection, bilinear_sub_right, bilinear_zsmul_right,
      root_length_two D alpha hα]
    ring
  change chargeReflection D alpha beta -
    bilinear D alpha (chargeReflection D alpha beta) • alpha = beta
  rw [hb, chargeReflection]
  module

private theorem cartanReflection_involutive (alpha : Charge D)
    (hα : chargeEnergy D alpha = 1) (v : Fin D.rank → ℂ) :
    cartanReflection D alpha (cartanReflection D alpha v) = v := by
  have hg : gamma D (cartanReflection D alpha v) alpha = -gamma D v alpha := by
    rw [gamma_reflect_cartan, root_length_two D alpha hα]
    push_cast
    ring
  change cartanReflection D alpha v -
    gamma D (cartanReflection D alpha v) alpha • (fun i => (alpha i : ℂ)) = v
  rw [hg, cartanReflection]
  module

/- A fiber element is ⟨(e : C), he⟩. Membership he already includes BOTH
   physical-image and inclusion-range membership; no additional pair is added. -/
private theorem opposite_functional_ne_zero
    (alpha : Charge D) (hα0 : alpha ≠ 0)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0) :
    oppositePairing D H h26 hHG hGH alpha (⟨(e : C), he⟩ : Fib alpha) ≠ 0 := by
  intro hz
  have heq : (⟨(e : C), he⟩ : Fib alpha) = 0 := by
    apply (nonzeroChargeDuality D H h26 hHG hGH alpha hα0).injective
    change oppositePairing D H h26 hHG hGH alpha (⟨(e : C), he⟩ : Fib alpha) =
      oppositePairing D H h26 hHG hGH alpha 0
    simpa only [map_zero] using hz
  apply he0
  exact Subtype.ext (congrArg Subtype.val heq)

private theorem exists_opposite_pairing_ne_zero
    (alpha : Charge D) (hα0 : alpha ≠ 0)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0) :
    ∃ z : Fib (-alpha), oppositePairing D H h26 hHG hGH alpha
      (⟨(e : C), he⟩ : Fib alpha) z ≠ 0 := by
  classical
  by_contra hn
  apply opposite_functional_ne_zero D H h26 hHG hGH alpha hα0 e he he0
  apply LinearMap.ext
  intro z
  have hz : oppositePairing D H h26 hHG hGH alpha
      (⟨(e : C), he⟩ : Fib alpha) z = 0 := by
    by_contra hz
    exact hn ⟨z, hz⟩
  simpa only [LinearMap.zero_apply] using hz

private def oppositeFiber
    (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0) : Fib (-alpha) :=
  let z := Classical.choose (exists_opposite_pairing_ne_zero D H h26 hHG hGH
    alpha (charge_ne_zero_of_energy_one D alpha hα) e he he0)
  let c := oppositePairing D H h26 hHG hGH alpha (⟨(e : C), he⟩ : Fib alpha) z
  (-c)⁻¹ • z

/-- The original opposite physical root, normalized by the signed actual
pairing: if c = B(e,z), this is the literal image of (-c)⁻¹ • z. -/
def normalizedOpposite
    (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0) : Ph :=
  let f := oppositeFiber D H h26 hHG hGH alpha hα e he he0
  ⟨(f : C), f.property.1⟩

private theorem normalizedOpposite_mem
    (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0) :
    (normalizedOpposite D H h26 hHG hGH alpha hα e he he0 : C) ∈ Fib (-alpha) :=
  (oppositeFiber D H h26 hHG hGH alpha hα e he he0).property

private theorem normalizedOpposite_pairing
    (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0) :
    physicalBilinearForm D H h26 hHG hGH e
      (normalizedOpposite D H h26 hHG hGH alpha hα e he he0) = -1 := by
  let z := Classical.choose (exists_opposite_pairing_ne_zero D H h26 hHG hGH
    alpha (charge_ne_zero_of_energy_one D alpha hα) e he he0)
  let φ := oppositePairing D H h26 hHG hGH alpha (⟨(e : C), he⟩ : Fib alpha)
  let c := φ z
  have hc : c ≠ 0 := Classical.choose_spec
    (exists_opposite_pairing_ne_zero D H h26 hHG hGH
      alpha (charge_ne_zero_of_energy_one D alpha hα) e he he0)
  change φ ((-c)⁻¹ • z) = -1
  rw [map_smul]
  change (-c)⁻¹ * c = -1
  field_simp [hc] <;> ring

/-- The signed normalization produces a nonzero actual physical opposite root. -/
theorem normalizedOpposite_ne_zero
    (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0) :
    normalizedOpposite D H h26 hHG hGH alpha hα e he he0 ≠ 0 := by
  intro hz
  have hp := normalizedOpposite_pairing D H h26 hHG hGH alpha hα e he he0
  rw [hz, map_zero] at hp
  norm_num at hp

/- Mathlib inner x sends y to [y,x]. Negation is essential here. -/
private def leftAdjoint (x : Ph) : LieDerivation ℂ Ph Ph :=
  -(LieDerivation.inner ℂ Ph Ph x)

private theorem leftAdjoint_apply (x y : Ph) :
    leftAdjoint D H h26 hHG hGH x y = ⁅x, y⁆ := by
  change -⁅y, x⁆ = ⁅x, y⁆
  exact lie_skew x y

private theorem leftAdjoint_pow_apply (x y : Ph) (N : ℕ) :
    ((leftAdjoint D H h26 hHG hGH x).toLinearMap ^ N) y =
      ((fun z : Ph => ⁅x, z⁆)^[N]) y := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply]
    change leftAdjoint D H h26 hHG hGH x
      (((leftAdjoint D H h26 hHG hGH x).toLinearMap ^ N) y) = _
    rw [leftAdjoint_apply, ih, Function.iterate_succ_apply']

private theorem adjoint_locally_nilpotent (alpha : Charge D)
    (hα : 0 < chargeEnergy D alpha) (x : Ph) (hx : (x : C) ∈ Fib alpha) :
    ∀ y : Ph, ∃ N : ℕ, ((leftAdjoint D H h26 hHG hGH x).toLinearMap ^ N) y = 0 := by
  intro y
  obtain ⟨N, hN⟩ := positive_root_adjoint_locally_nilpotent
    D H h26 hHG hGH alpha hα x hx y
  exact ⟨N, (leftAdjoint_pow_apply D H h26 hHG hGH x y N).trans hN⟩

private def rootExp (alpha : Charge D) (hα : 0 < chargeEnergy D alpha)
    (x : Ph) (hx : (x : C) ∈ Fib alpha) (t : ℂ) : Ph ≃ₗ⁅ℂ⁆ Ph :=
  localExpLieEquiv (leftAdjoint D H h26 hHG hGH x)
    (adjoint_locally_nilpotent D H h26 hHG hGH alpha hα x hx) t

/- These finite evaluations use ONLY the sealed exact generic interface.
   They are on the original Ph and are all consumed in the sl2 calculation. -/
private theorem exp_bound_one (A : LieDerivation ℂ Ph Ph)
    (hloc : ∀ x : Ph, ∃ N : ℕ, (A.toLinearMap ^ N) x = 0)
    (t : ℂ) (x : Ph) (hx : A x = 0) :
    localExpLieEquiv A hloc t x = x := by
  rw [localExpLieEquiv_apply_of_bound A hloc t x 1 (by simpa using hx)]
  simp

private theorem exp_bound_two (A : LieDerivation ℂ Ph Ph)
    (hloc : ∀ x : Ph, ∃ N : ℕ, (A.toLinearMap ^ N) x = 0)
    (t : ℂ) (x : Ph) (hx : A (A x) = 0) :
    localExpLieEquiv A hloc t x = x + t • A x := by
  have hb : (A.toLinearMap ^ 2) x = 0 := by
    simpa [pow_succ, Module.End.mul_apply] using hx
  rw [localExpLieEquiv_apply_of_bound A hloc t x 2 hb]
  simp [Finset.sum_range_succ]

private theorem exp_bound_three (A : LieDerivation ℂ Ph Ph)
    (hloc : ∀ x : Ph, ∃ N : ℕ, (A.toLinearMap ^ N) x = 0)
    (t : ℂ) (x : Ph) (hx : A (A (A x)) = 0) :
    localExpLieEquiv A hloc t x = x + t • A x + (t ^ 2 / 2) • A (A x) := by
  have hb : (A.toLinearMap ^ 3) x = 0 := by
    simpa [pow_succ, Module.End.mul_apply] using hx
  rw [localExpLieEquiv_apply_of_bound A hloc t x 3 hb]
  norm_num [Finset.sum_range_succ, pow_succ, Module.End.mul_apply,
    Nat.factorial] <;> module

section Root

variable (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
  (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0)

local notation "fα" => normalizedOpposite D H h26 hHG hGH alpha hα e he he0
local notation "hαC" => hC (fun i => (alpha i : ℂ))

include hα in
private theorem opposite_energy_one : chargeEnergy D (-alpha) = 1 := by
  rw [charge_energy_neg, hα]

include hα in
private theorem root_positive : 0 < chargeEnergy D alpha := by omega

include hα in
private theorem opposite_positive : 0 < chargeEnergy D (-alpha) := by
  rw [opposite_energy_one D alpha hα]
  norm_num

include hα he he0

private theorem sl2_ef : ⁅e, fα⁆ = hαC := by
  have hp := normalizedOpposite_pairing D H h26 hHG hGH alpha hα e he he0
  rw [opposite_charge_bracket D H h26 hHG hGH alpha e fα he.2
    (normalizedOpposite_mem D H h26 hHG hGH alpha hα e he he0).2, hp]
  simp

private theorem sl2_he : ⁅hαC, e⁆ = (2 : ℂ) • e := by
  rw [cartan_adjoint D H h26 hHG hGH _ alpha e he.2,
    gamma_charge, root_length_two D alpha hα]
  norm_num

private theorem sl2_hf : ⁅hαC, fα⁆ = (-2 : ℂ) • fα := by
  rw [cartan_adjoint D H h26 hHG hGH _ (-alpha) fα
    (normalizedOpposite_mem D H h26 hHG hGH alpha hα e he he0).2,
    gamma_neg, gamma_charge, root_length_two D alpha hα]
  norm_num

private theorem sl2_fe : ⁅fα, e⁆ = -hαC := by
  rw [← lie_skew fα e, sl2_ef D H h26 hHG hGH alpha hα e he he0]

private theorem sl2_eh : ⁅e, hαC⁆ = (-2 : ℂ) • e := by
  rw [← lie_skew e hαC, sl2_he D H h26 hHG hGH alpha hα e he he0]
  module

private theorem sl2_fh : ⁅fα, hαC⁆ = (2 : ℂ) • fα := by
  rw [← lie_skew fα hαC, sl2_hf D H h26 hHG hGH alpha hα e he he0]
  module

local notation "Eα" => rootExp D H h26 hHG hGH alpha
  (root_positive D alpha hα) e he 1
local notation "Fα" => rootExp D H h26 hHG hGH (-alpha)
  (opposite_positive D alpha hα) fα
  (normalizedOpposite_mem D H h26 hHG hGH alpha hα e he he0) (-1)

private theorem exp_e_e : Eα e = e := by
  unfold rootExp
  apply exp_bound_one
  rw [leftAdjoint_apply, lie_self]

private theorem exp_f_f : Fα fα = fα := by
  unfold rootExp
  apply exp_bound_one
  rw [leftAdjoint_apply, lie_self]

private theorem exp_e_h : Eα hαC = hαC - (2 : ℂ) • e := by
  unfold rootExp
  have hz : (leftAdjoint D H h26 hHG hGH e)
      ((leftAdjoint D H h26 hHG hGH e) hαC) = 0 := by
    simp only [leftAdjoint_apply, sl2_eh D H h26 hHG hGH alpha hα e he he0,
      lie_smul, lie_self, smul_zero]
  rw [exp_bound_two _ _ 1 hαC hz,
    leftAdjoint_apply, sl2_eh D H h26 hHG hGH alpha hα e he he0]
  module

private theorem exp_f_h : Fα hαC = hαC - (2 : ℂ) • fα := by
  unfold rootExp
  have hz : (leftAdjoint D H h26 hHG hGH fα)
      ((leftAdjoint D H h26 hHG hGH fα) hαC) = 0 := by
    simp only [leftAdjoint_apply, sl2_fh D H h26 hHG hGH alpha hα e he he0,
      lie_smul, lie_self, smul_zero]
  rw [exp_bound_two _ _ (-1) hαC hz,
    leftAdjoint_apply, sl2_fh D H h26 hHG hGH alpha hα e he he0]
  module

private theorem exp_e_f : Eα fα = fα + hαC - e := by
  unfold rootExp
  have hz : (leftAdjoint D H h26 hHG hGH e)
      ((leftAdjoint D H h26 hHG hGH e)
        ((leftAdjoint D H h26 hHG hGH e) fα)) = 0 := by
    simp only [leftAdjoint_apply, sl2_ef D H h26 hHG hGH alpha hα e he he0,
      sl2_eh D H h26 hHG hGH alpha hα e he he0,
      lie_smul, lie_self, smul_zero]
  rw [exp_bound_three _ _ 1 fα hz]
  simp only [leftAdjoint_apply, sl2_ef D H h26 hHG hGH alpha hα e he he0,
    sl2_eh D H h26 hHG hGH alpha hα e he he0]
  module

private theorem exp_f_e : Fα e = e + hαC - fα := by
  unfold rootExp
  have hz : (leftAdjoint D H h26 hHG hGH fα)
      ((leftAdjoint D H h26 hHG hGH fα)
        ((leftAdjoint D H h26 hHG hGH fα) e)) = 0 := by
    simp only [leftAdjoint_apply, sl2_fe D H h26 hHG hGH alpha hα e he he0,
      lie_neg, sl2_fh D H h26 hHG hGH alpha hα e he he0,
      lie_smul, lie_self, smul_zero, neg_zero]
  rw [exp_bound_three _ _ (-1) e hz]
  simp only [leftAdjoint_apply, sl2_fe D H h26 hHG hGH alpha hα e he he0,
    lie_neg, sl2_fh D H h26 hHG hGH alpha hα e he he0]
  module

private theorem exp_e_cartan (v : Fin D.rank → ℂ) :
    Eα (hC v) = hC v - gamma D v alpha • e := by
  unfold rootExp
  have had : ⁅e, hC v⁆ = -gamma D v alpha • e := by
    rw [← lie_skew e (hC v), cartan_adjoint D H h26 hHG hGH v alpha e he.2]
    module
  have hz : (leftAdjoint D H h26 hHG hGH e)
      ((leftAdjoint D H h26 hHG hGH e) (hC v)) = 0 := by
    simp only [leftAdjoint_apply, had, lie_smul, lie_self, smul_zero]
  rw [exp_bound_two _ _ 1 (hC v) hz, leftAdjoint_apply, had]
  module

private theorem exp_f_cartan (v : Fin D.rank → ℂ) :
    Fα (hC v) = hC v - gamma D v alpha • fα := by
  unfold rootExp
  have had : ⁅fα, hC v⁆ = gamma D v alpha • fα := by
    rw [← lie_skew fα (hC v), cartan_adjoint D H h26 hHG hGH v (-alpha) fα
      (normalizedOpposite_mem D H h26 hHG hGH alpha hα e he he0).2, gamma_neg]
    module
  have hz : (leftAdjoint D H h26 hHG hGH fα)
      ((leftAdjoint D H h26 hHG hGH fα) (hC v)) = 0 := by
    simp only [leftAdjoint_apply, had, lie_smul, lie_self, smul_zero]
  rw [exp_bound_two _ _ (-1) (hC v) hz, leftAdjoint_apply, had]
  module

/-- On the ENTIRE original physical Lie image, with no extra local-nilpotence
premise. Trans acts first by its left factor, so the displayed product acts as
Exp(ad e) (Exp(-ad f) (Exp(ad e) c)). -/
def WeylAlpha : Ph ≃ₗ⁅ℂ⁆ Ph :=
  Eα.trans (Fα.trans Eα)

/-- The actual root e is taken to the negative normalized opposite root. -/
theorem WeylAlpha_root_e :
    WeylAlpha D H h26 hHG hGH alpha hα e he he0 e = -fα := by
  change Eα (Fα (Eα e)) = -fα
  rw [exp_e_e D H h26 hHG hGH alpha hα e he he0,
    exp_f_e D H h26 hHG hGH alpha hα e he he0,
    map_sub, map_add, exp_e_e D H h26 hHG hGH alpha hα e he he0,
    exp_e_h D H h26 hHG hGH alpha hα e he he0,
    exp_e_f D H h26 hHG hGH alpha hα e he he0]
  module

/-- The normalized actual opposite root is taken to -e. -/
theorem WeylAlpha_root_f :
    WeylAlpha D H h26 hHG hGH alpha hα e he he0 fα = -e := by
  change Eα (Fα (Eα fα)) = -e
  rw [exp_e_f D H h26 hHG hGH alpha hα e he he0,
    map_sub, map_add, exp_f_f D H h26 hHG hGH alpha hα e he he0,
    exp_f_h D H h26 hHG hGH alpha hα e he he0,
    exp_f_e D H h26 hHG hGH alpha hα e he he0]
  have hz : fα + (hαC - (2 : ℂ) • fα) - (e + hαC - fα) = -e := by module
  rw [hz, map_neg, exp_e_e D H h26 hHG hGH alpha hα e he he0]

/-- Conjugation on EVERY complex Cartan vector, not only the root coroot. -/
theorem WeylAlpha_cartan (v : Fin D.rank → ℂ) :
    WeylAlpha D H h26 hHG hGH alpha hα e he he0 (hC v) =
      hC (cartanReflection D alpha v) := by
  change Eα (Fα (Eα (hC v))) = _
  rw [exp_e_cartan D H h26 hHG hGH alpha hα e he he0 v,
    map_sub, map_smul, exp_f_cartan D H h26 hHG hGH alpha hα e he he0 v,
    exp_f_e D H h26 hHG hGH alpha hα e he he0]
  have hz : hC v - gamma D v alpha • fα -
      gamma D v alpha • (e + hαC - fα) =
      hC v - gamma D v alpha • e - gamma D v alpha • hαC := by module
  rw [hz, map_sub, map_sub, map_smul, map_smul,
    exp_e_cartan D H h26 hHG hGH alpha hα e he he0 v,
    exp_e_e D H h26 hHG hGH alpha hα e he he0,
    exp_e_h D H h26 hHG hGH alpha hα e he he0]
  rw [cartanReflection, map_sub, map_smul]
  module

private theorem WeylAlpha_cartan_reflected (v : Fin D.rank → ℂ) :
    WeylAlpha D H h26 hHG hGH alpha hα e he he0
      (hC (cartanReflection D alpha v)) = hC v := by
  rw [WeylAlpha_cartan, cartanReflection_involutive D alpha hα v]

/-- Full original charge-fiber equivalence for EVERY beta, including beta=0,
and every c in the literal global physical image. No assertion W²=id is used. -/
theorem WeylAlpha_mem_fiber_iff (beta : Charge D) (c : Ph) :
    (WeylAlpha D H h26 hHG hGH alpha hα e he he0 c : C) ∈
        Fib (chargeReflection D alpha beta) ↔ (c : C) ∈ Fib beta := by
  let W := WeylAlpha D H h26 hHG hGH alpha hα e he he0
  have hW (v : Fin D.rank → ℂ) :
      W (hC (cartanReflection D alpha v)) = hC v :=
    WeylAlpha_cartan_reflected D H h26 hHG hGH alpha hα e he he0 v
  have hWv (v : Fin D.rank → ℂ) : W (hC v) = hC (cartanReflection D alpha v) :=
    WeylAlpha_cartan D H h26 hHG hGH alpha hα e he he0 v
  have hchar (v : Fin D.rank → ℂ) :
      gamma D v (chargeReflection D alpha beta) =
        gamma D (cartanReflection D alpha v) beta :=
    (gamma_reflection_compatibility D alpha beta v).symm
  constructor
  · intro hc
    apply (mem_physicalChargeFiber_iff_cartan_adjoint D H h26 hHG hGH beta c).mpr
    intro v
    apply W.injective
    rw [W.map_lie, W.map_smul]
    change ⁅W (hC v), W c⁆ = gamma D v beta • W c
    rw [hWv v]
    have hev := (mem_physicalChargeFiber_iff_cartan_adjoint D H h26 hHG hGH
      (chargeReflection D alpha beta) (W c)).mp hc
    rw [hev (cartanReflection D alpha v),
      gamma_reflection_compatibility D alpha (chargeReflection D alpha beta) v,
      chargeReflection_involutive D alpha hα beta]
  · intro hc
    apply (mem_physicalChargeFiber_iff_cartan_adjoint D H h26 hHG hGH
      (chargeReflection D alpha beta) (W c)).mpr
    intro v
    calc
      ⁅hC v, W c⁆ = W ⁅hC (cartanReflection D alpha v), c⁆ := by
        rw [W.map_lie, hW v]
      _ = W (gamma D (cartanReflection D alpha v) beta • c) := by
        rw [(mem_physicalChargeFiber_iff_cartan_adjoint D H h26 hHG hGH beta c).mp
          hc (cartanReflection D alpha v)]
      _ = gamma D v (chargeReflection D alpha beta) • W c := by
        rw [W.map_smul, hchar v]

end Root
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootWeylReflection
