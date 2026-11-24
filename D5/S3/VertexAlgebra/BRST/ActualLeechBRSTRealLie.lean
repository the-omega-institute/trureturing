/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechBRSTRealLie
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechBRSTRealLie
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The coefficient-real Lie algebra and its signed relative BPZ form. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechBRSTCoefficientRealForm
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeInvariantForm
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic.Abel

/-!
The native momentum bracket and the signed native relative BPZ form descend to the
fixed space of coefficient conjugation. The real and imaginary projections exhibit
the complex Lie algebra as the sum of this fixed space and its imaginary multiple.

proof_shape: momentumConjugation_lie, momentumH1_real_decomposition,
  nativeRelativeBPZ_conjugation, momentumRealBPZ_nondegenerate: content
admission_basis: escape-witness
escape_witness: Quotient conjugation and the native zero-mode bracket agree on each
homogeneous pair. On the original carrier, conjugation of the fixed, twisted, plane
and ghost pairings survives the relative c₀ insertion and then passes to the quotient.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators ComplexConjugate DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane)
open ActualLeechOrbifoldModeRealForm (orbifoldConjugation)
open Lattice.ActualCoefficientRealForm (fixedKappa)
open LatticeGeneratingFieldLocality (Charge)
open RelativeCohomology (GradedCycles GradedBoundaries GradedCohomology)
open SourceBPZ.OriginalMatterHermitian (kappaCarrier sourcePairing_kappa)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open TwistedGround.ActualLeechTwistedTensorRealForm (actualForm_negativeConjugation)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open BcGhostBilinear (Bg Bg_signed_coefficient kappa kappa_apply kappa_c)
open NativeBPZ (orbifoldPairing matterPairing relativePairing)

open private matterConjugation matterConjugation_tmul planeConjugation ghostConjugation
  from D5.S3.VertexAlgebra.BRST.ActualLeechBRSTCoefficientRealForm
open private tensor_pairing_tmul
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZ

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "Cycles" => fun p : Momentum => GradedCycles planeFrame planeBasis p 1
local notation "Boundaries" => fun p : Momentum => GradedBoundaries planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H
local notation "RealMomentumH1" => RestrictScalars ℝ ℂ MomentumH1
local notation "κ" => coefficientConjugationMomentum

local instance (p : Momentum) : AddCommGroup (relativeShell p) := Submodule.addCommGroup _
local instance (p : Momentum) : AddCommGroup (Cycles p) := Submodule.addCommGroup _

/-- Covariance for the Lie bracket on the actual BRST momentum direct sum. -/
theorem momentumConjugation_lie (x y : MomentumH1) :
    κ ⁅x, y⁆ = ⁅κ x, κ y⁆ :=
  coefficientConjugationMomentum_bracket x y

/-- The pointwise fixed real Lie subalgebra of the native momentum algebra. -/
def momentumRealLie : LieSubalgebra ℝ RealMomentumH1 where
  carrier := {x | κ x = x}
  zero_mem' := coefficientConjugationMomentum.map_zero
  add_mem' := by
    intro x y hx hy
    change κ x = x at hx
    change κ y = y at hy
    change κ (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    let u := RestrictScalars.addEquiv ℝ ℂ MomentumH1 x
    change κ u = u at hx
    change κ ((r : ℂ) • u) = (r : ℂ) • u
    rw [map_smulₛₗ, Complex.conj_ofReal, hx]
  lie_mem' := by
    intro x y hx hy
    let u := RestrictScalars.addEquiv ℝ ℂ MomentumH1 x
    let v := RestrictScalars.addEquiv ℝ ℂ MomentumH1 y
    change κ u = u at hx
    change κ v = v at hy
    exact (momentumConjugation_lie u v).trans (congrArg₂ (fun a b : MomentumH1 => ⁅a, b⁆) hx hy)

@[simp] theorem mem_momentumRealLie (x : RealMomentumH1) :
    x ∈ momentumRealLie ↔ κ x = x := Iff.rfl

/-- The original complex cohomology class underlying a real class. -/
abbrev momentumRealValue (x : momentumRealLie) : MomentumH1 := x.val

@[simp] theorem momentumConjugation_realValue (x : momentumRealLie) :
    κ (momentumRealValue x) = momentumRealValue x :=
  x.property

private theorem two_mul_I_ne_zero : (2 * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero two_ne_zero Complex.I_ne_zero

/-- The fixed part (x + κx)/2. -/
def momentumRealPart (x : MomentumH1) : momentumRealLie :=
  ⟨(2 : ℂ)⁻¹ • (x + κ x), by
    change κ ((2 : ℂ)⁻¹ • (x + κ x)) = _
    have h : conj ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
      simp only [map_inv₀, Complex.conj_ofNat]
    rw [map_smulₛₗ, h, map_add, coefficientConjugationMomentum_involutive x, add_comm (κ x) x]⟩

/-- The fixed part (x - κx)/(2i). -/
def momentumImaginaryPart (x : MomentumH1) : momentumRealLie :=
  ⟨(2 * Complex.I : ℂ)⁻¹ • (x - κ x), by
    change κ ((2 * Complex.I : ℂ)⁻¹ • (x - κ x)) = _
    have h : conj ((2 * Complex.I : ℂ)⁻¹) = -(2 * Complex.I : ℂ)⁻¹ := by
      simp only [map_inv₀, map_mul, map_ofNat, Complex.conj_I, mul_neg, inv_neg]
    rw [map_smulₛₗ, h, map_sub, coefficientConjugationMomentum_involutive x, neg_smul,
      ← smul_neg, neg_sub]⟩

/-- Every original complex class is the sum of a fixed class and i times a fixed class. -/
theorem momentumH1_real_decomposition (x : MomentumH1) :
    x = momentumRealValue (momentumRealPart x) +
      Complex.I • momentumRealValue (momentumImaginaryPart x) := by
  change x = (2 : ℂ)⁻¹ • (x + κ x) + Complex.I • ((2 * Complex.I : ℂ)⁻¹ • (x - κ x))
  have hI : Complex.I * (2 * Complex.I : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
  have htwo : (2 : ℂ)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
  rw [smul_smul, hI, ← smul_add, add_add_sub_cancel,
    ← two_smul ℂ x, smul_smul, htwo, one_smul]

/-- Conjugating an equality of two splittings and subtracting determines the imaginary part. -/
theorem momentumH1_real_decomposition_unique (a b c d : momentumRealLie)
    (h : momentumRealValue a + Complex.I • momentumRealValue b =
      momentumRealValue c + Complex.I • momentumRealValue d) :
    (a, b) = (c, d) := by
  have hc := congrArg κ h
  simp only [map_add, map_smulₛₗ, Complex.conj_I, momentumConjugation_realValue] at hc
  have subtract_conjugate (u v : MomentumH1) :
      (u + Complex.I • v) - (u + (-Complex.I) • v) = (2 * Complex.I : ℂ) • v := by
    calc
      _ = Complex.I • v + Complex.I • v := by rw [neg_smul]; abel
      _ = _ := by rw [← add_smul, two_mul]
  have hs := congrArg₂ (fun x y : MomentumH1 => x - y) h hc
  have hb : momentumRealValue b = momentumRealValue d := by
    have hs' : (2 * Complex.I : ℂ) • momentumRealValue b =
        (2 * Complex.I : ℂ) • momentumRealValue d := by
      simpa only [subtract_conjugate] using hs
    have hinv : (2 * Complex.I : ℂ)⁻¹ * (2 * Complex.I) = 1 :=
      inv_mul_cancel₀ two_mul_I_ne_zero
    simpa only [smul_smul, hinv, one_smul] using
      congrArg (fun v : MomentumH1 => (2 * Complex.I : ℂ)⁻¹ • v) hs'
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext hb)
  exact add_right_cancel (by simpa only [hb] using h)

private theorem ghostBg_conjugation (x y : Fock) :
    Bg (kappa x) (kappa y) = conj (Bg x y) := by
  classical
  have support : (kappa x).support = x.support := by
    ext S
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, kappa_apply]
    exact not_congr (star_eq_zero (x := x S))
  have eps_real (S : Finset ℕ) : conj (BcGhostHermitian.eps S) = BcGhostHermitian.eps S := by
    exact BcGhostHermitian.eps_real S
  rw [Bg_signed_coefficient, Bg_signed_coefficient, support, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [kappa_apply, kappa_apply]
  change conj (x S) * BcGhostHermitian.eps S * conj (y (BcGhostHermitian.partner S)) = _
  simp only [map_mul, eps_real]

private theorem orbifoldPairing_conjugation (a b : ActualLeechOrbifoldMatter.Orbifold) :
    orbifoldPairing (orbifoldConjugation a) (orbifoldConjugation b) =
      conj (orbifoldPairing a b) := by
  rw [NativeBPZ.orbifoldPairing_apply, NativeBPZ.orbifoldPairing_apply, map_add]
  exact congrArg₂ (· + ·) (sourcePairing_kappa a.1.val b.1.val)
    (actualForm_negativeConjugation a.2 b.2)

private theorem matterPairing_conjugation (x y : Matter) :
    matterPairing (matterConjugation x) (matterConjugation y) = conj (matterPairing x y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u =>
    induction y using TensorProduct.inductionOn with
    | tmul b v =>
      simp only [matterConjugation_tmul, NativeBPZ.matterPairing, tensor_pairing_tmul,
        map_mul, orbifoldPairing_conjugation]
      rw [show planeConjugation u = kappaCarrier u from rfl,
        show planeConjugation v = kappaCarrier v from rfl, sourcePairing_kappa]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- Conjugation commutes with the original relative BPZ evaluation, including the c₀ insertion. -/
theorem relativePairing_coefficientConjugation (x y : ComplexState) :
    relativePairing (coefficientConjugation x) (coefficientConjugation y) =
      conj (relativePairing x y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a g =>
    induction y using TensorProduct.inductionOn with
    | tmul b h =>
      simp only [coefficientConjugation_tmul, NativeBPZ.relativePairing_tmul, map_mul,
        matterPairing_conjugation]
      change Bg (kappa g) (BcGhostFock.c 0 (kappa h)) * _ = _
      rw [← kappa_c, ghostBg_conjugation]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- Reality of the signed native BPZ form on the full momentum direct sum. -/
theorem nativeRelativeBPZ_conjugation (x y : MomentumH1) :
    nativeRelativeBPZ (κ x) (κ y) =
      conj (nativeRelativeBPZ x y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | of p x =>
    change nativeRelativeBPZ (κ (incl p x)) (κ y) =
      conj (nativeRelativeBPZ (incl p x) y)
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of q y =>
      change nativeRelativeBPZ (κ (incl p x)) (κ (incl q y)) =
        conj (nativeRelativeBPZ (incl p x) (incl q y))
      refine Submodule.Quotient.induction_on (Boundaries p) x fun a => ?_
      refine Submodule.Quotient.induction_on (Boundaries q) y fun b => ?_
      simp only [coefficientConjugationMomentum_incl, coefficientConjugationCohomology_mk,
        nativeRelativeBPZ_incl_mk, coefficientConjugationCycles_nativeValue,
        relativePairing_coefficientConjugation, map_neg]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- The real part of the signed native BPZ form on the fixed Lie algebra. -/
def momentumRealBPZ : LinearMap.BilinForm ℝ momentumRealLie where
  toFun x :=
    { toFun := fun y => (nativeRelativeBPZ (momentumRealValue x) (momentumRealValue y)).re
      map_add' := by
        intro y z
        change (nativeRelativeBPZ (momentumRealValue x)
          (momentumRealValue y + momentumRealValue z)).re = _
        rw [map_add, Complex.add_re]
      map_smul' := by
        intro r y
        change (nativeRelativeBPZ (momentumRealValue x) ((r : ℂ) • momentumRealValue y)).re =
          r • (nativeRelativeBPZ (momentumRealValue x) (momentumRealValue y)).re
        exact (congrArg Complex.re
          ((nativeRelativeBPZ (momentumRealValue x)).map_smul (r : ℂ)
            (momentumRealValue y))).trans (Complex.smul_re r _) }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change (nativeRelativeBPZ (momentumRealValue x + momentumRealValue y)
      (momentumRealValue z)).re =
        (nativeRelativeBPZ (momentumRealValue x) (momentumRealValue z)).re +
        (nativeRelativeBPZ (momentumRealValue y) (momentumRealValue z)).re
    exact (congrArg (fun f : MomentumH1 →ₗ[ℂ] ℂ => (f (momentumRealValue z)).re)
      (nativeRelativeBPZ.map_add (momentumRealValue x) (momentumRealValue y))).trans
        (Complex.add_re _ _)
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    change (nativeRelativeBPZ ((r : ℂ) • momentumRealValue x) (momentumRealValue y)).re =
      r • (nativeRelativeBPZ (momentumRealValue x) (momentumRealValue y)).re
    exact (congrArg (fun f : MomentumH1 →ₗ[ℂ] ℂ => (f (momentumRealValue y)).re)
      (nativeRelativeBPZ.map_smul (r : ℂ) (momentumRealValue x))).trans
        (Complex.smul_re r _)

/-- On fixed classes the original complex evaluation is the embedded real evaluation. -/
theorem ofReal_momentumRealBPZ (x y : momentumRealLie) :
    (momentumRealBPZ x y : ℂ) = nativeRelativeBPZ (momentumRealValue x) (momentumRealValue y) := by
  apply Complex.conj_eq_iff_re.mp
  simpa only [momentumConjugation_realValue] using
    (nativeRelativeBPZ_conjugation (momentumRealValue x) (momentumRealValue y)).symm

theorem momentumRealBPZ_symmetric : momentumRealBPZ.IsSymm := by
  constructor
  intro x y
  exact congrArg Complex.re
    (nativeRelativeBPZ_symmetric.eq (momentumRealValue x) (momentumRealValue y))

/-- The fixed space detects every complex class by the real and imaginary decomposition. -/
theorem momentumRealBPZ_nondegenerate : momentumRealBPZ.Nondegenerate := by
  have left (x : momentumRealLie) (hx : ∀ y : momentumRealLie, momentumRealBPZ x y = 0) :
      x = 0 := by
    apply Subtype.ext
    change momentumRealValue x = 0
    apply nativeRelativeBPZ_nondegenerate.1
    intro y
    have hfixed (z : momentumRealLie) :
        nativeRelativeBPZ (momentumRealValue x) (momentumRealValue z) = 0 := by
      rw [← ofReal_momentumRealBPZ, hx, Complex.ofReal_zero]
    calc
      nativeRelativeBPZ (momentumRealValue x) y =
          nativeRelativeBPZ (momentumRealValue x) (momentumRealValue (momentumRealPart y) +
            Complex.I • momentumRealValue (momentumImaginaryPart y)) :=
        congrArg (nativeRelativeBPZ (momentumRealValue x)) (momentumH1_real_decomposition y)
      _ = 0 := by simp only [map_add, map_smul, hfixed, smul_zero, add_zero]
  refine ⟨left, ?_⟩
  intro x hx
  exact left x fun y => (momentumRealBPZ_symmetric.eq x y).trans (hx y)

/-- The inherited real bracket preserves the real BPZ form. -/
theorem momentumRealBPZ_invariant (x y z : momentumRealLie) :
    momentumRealBPZ ⁅x, y⁆ z = momentumRealBPZ x ⁅y, z⁆ := by
  exact congrArg Complex.re
    (nativeRelativeBPZ_invariant (momentumRealValue x) (momentumRealValue y) (momentumRealValue z))

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
