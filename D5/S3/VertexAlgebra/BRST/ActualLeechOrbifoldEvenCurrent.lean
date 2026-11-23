/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldEvenCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldEvenCurrent
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: An even native zero mode is a derivation on every original tensor mode. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracketIdentities
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra

/-! The all-state Leech Borcherds law supplies the first leg of the finite tensor shuffle. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechHyperbolic (leechData leech_spec)
open TwistedGround.Orbifold
open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private SignedLaw tensor_zero_mode
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldModeSuperderivation
open private rightLift_tmul from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private assocY_tmul assocParity reassoc_parity
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private parity_square from D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

private abbrev PlaneGhost := LatticeMatterGhostCoupling.State hyperbolicPlane
local notation "orb" => modesOfStateField (OriginalOrbifoldField.Y leechData leechUnit leechPosDef)
local notation "plane" => modesOfStateField (LatticeMatterGhostStateField.Y hyperbolicPlane)
local notation "tensor" => modesOfStateField assocY
local notation "par" => LatticeMatterGhostStateField.parity hyperbolicPlane

private theorem orb_law (a w c : Orbifold) : SignedLaw orb 1 a w c := by
  intro p q r
  have h := (ActualLeechExtensionVertexAlgebra.leechVertexAlgebra.borcherds a w c p q r).2.2.2
  simpa only [iterate, modesOfStateField, LinearMap.comp_apply, LinearMap.proj_apply,
    ActualLeechExtensionVertexAlgebra.stateField_eq, mul_one] using h

private theorem plane_even_law (b x y : PlaneGhost) (hb : par b = b) :
    SignedLaw plane 1 b x y := by
  intro p q r
  have law := (LatticeMatterGhostBorcherds.borcherds hyperbolicPlane b x y p q r).2.2.2.2
  change iterate plane b x y p q r = ∑ᶠ t : ℕ,
    (((-1 : ℂ)^t) * integerBinomial r t) •
      (plane (p+r-t) b (plane (q+t) x y) - epsilon r •
        (plane (q+r-t) x (plane (p+t) ((2 : ℂ)⁻¹ • (b + par b)) y) +
          plane (q+r-t) (par x) (plane (p+t) ((2 : ℂ)⁻¹ • (b - par b)) y))) at law
  have even : (2 : ℂ)⁻¹ • (b + par b) = b := by rw [hb]; module
  have odd : (2 : ℂ)⁻¹ • (b - par b) = 0 := by rw [hb, sub_self, smul_zero]
  simpa only [even, odd, map_zero, LinearMap.zero_apply, add_zero, mul_one] using law

private def planeEven : Module.End ℂ PlaneGhost := (2 : ℂ)⁻¹ • (1 + par)

private theorem planeEven_fixed (x : PlaneGhost) : par (planeEven x) = planeEven x := by
  change par ((2 : ℂ)⁻¹ • (x + par x)) = (2 : ℂ)⁻¹ • (x + par x)
  rw [map_smul, map_add, parity_square, add_comm (par x)]

private theorem assoc_even_derivation (n : ℤ) (a x y : AssocState) :
    let e := rightLift planeEven a
    tensor 0 e (tensor n x y) = tensor n (tensor 0 e x) y + tensor n x (tensor 0 e y) := by
  dsimp only
  induction a using TensorProduct.inductionOn with
  | tmul u b =>
    rw [rightLift_tmul]
    induction x using TensorProduct.inductionOn with
    | tmul v c =>
      induction y using TensorProduct.inductionOn with
      | tmul w d =>
        have law := tensor_zero_mode (T := tensor) (lowerTruncated_modesOfStateField _)
          (lowerTruncated_modesOfStateField _) assocY_tmul
          (orb_law u v w) (plane_even_law (planeEven b) c d (planeEven_fixed b)) n
        rw [one_smul] at law
        exact sub_eq_iff_eq_add.mp law
      | add x y hx hy =>
        simp only [map_add, hx, hy]
        abel
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]
      abel
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]
    abel

private theorem assoc_even_projection (a : AssocState) :
    rightLift planeEven a = (2 : ℂ)⁻¹ • (a + assocParity a) := by
  have h : rightLift planeEven = (2 : ℂ)⁻¹ • (1 + assocParity) := by
    simp only [planeEven, assocParity, map_smul, map_add, map_one]
  exact LinearMap.congr_fun h a

/-- The original zero mode of an even state acts on every original integer mode. -/
theorem even_zero_mode (n : ℤ) (a x y : ComplexState) (ha : originalParity a = a) :
    originalMode 0 a (originalMode n x y) =
      originalMode n (originalMode 0 a x) y + originalMode n x (originalMode 0 a y) := by
  have ha' : assocParity (reassoc a) = reassoc a :=
    (reassoc_parity a).symm.trans (congrArg reassoc ha)
  have h : rightLift planeEven (reassoc a) = reassoc a := by
    rw [assoc_even_projection, ha']
    module
  apply reassoc.injective
  rw [map_add, reassoc_originalMode, reassoc_originalMode, reassoc_originalMode,
    reassoc_originalMode, reassoc_originalMode, reassoc_originalMode]
  simpa only [h, modesOfStateField, LinearMap.comp_apply, LinearMap.proj_apply] using
    assoc_even_derivation n (reassoc a) (reassoc x) (reassoc y)

/-- The even current law used for the relative Jacobi primitive is unconditional. -/
theorem even_current : EvenCurrentLaw := by
  intro u v w hu _
  exact even_zero_mode 0 (B u) (B v) w (even_B_of_degree_one hu)

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
