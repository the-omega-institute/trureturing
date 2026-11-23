/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldEvenCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldEvenCurrent
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: An even native zero mode is a derivation on every original tensor mode. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracketIdentities
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.DirectSum.Module

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

section MomentumSum

open scoped DirectSum
open LatticeGeneratingFieldLocality (Charge)
open RelativeCohomology (GradedCycles GradedBoundaries GradedCohomology)
open private nativeValue_injective native_add native_cycleCurrent native_degree
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "Cycles" => fun p : Momentum => GradedCycles planeFrame planeBasis p 1
local notation "Boundaries" => fun p : Momentum => GradedBoundaries planeFrame planeBasis p 1

local instance (p : Momentum) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance (p : Momentum) (g : ℤ) :
    AddCommGroup (GradedCycles planeFrame planeBasis p g) :=
  Submodule.addCommGroup _

/-- Relative ghost-one BRST cohomology, summed over the plane momenta. -/
abbrev MomentumH1 := ⨁ p : Momentum, H p

local notation "incl" => DirectSum.lof ℂ Momentum H

/-- Bilinear extension of the native quotient bracket to the momentum direct sum. -/
def momentumBracket : MomentumH1 →ₗ[ℂ] MomentumH1 →ₗ[ℂ] MomentumH1 :=
  DirectSum.toModule ℂ Momentum _ fun p =>
    (DirectSum.toModule ℂ Momentum _ fun q =>
      ((LinearMap.llcomp ℂ (H q) (H (p + q)) MomentumH1 (incl (p + q))).comp
        (bracket p q)).flip).flip

@[simp] theorem momentumBracket_incl (p q : Momentum) (x : H p) (y : H q) :
    momentumBracket (incl p x) (incl q y) = incl (p+q) (bracket p q x y) := by
  simp only [momentumBracket, DirectSum.toModule_lof, LinearMap.flip_apply,
    LinearMap.comp_apply, LinearMap.llcomp_apply]

private def inclCycle (p : Momentum) : Cycles p →ₗ[ℂ] MomentumH1 :=
  (incl p).comp (Boundaries p).mkQ

private theorem inclCycle_congr {p q : Momentum} (h : p = q) (x : Cycles p) (y : Cycles q)
    (he : nativeValue x = nativeValue y) : inclCycle p x = inclCycle q y := by
  subst q
  rw [nativeValue_injective _ he]

private theorem inclCycle_cast {p q : Momentum} (h : p = q) (x : Cycles p) :
    nativeValue (h ▸ x : Cycles q) = nativeValue x := by
  subst q
  rfl

private theorem momentum_skew_incl (p q : Momentum) (x : H p) (y : H q) :
    momentumBracket (incl p x) (incl q y) + momentumBracket (incl q y) (incl p x) = 0 := by
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  refine Submodule.Quotient.induction_on _ y fun y => ?_
  simp only [momentumBracket_incl, bracket_mk]
  change inclCycle (p+q) (cycleCurrent x y) + inclCycle (q+p) (cycleCurrent y x) = 0
  let h : q+p = p+q := add_comm q p
  let v : Cycles (p+q) := h ▸ cycleCurrent y x
  have hv : nativeValue v = nativeValue (cycleCurrent y x) := inclCycle_cast h _
  rw [inclCycle_congr h _ v hv.symm, ← map_add]
  have hz := skew_defect_class_zero odd_product_skew x y (cycleCurrent x y + v)
    (by rw [native_add, hv, native_cycleCurrent, native_cycleCurrent])
  change incl (p+q) (Submodule.Quotient.mk (cycleCurrent x y + v)) = 0
  rw [hz, map_zero]

private theorem momentum_leibniz_incl (p q r : Momentum) (x : H p) (y : H q) (z : H r) :
    momentumBracket (incl p x) (momentumBracket (incl q y) (incl r z)) =
      momentumBracket (momentumBracket (incl p x) (incl q y)) (incl r z) +
      momentumBracket (incl q y) (momentumBracket (incl p x) (incl r z)) := by
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  refine Submodule.Quotient.induction_on _ y fun y => ?_
  refine Submodule.Quotient.induction_on _ z fun z => ?_
  simp only [momentumBracket_incl, bracket_mk]
  change inclCycle (p+(q+r)) (cycleCurrent x (cycleCurrent y z)) =
    inclCycle ((p+q)+r) (cycleCurrent (cycleCurrent x y) z) +
      inclCycle (q+(p+r)) (cycleCurrent y (cycleCurrent x z))
  let h : q+(p+r) = (p+q)+r := by abel
  let v : Cycles ((p+q)+r) := h ▸ cycleCurrent y (cycleCurrent x z)
  have hv : nativeValue v = nativeValue (cycleCurrent y (cycleCurrent x z)) :=
    inclCycle_cast h _
  rw [inclCycle_congr h _ v hv.symm, ← map_add]
  apply inclCycle_congr (add_assoc p q r).symm
  simp only [native_add, hv, native_cycleCurrent]
  exact current_leftLeibniz even_current _ _ _ (native_degree x) (native_degree y)

private theorem momentumBracket_add_left (x y z : MomentumH1) :
    momentumBracket (x+y) z = momentumBracket x z + momentumBracket y z :=
  LinearMap.congr_fun (momentumBracket.map_add x y) z

private theorem momentumBracket_add_right (x y z : MomentumH1) :
    momentumBracket x (y+z) = momentumBracket x y + momentumBracket x z :=
  (momentumBracket x).map_add y z

private theorem momentum_skew_sum (x y : MomentumH1) :
    momentumBracket x y + momentumBracket y x = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    change momentumBracket (incl p x) y + momentumBracket y (incl p x) = 0
    induction y using DirectSum.induction_on with
    | zero => simp
    | of q y => exact momentum_skew_incl p q x y
    | add y z hy hz =>
      simp only [momentumBracket_add_left, momentumBracket_add_right]
      calc
        _ = (momentumBracket (incl p x) y + momentumBracket y (incl p x)) +
            (momentumBracket (incl p x) z + momentumBracket z (incl p x)) := by abel
        _ = 0 := (congrArg₂ (· + ·) hy hz).trans (zero_add 0)
  | add x z hx hz =>
    simp only [momentumBracket_add_left, momentumBracket_add_right]
    calc
      _ = (momentumBracket x y + momentumBracket y x) +
          (momentumBracket z y + momentumBracket y z) := by abel
      _ = 0 := (congrArg₂ (· + ·) hx hz).trans (zero_add 0)

private theorem momentum_leibniz (x y z : MomentumH1) :
    momentumBracket x (momentumBracket y z) =
      momentumBracket (momentumBracket x y) z + momentumBracket y (momentumBracket x z) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    change momentumBracket (incl p x) (momentumBracket y z) =
      momentumBracket (momentumBracket (incl p x) y) z +
        momentumBracket y (momentumBracket (incl p x) z)
    induction y using DirectSum.induction_on with
    | zero => simp
    | of q y =>
      change momentumBracket (incl p x) (momentumBracket (incl q y) z) =
        momentumBracket (momentumBracket (incl p x) (incl q y)) z +
          momentumBracket (incl q y) (momentumBracket (incl p x) z)
      induction z using DirectSum.induction_on with
      | zero => simp
      | of r z => exact momentum_leibniz_incl p q r x y z
      | add z w hz hw => simp only [momentumBracket_add_right, hz, hw]; abel
    | add y w hy hw =>
      simp only [momentumBracket_add_left, momentumBracket_add_right, hy, hw]
      abel
  | add x w hx hw =>
    simp only [momentumBracket_add_left, momentumBracket_add_right, hx, hw]
    abel

instance momentumLieRing : LieRing MomentumH1 where
  bracket x y := momentumBracket x y
  add_lie := momentumBracket_add_left
  lie_add x := (momentumBracket x).map_add
  lie_self x := by
    change momentumBracket x x = 0
    calc
      momentumBracket x x = (2 : ℂ)⁻¹ • (momentumBracket x x + momentumBracket x x) := by module
      _ = 0 := by rw [momentum_skew_sum, smul_zero]
  leibniz_lie := momentum_leibniz

instance momentumLieAlgebra : LieAlgebra ℂ MomentumH1 where
  lie_smul c x y := (momentumBracket x).map_smul c y

end MomentumSum

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
