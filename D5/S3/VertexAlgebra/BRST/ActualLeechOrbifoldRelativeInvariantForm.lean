/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeInvariantForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeInvariantForm
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The normalized native BPZ form on the actual relative BRST Lie algebra. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRSTPairingInvariance
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootBracket
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! The signed native BPZ pairing extends to the momentum direct sum.
The actual zero-momentum Cartan classes have hyperbolic Gram matrix. -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open RelativeCohomology (GradedCycles GradedBoundaries GradedCohomology NativeShell nativeQ)
open private native_mem native_degree native_closed cycleOf boundary_of_native
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket
open private cyclesEquiv from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "Cycles" => fun p : Momentum => GradedCycles planeFrame planeBasis p 1
local notation "Boundaries" => fun p : Momentum => GradedBoundaries planeFrame planeBasis p 1

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
local instance (p : Momentum) : AddCommGroup (relativeShell p) := Submodule.addCommGroup _
local instance (p : Momentum) : AddCommGroup (NativeShell p) := Submodule.addCommGroup _
local instance (p : Momentum) : AddCommGroup (Cycles p) := Submodule.addCommGroup _

local notation "incl" => DirectSum.lof ℂ Momentum H

/-- The signed native BPZ form on the momentum direct sum. -/
def nativeRelativeBPZ : LinearMap.BilinForm ℂ MomentumH1 :=
  DirectSum.toModule ℂ Momentum _ fun p =>
    (DirectSum.toModule ℂ Momentum _ fun q => (NativeBPZ.gradedRelativePairing p q).flip).flip

/-- Evaluation on arbitrary homogeneous cohomology classes. -/
@[simp] theorem nativeRelativeBPZ_incl (p q : Momentum) (x : H p) (y : H q) :
    nativeRelativeBPZ (incl p x) (incl q y) = NativeBPZ.gradedRelativePairing p q x y := by
  simp only [nativeRelativeBPZ, DirectSum.toModule_lof, LinearMap.flip_apply]

/-- Evaluation on the classes of original relative cycles. -/
theorem nativeRelativeBPZ_incl_mk {p q : Momentum} (x : Cycles p) (y : Cycles q) :
    nativeRelativeBPZ (incl p (Submodule.Quotient.mk x)) (incl q (Submodule.Quotient.mk y)) =
      -NativeBPZ.relativePairing (nativeValue x) (nativeValue y) := by
  rw [nativeRelativeBPZ_incl, NativeBPZ.gradedRelativePairing_mk]

/-- Only opposite momenta can pair. -/
theorem nativeRelativeBPZ_momentum_selection (p q : Momentum) (x : H p) (y : H q)
    (hpq : q ≠ -p) : nativeRelativeBPZ (incl p x) (incl q y) = 0 := by
  refine Submodule.Quotient.induction_on (Boundaries p) x fun x => ?_
  refine Submodule.Quotient.induction_on (Boundaries q) y fun y => ?_
  rw [nativeRelativeBPZ_incl_mk, NativeBPZ.relativePairing_momentum_selection
    ((relative_iff p _).mp (native_mem x)).1 ((relative_iff q _).mp (native_mem y)).1 hpq, neg_zero]

/-- Symmetry on the full momentum direct sum. -/
theorem nativeRelativeBPZ_symmetric : nativeRelativeBPZ.IsSymm := by
  constructor
  intro x y
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | of p x =>
    change nativeRelativeBPZ (incl p x) y = nativeRelativeBPZ y (incl p x)
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | of q y =>
      change nativeRelativeBPZ (incl p x) (incl q y) = nativeRelativeBPZ (incl q y) (incl p x)
      refine Submodule.Quotient.induction_on (Boundaries p) x fun x => ?_
      refine Submodule.Quotient.induction_on (Boundaries q) y fun y => ?_
      simp only [nativeRelativeBPZ_incl_mk]
      exact congrArg (fun a : ℂ => -a) (NativeBPZ.relativePairing_symmetric _ _)
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

private theorem eq_zero_of_pairing_opposite (p : Momentum) (x : H p)
    (hx : ∀ y : H (-p), nativeRelativeBPZ (incl p x) (incl (-p) y) = 0) : x = 0 := by
  revert hx
  refine Submodule.Quotient.induction_on (Boundaries p) x fun x hx => ?_
  let s : NativeShell p := ⟨nativeValue x, native_mem x⟩
  have hs : nativeQ p s = 0 := Subtype.ext (native_closed x)
  have hrad (y : NativeShell (-p)) (hy : Degree 1 y.val) (hQy : nativeQ (-p) y = 0) :
      NativeBPZ.relativePairing s.val y.val = 0 := by
    have hclosed : Q y.val = 0 := congrArg Subtype.val hQy
    let z : Cycles (-p) := cycleOf y.val y.property hy hclosed
    have hz : nativeValue z = y.val := reassoc.symm_apply_apply _
    have h := hx (Submodule.Quotient.mk z)
    rwa [nativeRelativeBPZ_incl_mk, hz, neg_eq_zero] at h
  obtain ⟨a, ha, hQa⟩ :=
    (NativeBPZ.relativePairing_radical_iff_boundary_all_momenta p s (native_degree x) hs).mp hrad
  have hboundary : Q a.val = nativeValue x := congrArg Subtype.val hQa
  exact (Submodule.Quotient.mk_eq_zero (Boundaries p)).mpr
    (boundary_of_native x a.val a.property ha hboundary)

private theorem nativeRelativeBPZ_component (p : Momentum) (x : MomentumH1) (y : H (-p)) :
    nativeRelativeBPZ x (incl (-p) y) =
      nativeRelativeBPZ (incl p (DirectSum.component ℂ Momentum H p x)) (incl (-p) y) := by
  classical
  let proj := DirectSum.component ℂ Momentum H p
  change nativeRelativeBPZ x (incl (-p) y) = nativeRelativeBPZ (incl p (proj x)) (incl (-p) y)
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of q z =>
    change nativeRelativeBPZ (incl q z) (incl (-p) y) =
      nativeRelativeBPZ (incl p (proj (incl q z))) (incl (-p) y)
    by_cases h : q = p
    · subst q
      rw [show proj (incl p z) = z from DirectSum.component.lof_self ℂ (M := H) p z]
    · have hzero : proj (incl q z) = 0 := by
        dsimp only [proj]
        rw [DirectSum.component.of, dite_eq_right h]
      simpa only [hzero, map_zero, LinearMap.zero_apply] using
        nativeRelativeBPZ_momentum_selection q (-p) z y (fun heq => h (neg_inj.mp heq.symm))
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- Each component is detected by the opposite momentum, so the full form is nondegenerate. -/
theorem nativeRelativeBPZ_nondegenerate : nativeRelativeBPZ.Nondegenerate := by
  have hleft (x : MomentumH1) (hx : ∀ y : MomentumH1, nativeRelativeBPZ x y = 0) :
      x = 0 := by
    apply DirectSum.ext_component ℂ
    intro p
    rw [map_zero]
    apply eq_zero_of_pairing_opposite
    intro y
    rw [← nativeRelativeBPZ_component p x y]
    exact hx (incl (-p) y)
  refine ⟨hleft, ?_⟩
  intro x hx
  exact hleft x fun y => (nativeRelativeBPZ_symmetric.eq x y).trans (hx y)

/-- Invariance for the existing Lie bracket on actual ghost-one relative cohomology. -/
theorem nativeRelativeBPZ_invariant (x y z : MomentumH1) :
    nativeRelativeBPZ ⁅x, y⁆ z = nativeRelativeBPZ x ⁅y, z⁆ := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_lie, map_zero, LinearMap.zero_apply]
  | of p x =>
    change nativeRelativeBPZ ⁅incl p x, y⁆ z = nativeRelativeBPZ (incl p x) ⁅y, z⁆
    induction y using DirectSum.induction_on with
    | zero => simp only [lie_zero, zero_lie, map_zero, LinearMap.zero_apply]
    | of q y =>
      change nativeRelativeBPZ ⁅incl p x, incl q y⁆ z =
        nativeRelativeBPZ (incl p x) ⁅incl q y, z⁆
      induction z using DirectSum.induction_on with
      | zero => simp only [lie_zero, map_zero]
      | of r z =>
        change nativeRelativeBPZ ⁅incl p x, incl q y⁆ (incl r z) =
          nativeRelativeBPZ (incl p x) ⁅incl q y, incl r z⁆
        change nativeRelativeBPZ (momentumBracket (incl p x) (incl q y)) (incl r z) =
          nativeRelativeBPZ (incl p x) (momentumBracket (incl q y) (incl r z))
        simpa only [momentumBracket_incl, nativeRelativeBPZ_incl] using
          NativeBPZ.gradedRelativePairing_bracket_invariant (p := p) (q := q) (r := r) x y z
      | add z w hz hw => simp only [lie_add, map_add, hz, hw]
    | add y w hy hw => simp only [lie_add, add_lie, map_add, LinearMap.add_apply, hy, hw]
  | add x w hx hw => simp only [add_lie, map_add, LinearMap.add_apply, hx, hw]

/-- The actual Cartan classes have the hyperbolic Gram matrix with off-diagonal entries one. -/
theorem nativeRelativeBPZ_cartan (f g : Fin 2 → ℂ) :
    nativeRelativeBPZ (RealRootBracket.cartanClass f) (RealRootBracket.cartanClass g) =
      f 0 * g 1 + f 1 * g 0 := by
  let a := RelativeZeroMomentum.degreeOneEquiv.symm f
  let b := RelativeZeroMomentum.degreeOneEquiv.symm g
  change nativeRelativeBPZ (incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm f))
    (incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm g)) = _
  rw [RelativeZeroMomentum.ghostOneCohomologyEquiv_symm f,
    RelativeZeroMomentum.ghostOneCohomologyEquiv_symm g]
  change nativeRelativeBPZ (incl 0 (Submodule.Quotient.mk (cyclesEquiv 1 a)))
    (incl 0 (Submodule.Quotient.mk (cyclesEquiv 1 b))) = _
  rw [nativeRelativeBPZ_incl_mk]
  change -NativeBPZ.relativePairing (reassoc.symm a.val.val) (reassoc.symm b.val.val) = _
  simp only [NativeBPZ.relativePairing_zeroMomentum_coordinates, neg_neg, a, b,
    LinearEquiv.apply_symm_apply]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
