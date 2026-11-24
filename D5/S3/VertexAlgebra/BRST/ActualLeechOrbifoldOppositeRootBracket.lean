/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldOppositeRootBracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldOppositeRootBracket
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The native BPZ formula for opposite-momentum brackets in actual relative BRST H¹. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeInvariantForm
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The invariant form determines the Cartan component of the actual opposite-momentum bracket. -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open RelativeCohomology (GradedCycles GradedCohomology)

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
local instance (p : Momentum) : AddCommGroup (relativeShell p) := Submodule.addCommGroup _
local instance (p : Momentum) : AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup _

/-- The graded bracket of opposite homogeneous classes lies in the zero-momentum summand. -/
theorem lie_incl_neg_incl_mem_zero_momentum (p : Momentum) (x : H p) (y : H (-p)) :
    ⁅incl p x, incl (-p) y⁆ ∈ LinearMap.range (incl 0) := by
  change momentumBracket (incl p x) (incl (-p) y) ∈ LinearMap.range (incl 0)
  rw [momentumBracket_incl]
  have mem_range (q : Momentum) (a : H q) (hq : q = 0) :
      incl q a ∈ LinearMap.range (incl 0) := by
    subst q
    exact ⟨a, rfl⟩
  exact mem_range (p + -p) (bracket p (-p) x y) (add_neg_cancel p)

private theorem cartanClass_of_zero_momentum (a : H 0) :
    RealRootBracket.cartanClass (RelativeZeroMomentum.ghostOneCohomologyEquiv a) = incl 0 a := by
  change incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm
    (RelativeZeroMomentum.ghostOneCohomologyEquiv a)) = incl 0 a
  rw [LinearEquiv.symm_apply_apply]

-- Comparing the Cartan coordinates requires reducing the concrete quotient and direct sum types.
set_option maxHeartbeats 600000 in
/-- The actual opposite-momentum commutator is the native BPZ pairing times the Cartan
class of the integral momentum in the ordered null basis. -/
theorem lie_incl_neg_incl (p : Momentum) (x : H p) (y : H (-p)) :
    ⁅incl p x, incl (-p) y⁆ =
      nativeRelativeBPZ (incl p x) (incl (-p) y) •
        RealRootBracket.cartanClass (fun i => (p i : ℂ)) := by
  obtain ⟨a, ha⟩ := lie_incl_neg_incl_mem_zero_momentum p x y
  let f := RelativeZeroMomentum.ghostOneCohomologyEquiv a
  have hf : RealRootBracket.cartanClass f = ⁅incl p x, incl (-p) y⁆ :=
    (cartanClass_of_zero_momentum a).trans ha
  have hright (g : Fin 2 → ℂ) :
      ⁅incl (-p) y, RealRootBracket.cartanClass g⁆ =
        (g 0 * (p (1 : Fin 2) : ℂ) + g 1 * (p (0 : Fin 2) : ℂ)) • incl (-p) y := by
    rw [← lie_skew, RealRootBracket.lie_cartanClass_incl]
    simp only [Pi.neg_apply, Int.cast_neg, mul_neg, ← neg_add, neg_smul, neg_neg]
  let c := nativeRelativeBPZ (incl p x) (incl (-p) y)
  have hpair (g : Fin 2 → ℂ) :
      f 0 * g 1 + f 1 * g 0 = (g 0 * (p (1 : Fin 2) : ℂ) + g 1 * (p (0 : Fin 2) : ℂ)) * c := by
    rw [← nativeRelativeBPZ_cartan f g, hf, nativeRelativeBPZ_invariant, hright,
      LinearMap.BilinForm.smul_right]
  have h0 : f 0 = (p (0 : Fin 2) : ℂ) * c := by
    simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
      mul_one, mul_zero, zero_mul, one_mul, add_zero, zero_add] using
      hpair (Pi.single (1 : Fin 2) 1)
  have h1 : f 1 = (p (1 : Fin 2) : ℂ) * c := by
    simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      mul_one, mul_zero, zero_mul, one_mul, add_zero, zero_add] using
      hpair (Pi.single (0 : Fin 2) 1)
  have hcoords : f = c • (fun i : Fin 2 => (p i : ℂ)) := by
    funext i
    fin_cases i
    · exact h0.trans (mul_comm _ c)
    · exact h1.trans (mul_comm _ c)
  calc
    ⁅incl p x, incl (-p) y⁆ = RealRootBracket.cartanClass f := hf.symm
    _ = RealRootBracket.cartanClass (c • (fun i : Fin 2 => (p i : ℂ))) :=
      congrArg RealRootBracket.cartanClass hcoords
    _ = c • RealRootBracket.cartanClass (fun i : Fin 2 => (p i : ℂ)) :=
      RealRootBracket.cartanClass.map_smul c _

private theorem momentumIncl_injective (p : Momentum) : Function.Injective (incl p) := by
  classical
  intro x y h
  simpa only [DirectSum.component.lof_self] using
    congrArg (fun z : MomentumH1 => DirectSum.component ℂ Momentum H p z) h

private theorem exists_opposite_pairing_ne_zero (p : Momentum) (x : H p) (hx : x ≠ 0) :
    ∃ y : H (-p), nativeRelativeBPZ (incl p x) (incl (-p) y) ≠ 0 := by
  classical
  by_contra! h
  have hall (z : MomentumH1) : nativeRelativeBPZ (incl p x) z = 0 := by
    induction z using DirectSum.induction_on with
    | zero => exact (nativeRelativeBPZ (incl p x)).map_zero
    | of q w =>
      change nativeRelativeBPZ (incl p x) (incl q w) = 0
      by_cases hq : q = -p
      · subst q
        exact h w
      · exact nativeRelativeBPZ_momentum_selection p q x w hq
    | add z w hz hw => simp only [map_add, hz, hw, add_zero]
  have hzero := nativeRelativeBPZ_nondegenerate.1 (incl p x) hall
  exact hx (momentumIncl_injective p (hzero.trans ((incl p).map_zero).symm))

/-- At a supported momentum, opposite brackets span the Cartan class of that momentum. -/
theorem span_opposite_root_brackets (p : Momentum) (hSupport : ∃ x : H p, x ≠ 0) :
    Submodule.span ℂ {z : MomentumH1 | ∃ (x : H p) (y : H (-p)), ⁅incl p x, incl (-p) y⁆ = z} =
      Submodule.span ℂ {RealRootBracket.cartanClass (fun i => (p i : ℂ))} := by
  let brackets : Set MomentumH1 := {z | ∃ (x : H p) (y : H (-p)), ⁅incl p x, incl (-p) y⁆ = z}
  change Submodule.span ℂ brackets = _
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, y, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨_, (lie_incl_neg_incl p x y).symm⟩
  · obtain ⟨x, hx⟩ := hSupport
    obtain ⟨y, hy⟩ := exists_opposite_pairing_ne_zero p x hx
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    have hb : ⁅incl p x, incl (-p) y⁆ ∈ Submodule.span ℂ brackets :=
      Submodule.subset_span ⟨x, y, rfl⟩
    rw [lie_incl_neg_incl] at hb
    simpa only [inv_smul_smul₀ hy] using
      (Submodule.span ℂ brackets).smul_mem (nativeRelativeBPZ (incl p x) (incl (-p) y))⁻¹ hb

/-- For a nonzero supported momentum, the span of its opposite brackets has dimension one. -/
theorem finrank_span_opposite_root_brackets (p : Momentum) (hp : p ≠ 0)
    (hSupport : ∃ x : H p, x ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ
      {z : MomentumH1 | ∃ (x : H p) (y : H (-p)), ⁅incl p x, incl (-p) y⁆ = z}) = 1 := by
  rw [span_opposite_root_brackets p hSupport]
  apply finrank_span_singleton
  intro hz
  let f : Fin 2 → ℂ := fun i => (p i : ℂ)
  let e := RelativeZeroMomentum.ghostOneCohomologyEquiv.symm
  change incl 0 (e f) = 0 at hz
  have hzq : e f = 0 := momentumIncl_injective 0 (hz.trans ((incl 0).map_zero).symm)
  have hf := e.map_eq_zero_iff.mp hzq
  apply hp
  funext i
  change p i = (0 : ℤ)
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_zero]
  exact congrFun hf i

/-- Commuting with all opposite brackets at a supported momentum is equivalent to
commuting with its Cartan class. -/
theorem centralizes_opposite_root_brackets_iff (p : Momentum) (hSupport : ∃ x : H p, x ≠ 0)
    (z : MomentumH1) :
    (∀ (x : H p) (y : H (-p)), ⁅⁅incl p x, incl (-p) y⁆, z⁆ = 0) ↔
      ⁅RealRootBracket.cartanClass (fun i => (p i : ℂ)), z⁆ = 0 := by
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := hSupport
    obtain ⟨y, hy⟩ := exists_opposite_pairing_ne_zero p x hx
    have h := hz x y
    rw [lie_incl_neg_incl, smul_lie] at h
    simpa only [inv_smul_smul₀ hy, smul_zero] using
      congrArg (fun w : MomentumH1 => (nativeRelativeBPZ (incl p x) (incl (-p) y))⁻¹ • w) h
  · intro hz x y
    rw [lie_incl_neg_incl, smul_lie, hz, smul_zero]

/-- The centralizer of the full actual Cartan subspace is the Cartan subspace itself. -/
theorem mem_range_cartanClass_iff_centralizes_cartan (z : MomentumH1) :
    z ∈ LinearMap.range RealRootBracket.cartanClass ↔
      ∀ f : Fin 2 → ℂ, ⁅RealRootBracket.cartanClass f, z⁆ = 0 := by
  constructor
  · rintro ⟨f, rfl⟩ g
    change ⁅incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm g),
      incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm f)⁆ = 0
    exact RealRootBracket.zero_momentum_lie_eq_zero _ _
  · intro hz
    obtain ⟨a, ha⟩ := (RealRootBracket.mem_zero_momentum_range_iff_cartan_centralizer z).mpr
      (fun i => hz (Pi.single i 1))
    exact ⟨RelativeZeroMomentum.ghostOneCohomologyEquiv a,
      (cartanClass_of_zero_momentum a).trans ha⟩

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
