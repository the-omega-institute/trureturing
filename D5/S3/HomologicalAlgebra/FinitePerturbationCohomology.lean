/- GID: D5/S3/HomologicalAlgebra/FinitePerturbationCohomology
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FinitePerturbationCohomology
   mirror-E: none(waiver:algebraic-inference)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Actual cohomology quotients and pointwise perturbation retractions. -/

/- Actual kernel/image cohomology for finite perturbation with nonzero transfer. -/

import D5.S3.HomologicalAlgebra.FinitePerturbation
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The finite perturbation inference is reused from
`D5.S3.HomologicalAlgebra.FinitePerturbation.Input.finite_perturbation`;
the classical basic perturbation lemma is due to Gugenheim--Lambe--Stasheff.
The concrete `boundaryMap` / range / quotient pattern follows the repository's
`D5.S3.VertexAlgebra.LatticeOriginalAbsoluteZeroCohomology`, retaining its source attribution but
none of its special BRST hypotheses or calculations. It is also the literal
quotient used by Joël Riou's Mathlib `ShortComplex.moduleCatLeftHomologyData`.
Quotient descent reuses Mathlib's `Submodule.mapQ`, `Quotient.eq` and quotient
induction (Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov;
Apache 2.0). No new perturbation or categorical infrastructure is introduced.

The target is cohomology of the actual transferred differential, which need
not vanish. There is no assertion identifying a physical charge or ground
complex with this algebraic input. This file is a source-only candidate;
native and official acceptance require independent validation.
-/

namespace D5.S3.HomologicalAlgebra.FinitePerturbation

section Quotient

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The actual differential, with its codomain restricted to its actual kernel. -/
def boundaryMap (d : Module.End R M) (square : d * d = 0) :
    M →ₗ[R] LinearMap.ker d :=
  d.codRestrict _ (fun x => DFunLike.congr_fun square x)

/-- Boundaries have genuine preimages in the original module. -/
def Boundaries (d : Module.End R M) (square : d * d = 0) :
    Submodule R (LinearMap.ker d) :=
  LinearMap.range (boundaryMap d square)

/-- Only one quotient convention: the kernel modulo the actual restricted image. -/
abbrev Cohomology (d : Module.End R M) (square : d * d = 0) :=
  LinearMap.ker d ⧸ Boundaries d square

private def cycleMap (d : Module.End R M) (e : Module.End R N)
    (f : M →ₗ[R] N) (chain : f.comp d = e.comp f) :
    LinearMap.ker d →ₗ[R] LinearMap.ker e :=
  (f.comp (LinearMap.ker d).subtype).codRestrict _ (fun x => by
    have hx : d (x : M) = 0 := x.property
    have eq := DFunLike.congr_fun chain (x : M)
    simpa [hx] using eq.symm)

private def cohomologyMap (d : Module.End R M) (e : Module.End R N)
    (d_square : d * d = 0) (e_square : e * e = 0)
    (f : M →ₗ[R] N) (chain : f.comp d = e.comp f) :
    Cohomology d d_square →ₗ[R] Cohomology e e_square :=
  (Boundaries d d_square).mapQ (Boundaries e e_square) (cycleMap d e f chain) (by
    intro x hx
    change cycleMap d e f chain x ∈ Boundaries e e_square
    change ∃ y, boundaryMap d d_square y = x at hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨f y, ?_⟩
    apply Subtype.ext
    exact (DFunLike.congr_fun chain y).symm)

-- This readout is used in both inverse proofs below, not just exposed as an alias.
private theorem cohomologyMap_mk (d : Module.End R M) (e : Module.End R N)
    (d_square : d * d = 0) (e_square : e * e = 0)
    (f : M →ₗ[R] N) (chain : f.comp d = e.comp f) (x : LinearMap.ker d) :
    cohomologyMap d e d_square e_square f chain (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cycleMap d e f chain x) := rfl

end Quotient

section Perturbation

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

namespace Input

variable (c : Input (R := R) (U := U) (V := V))

private theorem cycle_primitive (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) (x : V) (hx : c.D x = 0) :
    c.D (c.H n x) = x - c.I n (c.P n x) := by
  have out := c.finite_perturbation n hn nilpotent
  have eq := DFunLike.congr_fun out.homotopy x
  simpa [hx] using eq

/-- A genuine source cycle is exact precisely when its projection is exact for
the actual transferred differential. The reverse primitive is `I u + H x`. -/
theorem boundary_iff_transferred_boundary (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) (x : V) (hx : c.D x = 0) :
    (∃ y : V, c.D y = x) ↔ ∃ u : U, c.transferred n u = c.P n x := by
  have out := c.finite_perturbation n hn nilpotent
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨c.P n y, (DFunLike.congr_fun out.projection_chain y).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨c.I n u + c.H n x, ?_⟩
    have inc : c.D (c.I n u) = c.I n (c.transferred n u) :=
      DFunLike.congr_fun out.inclusion_chain u
    rw [map_add, inc, hu, add_comm, cycle_primitive c n hn nilpotent x hx,
      sub_add_cancel]

/-- Finite perturbation induces the canonical linear equivalence of the two
literal kernel/image quotients. It requires no zero-transfer hypothesis.
Both directions descend actual chain maps, and the left inverse uses the
actual boundary with preimage `H x`; the right inverse uses `P I = id`. -/
def cohomologyEquiv (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) :
    Cohomology c.D c.perturbed_sq ≃ₗ[R]
      Cohomology (c.transferred n) (c.finite_perturbation n hn nilpotent).transferred_sq := by
  let out := c.finite_perturbation n hn nilpotent
  let fwd := cohomologyMap c.D (c.transferred n) c.perturbed_sq out.transferred_sq
    (c.P n) out.projection_chain
  let bwd := cohomologyMap (c.transferred n) c.D out.transferred_sq c.perturbed_sq
    (c.I n) out.inclusion_chain.symm
  refine { fwd with
    toFun := fwd
    invFun := bwd
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    dsimp only [fwd, bwd]
    simp only [cohomologyMap_mk]
    symm
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨c.H n (x : V), ?_⟩
    apply Subtype.ext
    exact cycle_primitive c n hn nilpotent (x : V) x.property
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun u => ?_)
    dsimp only [fwd, bwd]
    simp only [cohomologyMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact DFunLike.congr_fun out.retract (u : U)

/-- The forward map is the stated projection on every actual source cycle. -/
@[simp] theorem cohomologyEquiv_mk (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) (x : V) (hx : c.D x = 0) :
    c.cohomologyEquiv n hn nilpotent (Submodule.Quotient.mk ⟨x, hx⟩) =
      Submodule.Quotient.mk
        (⟨c.P n x, by
          have eq := DFunLike.congr_fun
            (c.finite_perturbation n hn nilpotent).projection_chain x
          simpa [hx] using eq.symm⟩ : LinearMap.ker (c.transferred n)) := rfl

/-- The inverse map is the stated inclusion on every actual transferred cycle. -/
@[simp] theorem cohomologyEquiv_symm_mk (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) (u : U) (hu : c.transferred n u = 0) :
    (c.cohomologyEquiv n hn nilpotent).symm
        (Submodule.Quotient.mk (⟨u, hu⟩ : LinearMap.ker (c.transferred n))) =
      Submodule.Quotient.mk
        (⟨c.I n u, by
          have eq := DFunLike.congr_fun
            (c.finite_perturbation n hn nilpotent).inclusion_chain u
          simpa [hu] using eq⟩ : LinearMap.ker c.D) := rfl

end Input

end Perturbation
end D5.S3.HomologicalAlgebra.FinitePerturbation
