/- GID: D5/S3/VertexAlgebra/Lattice/FinitePermutationInvariants
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FinitePermutationInvariants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A representation permuting a finite basis has one invariant dimension per orbit, with arbitrary stabilizers and characteristic. -/

import D5.S3.VertexAlgebra.Lattice.FiniteGroupOrbitFixedLine
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
The basis may have nontrivial stabilizers, and the acting group need not be
finite. Fixed vectors are identified with functions on the actual orbit
quotient by descending their basis coefficients. Conversely, orbit-constant
coefficients reconstruct fixed vectors. There is no division by the group
order and no characteristic restriction.

proof_shape: content, for the orbit-coefficient descent and reconstruction.
admission_basis: escape-witness.
escape_witness: the bidirectional correspondence between actual fixed vectors
and coefficients on arbitrary basis orbits; the regular-orbit theorem does not
supply this when stabilizers are nontrivial.
Direct project supplier: FiniteGroupOrbitFixedLine.fixedSubmodule (definition;
no frozen theorem is used). Mathlib supplies basis coordinates, orbit quotient
relations, and finite function-space dimension.
utility: none; these are general algebraic results, with no bounded enumeration,
checker, numerical reduction or certified instance.
The theorem applies to pure permutation actions. A lattice lift with phases
requires a separate stabilizer-character analysis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.FinitePermutationInvariants

open FiniteGroupOrbitFixedLine

variable {K G X V : Type*} [Field K] [Group G] [MulAction G X]
  [Fintype X] [AddCommGroup V] [Module K V]

private theorem coefficient_translate
    (rho : G →* (V ≃ₗ[K] V)) (b : Basis X K V)
    (hperm : ∀ g x, rho g (b x) = b (g • x))
    (g : G) (v : V) (x : X) :
    b.equivFun (rho g v) (g • x) = b.equivFun v x := by
  classical
  have hinj : Function.Injective (fun y : X => g • y) := MulAction.injective g
  have hmap : (b.coord (g • x)).comp (rho g).toLinearMap = b.coord x := by
    apply b.ext
    intro y
    simp [LinearMap.comp_apply, hperm, Basis.coord_apply, hinj.eq_iff]
  exact congrArg (fun f : V →ₗ[K] K => f v) hmap

/-- Fixed vectors correspond to arbitrary coefficients on the actual basis orbits. -/
noncomputable def fixedBasisEquivOrbitFunctions
    (rho : G →* (V ≃ₗ[K] V)) (b : Basis X K V)
    (hperm : ∀ g x, rho g (b x) = b (g • x)) :
    fixedSubmodule rho ≃ₗ[K] (MulAction.orbitRel.Quotient G X → K) where
  toFun v := Quotient.lift (b.equivFun v.1) (by
    intro x y hxy
    rcases hxy with ⟨g, rfl⟩
    have h := coefficient_translate rho b hperm g v.1 y
    rw [v.property g] at h
    exact h)
  invFun c := ⟨b.equivFun.symm (fun x => c (Quotient.mk _ x)), by
    intro g
    apply b.equivFun.injective
    funext x
    have h := coefficient_translate rho b hperm g
      (b.equivFun.symm (fun x => c (Quotient.mk _ x))) (g⁻¹ • x)
    simpa only [smul_inv_smul, LinearEquiv.apply_symm_apply,
      MulAction.orbitRel.Quotient.quotient_smul_eq] using h⟩
  left_inv v := by
    apply Subtype.ext
    apply b.equivFun.injective
    simp
  right_inv c := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    simp
  map_add' v w := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    simp
  map_smul' a v := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    simp

/-- Stabilizers do not alter the one-dimensional contribution of a pure permutation orbit. -/
theorem fixed_finrank_eq_orbit_card
    (rho : G →* (V ≃ₗ[K] V)) (b : Basis X K V)
    (hperm : ∀ g x, rho g (b x) = b (g • x)) :
    Module.finrank K (fixedSubmodule rho) =
      Nat.card (MulAction.orbitRel.Quotient G X) := by
  classical
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  rw [(fixedBasisEquivOrbitFunctions rho b hperm).finrank_eq, Nat.card_eq_fintype_card]
  exact Module.finrank_fintype_fun_eq_card

end D5.S3.VertexAlgebra.Lattice.FinitePermutationInvariants
