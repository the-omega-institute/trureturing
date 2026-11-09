/- GID: D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology
   mirror-E: none(waiver:algebraic-inference)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Actual cohomology quotients and pointwise perturbation retractions. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
import D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Actual kernel/image cohomology for pointwise locally nilpotent perturbation,
with a possibly nonzero transferred differential. The algebraic basic
perturbation lemma is due to Gugenheim--Lambe--Stasheff. All square-zero,
chain, retract and homotopy identities used here are conclusions of
`LocallyNilpotentPerturbation.locally_nilpotent_perturbation`.

The literal `FinitePerturbation.Cohomology`, `Boundaries` and `boundaryMap`
and its private, generic quotient descent are reused without modification.
The inverse proof follows `FinitePerturbation.Input.cohomologyEquiv`, with
the global pointwise inference in place of the finite inference. Its quotient
pattern is attributed to the repository's
`D5.S3.VertexAlgebra.LatticeOriginalAbsoluteZeroCohomology` and Joël Riou's
Mathlib `ShortComplex.moduleCatLeftHomologyData`. Submodule quotient descent,
equality and induction are Mathlib's (Johannes Hölzl, Mario Carneiro, Kevin
Buzzard, Yury Kudryashov; Apache 2.0). Private-name access is Batteries'
`OpenPrivate` (Mario Carneiro; Microsoft Corporation; Apache 2.0).

This is source only, depending on two collected, uncompiled suppliers.
It asserts neither local nilpotence of an original BRST operator nor a
physical full-Q identification. The full scientific objective is incomplete.
-/

-- Short explicit aliases resolve the private declarations in this exact
-- supplying module; no public aliases or private numeric names are created.
open private cycleMap cohomologyMap cohomologyMap_mk
  from D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

namespace D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation

open FinitePerturbation

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
variable (c : Input (R := R) (U := U) (V := V))
variable (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta) ^ n) x = 0)

/-- The actual homotopy supplies a primitive for the difference from the
included projection, on every source cycle. -/
theorem cycle_primitive (x : V) (hx : c.D x = 0) :
    c.D (H c nilpotent x) = x - I c nilpotent (P c nilpotent x) := by
  have out := locally_nilpotent_perturbation c nilpotent
  have eq := DFunLike.congr_fun out.2.2.2.2.1 x
  simpa [hx] using eq

/-- Exactness of a source cycle is detected by the actual transferred
differential. The reverse witness is explicitly `I u + H x`. -/
theorem boundary_iff_transferred_boundary (x : V) (hx : c.D x = 0) :
    (∃ y : V, c.D y = x) ↔
      ∃ u : U, transferred c nilpotent u = P c nilpotent x := by
  have out := locally_nilpotent_perturbation c nilpotent
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨P c nilpotent y, (DFunLike.congr_fun out.2.2.1 y).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨I c nilpotent u + H c nilpotent x, ?_⟩
    have inc : c.D (I c nilpotent u) =
        I c nilpotent (transferred c nilpotent u) :=
      DFunLike.congr_fun out.2.1 u
    rw [map_add, inc, hu, add_comm, cycle_primitive c nilpotent x hx,
      sub_add_cancel]

/-- The global projection descends by the existing generic quotient helper;
the transferred square and projection chain identity are derived conclusions. -/
noncomputable def cohomologyProjection :
    Cohomology c.D c.perturbed_sq →ₗ[R]
      Cohomology (transferred c nilpotent)
        (locally_nilpotent_perturbation c nilpotent).1 :=
  cohomologyMap c.D (transferred c nilpotent) c.perturbed_sq
    (locally_nilpotent_perturbation c nilpotent).1
    (P c nilpotent) (locally_nilpotent_perturbation c nilpotent).2.2.1

/-- The global inclusion descends by the same helper, with its actual chain
identity in the direction required by quotient descent. -/
noncomputable def cohomologyInclusion :
    Cohomology (transferred c nilpotent)
        (locally_nilpotent_perturbation c nilpotent).1 →ₗ[R]
      Cohomology c.D c.perturbed_sq :=
  cohomologyMap (transferred c nilpotent) c.D
    (locally_nilpotent_perturbation c nilpotent).1 c.perturbed_sq
    (I c nilpotent) (locally_nilpotent_perturbation c nilpotent).2.1.symm

-- Both representative readouts are consumed in both quotient inverse proofs.
/-- On an actual cycle the descended projection is literally `[x] ↦ [P x]`. -/
@[simp] theorem cohomologyProjection_mk (x : LinearMap.ker c.D) :
    cohomologyProjection c nilpotent (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨P c nilpotent (x : V), by
          have hx : c.D (x : V) = 0 := x.property
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.2.1 (x : V)
          simpa [hx] using eq.symm⟩ :
            LinearMap.ker (transferred c nilpotent)) := by
  change cohomologyMap c.D (transferred c nilpotent) c.perturbed_sq
      (locally_nilpotent_perturbation c nilpotent).1
      (P c nilpotent) (locally_nilpotent_perturbation c nilpotent).2.2.1
      (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk
      (cycleMap c.D (transferred c nilpotent) (P c nilpotent)
        (locally_nilpotent_perturbation c nilpotent).2.2.1 x)
  exact cohomologyMap_mk c.D (transferred c nilpotent) c.perturbed_sq
    (locally_nilpotent_perturbation c nilpotent).1
    (P c nilpotent) (locally_nilpotent_perturbation c nilpotent).2.2.1 x

/-- On an actual transferred cycle the descended inclusion is `[u] ↦ [I u]`. -/
@[simp] theorem cohomologyInclusion_mk
    (u : LinearMap.ker (transferred c nilpotent)) :
    cohomologyInclusion c nilpotent (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk
        (⟨I c nilpotent (u : U), by
          have hu : transferred c nilpotent (u : U) = 0 := u.property
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.1 (u : U)
          simpa [hu] using eq⟩ : LinearMap.ker c.D) := by
  change cohomologyMap (transferred c nilpotent) c.D
      (locally_nilpotent_perturbation c nilpotent).1 c.perturbed_sq
      (I c nilpotent) (locally_nilpotent_perturbation c nilpotent).2.1.symm
      (Submodule.Quotient.mk u) =
    Submodule.Quotient.mk
      (cycleMap (transferred c nilpotent) c.D (I c nilpotent)
        (locally_nilpotent_perturbation c nilpotent).2.1.symm u)
  exact cohomologyMap_mk (transferred c nilpotent) c.D
    (locally_nilpotent_perturbation c nilpotent).1 c.perturbed_sq
    (I c nilpotent) (locally_nilpotent_perturbation c nilpotent).2.1.symm u

/-- The two literal kernel/image quotients are linearly equivalent on the full
original modules. The left inverse uses `D H + H D = id - I P` with primitive
`H x`; the right inverse uses `P I = id`. No transferred-zero assumption or
uniform nilpotence exponent enters this construction. -/
noncomputable def cohomologyEquiv :
    Cohomology c.D c.perturbed_sq ≃ₗ[R]
      Cohomology (transferred c nilpotent)
        (locally_nilpotent_perturbation c nilpotent).1 := by
  let out := locally_nilpotent_perturbation c nilpotent
  let fwd := cohomologyProjection c nilpotent
  let bwd := cohomologyInclusion c nilpotent
  refine { fwd with
    toFun := fwd
    invFun := bwd
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    dsimp only [fwd, bwd]
    simp only [cohomologyProjection_mk, cohomologyInclusion_mk]
    symm
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨H c nilpotent (x : V), ?_⟩
    apply Subtype.ext
    exact cycle_primitive c nilpotent (x : V) x.property
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun u => ?_)
    dsimp only [fwd, bwd]
    simp only [cohomologyProjection_mk, cohomologyInclusion_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact DFunLike.congr_fun out.2.2.2.1 (u : U)

/-- Forward representative readout for the equivalence itself. -/
@[simp] theorem cohomologyEquiv_mk (x : V) (hx : c.D x = 0) :
    cohomologyEquiv c nilpotent
        (Submodule.Quotient.mk (⟨x, hx⟩ : LinearMap.ker c.D)) =
      Submodule.Quotient.mk
        (⟨P c nilpotent x, by
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.2.1 x
          simpa [hx] using eq.symm⟩ :
            LinearMap.ker (transferred c nilpotent)) := by
  exact cohomologyProjection_mk c nilpotent ⟨x, hx⟩

/-- Inverse representative readout for the equivalence itself. -/
@[simp] theorem cohomologyEquiv_symm_mk (u : U)
    (hu : transferred c nilpotent u = 0) :
    (cohomologyEquiv c nilpotent).symm
        (Submodule.Quotient.mk
          (⟨u, hu⟩ : LinearMap.ker (transferred c nilpotent))) =
      Submodule.Quotient.mk
        (⟨I c nilpotent u, by
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.1 u
          simpa [hu] using eq⟩ : LinearMap.ker c.D) := by
  exact cohomologyInclusion_mk c nilpotent ⟨u, hu⟩

end D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
