/- GID: D5/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite-dimensional three-term chain complex satisfies the Euler characteristic identity. -/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.HomologicalAlgebra.FiniteDimensionalEulerCharacteristic

open Module

/-- The middle differential with codomain restricted to the next kernel. -/
noncomputable def middleDifferential
    {K : Type u} [Field K]
    {U : Type v} [AddCommGroup U] [Module K U]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type v} [AddCommGroup W] [Module K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hgf : g.comp f = 0) :
    U →ₗ[K] LinearMap.ker g :=
  f.codRestrict (LinearMap.ker g) (by
    intro x
    rw [LinearMap.mem_ker]
    have hx := congrArg (fun q : U →ₗ[K] W => q x) hgf
    simpa [LinearMap.comp_apply] using hx)

/-- For a finite-dimensional chain U → V → W, the alternating sum of the
dimensions of the terms equals the alternating sum of the dimensions of
H0 = W / range(g), H1 = ker(g) / range(f), and H2 = ker(f).
The middle quotient uses middleDifferential so that range(f) is represented
as a submodule of ker(g). -/
theorem finrank_three_term_euler
    {K : Type u} [Field K]
    {U : Type v} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hgf : g.comp f = 0) :
    finrank K U + finrank K W +
          finrank K ((LinearMap.ker g) ⧸ LinearMap.range
            (middleDifferential f g hgf)) =
      finrank K V + finrank K (W ⧸ LinearMap.range g) +
        finrank K (LinearMap.ker f) := by
  let f' := middleDifferential f g hgf
  have hker : LinearMap.ker f' = LinearMap.ker f := by
    simp [f', middleDifferential]
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hg := LinearMap.finrank_range_add_finrank_ker g
  have hf' := LinearMap.finrank_range_add_finrank_ker f'
  have hker_rank : finrank K (LinearMap.ker f') = finrank K (LinearMap.ker f) := by
    rw [hker]
  have hrange : finrank K (LinearMap.range f') = finrank K (LinearMap.range f) := by
    omega
  have h1 := (LinearMap.range f').finrank_quotient_add_finrank
  have h0 := (LinearMap.range g).finrank_quotient_add_finrank
  change finrank K U + finrank K W +
      finrank K ((LinearMap.ker g) ⧸ LinearMap.range f') =
      finrank K V + finrank K (W ⧸ LinearMap.range g) +
        finrank K (LinearMap.ker f)
  omega

end D5.S3.HomologicalAlgebra.FiniteDimensionalEulerCharacteristic
