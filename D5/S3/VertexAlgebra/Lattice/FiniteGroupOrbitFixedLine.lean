/- GID: D5/S3/VertexAlgebra/Lattice/FiniteGroupOrbitFixedLine
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FiniteGroupOrbitFixedLine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A free finite-group orbit has a one-dimensional fixed line, without a quotient-dimension claim. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
A finite group acting by invertible linear maps on a linearly independent orbit
contributes exactly one Reynolds fixed line.  This is the group-action-to-number
bridge used later for charged lattice orbits.  The theorem only classifies the
fixed submodule inside the specified orbit span; it does not identify a whole
C2 quotient or assume a spanning theorem for that quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.FiniteGroupOrbitFixedLine

open scoped BigOperators

variable {K G V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Group G] [Fintype G]

noncomputable def orbitMap (rho : G →* (V ≃ₗ[K] V)) (v : V) : G → V :=
  fun g => rho g v

noncomputable def orbitSum (rho : G →* (V ≃ₗ[K] V)) (v : V) : V :=
  ∑ g : G, orbitMap rho v g

def orbitSpan (b : G → V) : Submodule K V :=
  Submodule.span K (Set.range b)

def fixedSubmodule (rho : G →* (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {x | ∀ g : G, rho g x = x}
  zero_mem' := by intro g; simp
  add_mem' := by intro x y hx hy g; simp [hx g, hy g]
  smul_mem' := by intro c x hx g; simp [hx g]

def orbitFixedSubmodule (rho : G →* (V ≃ₗ[K] V)) (b : G → V) : Submodule K V :=
  orbitSpan b ⊓ fixedSubmodule rho

theorem orbitSum_ne_zero
    (b : G → V)
    (hind : LinearIndependent K b) :
    (∑ g : G, b g) ≠ 0 := by
  intro hzero
  have hcoeff : (fun _ : G => (1 : K)) = 0 := by
    apply hind.fintypeLinearCombination_injective
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply]
    simpa using hzero
  have hone : (1 : K) = 0 := by
    simpa using congrFun hcoeff (1 : G)
  exact one_ne_zero hone

lemma orbitCombination_shift
    (rho : G →* (V ≃ₗ[K] V)) (b : G → V)
    (hperm : ∀ h g, rho h (b g) = b (h * g))
    (h : G) (c : G → K) :
    (∑ g : G, c (h⁻¹ * g) • b g) =
      rho h (∑ g : G, c g • b g) := by
  classical
  simp only [map_sum, map_smul, hperm]
  calc
    (∑ g : G, c (h⁻¹ * g) • b g) =
        ∑ g : G, c (h⁻¹ * (h * g)) • b (h * g) := by
      exact (Function.Bijective.sum_comp (Group.mulLeft_bijective h)
        (fun g => c (h⁻¹ * g) • b g)).symm
    _ = ∑ g : G, c g • b (h * g) := by
      simp

theorem fixedOrbit_eq_span_orbitSum
    (rho : G →* (V ≃ₗ[K] V)) (b : G → V)
    (hperm : ∀ h g, rho h (b g) = b (h * g))
    (hind : LinearIndependent K b) :
    orbitFixedSubmodule rho b = Submodule.span K {∑ g : G, b g} := by
  classical
  apply le_antisymm
  · intro x hx
    rcases (Submodule.mem_span_range_iff_exists_fun K).mp hx.1 with ⟨c, hc⟩
    have hcoeff (h : G) : (fun g => c (h⁻¹ * g)) = c := by
      apply hind.fintypeLinearCombination_injective
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply]
      rw [orbitCombination_shift rho b hperm h c, hc]
      exact hx.2 h
    have hconst (g : G) : c g = c 1 := by
      have hcg := congrFun (hcoeff g) g
      simpa using hcg.symm
    have hlin : (∑ g : G, c g • b g) = c 1 • (∑ g : G, b g) := by
      simp_rw [hconst]
      rw [← Finset.smul_sum]
    rw [← hc, hlin]
    exact Submodule.smul_mem _ (c 1) (Submodule.subset_span (Set.mem_singleton _))
  · refine Submodule.span_le.2 ?_
    intro x hx
    have hx' : x = ∑ g : G, b g := by simpa using hx
    subst x
    refine ⟨?_, ?_⟩
    · exact (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨fun _ => 1, by simp⟩
    · intro h
      change rho h (∑ g : G, b g) = ∑ g : G, b g
      simp only [map_sum]
      simp_rw [hperm]
      exact Function.Bijective.sum_comp (Group.mulLeft_bijective h)
        (fun g => b g)

end D5.S3.VertexAlgebra.Lattice.FiniteGroupOrbitFixedLine
