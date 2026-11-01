/- GID: D5/S3/VertexAlgebra/Lattice/FiniteGroupOrbitFixedLine
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FiniteGroupOrbitFixedLine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent finite-group orbit sums span the fixed space, with rank equal to orbit count. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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

variable {I : Type*} [Fintype I]

def multiOrbitSpan (b : I → G → V) : Submodule K V :=
  Submodule.span K (Set.range (fun p : I × G => b p.1 p.2))

def multiOrbitFixedSubmodule (rho : G →* (V ≃ₗ[K] V)) (b : I → G → V) :
    Submodule K V :=
  multiOrbitSpan b ⊓ fixedSubmodule rho

def multiOrbitSum (b : I → G → V) (i : I) : V :=
  ∑ g : G, b i g

theorem multiOrbitFixed_eq_span_sums
    (rho : G →* (V ≃ₗ[K] V)) (b : I → G → V)
    (hperm : ∀ h i g, rho h (b i g) = b i (h * g))
    (hind : LinearIndependent K (fun p : I × G => b p.1 p.2)) :
    multiOrbitFixedSubmodule rho b =
      Submodule.span K (Set.range (multiOrbitSum b)) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases (Submodule.mem_span_range_iff_exists_fun K).mp hx.1 with ⟨c, hc⟩
    have hright :
        (∑ p : I × G, c p • b p.1 p.2) =
          ∑ i : I, ∑ g : G, c (i, g) • b i g := by
      rw [← Finset.sum_product (Finset.univ : Finset I) (Finset.univ : Finset G)
        (fun p : I × G => c p • b p.1 p.2)]
      simp
    change (∑ p : I × G, c p • b p.1 p.2) = x at hc
    rw [hright] at hc
    have hcoeff (h : G) : (fun p : I × G => c (p.1, h⁻¹ * p.2)) = c := by
      apply hind.fintypeLinearCombination_injective
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply]
      have hleft :
          (∑ p : I × G, c (p.1, h⁻¹ * p.2) • b p.1 p.2) =
            ∑ i : I, ∑ g : G, c (i, h⁻¹ * g) • b i g := by
        rw [← Finset.sum_product (Finset.univ : Finset I) (Finset.univ : Finset G)
          (fun p : I × G => c (p.1, h⁻¹ * p.2) • b p.1 p.2)]
        simp
      have hshift :
          (∑ i : I, ∑ g : G, c (i, h⁻¹ * g) • b i g) =
            rho h (∑ i : I, ∑ g : G, c (i, g) • b i g) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact orbitCombination_shift rho (fun g => b i g)
          (fun h g => hperm h i g) h (fun g => c (i, g))
      calc
        (∑ p : I × G, c (p.1, h⁻¹ * p.2) • b p.1 p.2) =
            ∑ i : I, ∑ g : G, c (i, h⁻¹ * g) • b i g := hleft
        _ = rho h (∑ i : I, ∑ g : G, c (i, g) • b i g) := hshift
        _ = rho h x := by rw [hc]
        _ = x := hx.2 h
        _ = ∑ p : I × G, c p • b p.1 p.2 := hc.symm.trans hright.symm
    have hconst (i : I) (g : G) : c (i, g) = c (i, 1) := by
      have hcg := congrFun (hcoeff g) (i, g)
      simpa using hcg.symm
    have hlin : (∑ i : I, ∑ g : G, c (i, g) • b i g) =
        ∑ i : I, c (i, 1) • multiOrbitSum b i := by
      simp_rw [hconst, multiOrbitSum]
      simp_rw [Finset.smul_sum]
    rw [← hc, hlin]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ (c (i, 1))
      (Submodule.subset_span (Set.mem_range.mpr ⟨i, rfl⟩))
  · refine Submodule.span_le.2 ?_
    intro x hx
    have hx' : ∃ i : I, multiOrbitSum b i = x := by simpa using hx
    rcases hx' with ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · apply Submodule.sum_mem
      intro g hg
      exact Submodule.subset_span (Set.mem_range.mpr ⟨(i, g), rfl⟩)
    · intro h
      change rho h (∑ g : G, b i g) = ∑ g : G, b i g
      simp only [map_sum]
      simp_rw [hperm]
      exact Function.Bijective.sum_comp (Group.mulLeft_bijective h)
        (fun g => b i g)

private lemma multiOrbitSum_linearIndependent
    (b : I → G → V)
    (hind : LinearIndependent K (fun p : I × G => b p.1 p.2)) :
    LinearIndependent K (multiOrbitSum b) := by
  classical
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro c d h
  have h' : (∑ i : I, c i • multiOrbitSum b i) =
      ∑ i : I, d i • multiOrbitSum b i := by
    simpa only [Fintype.linearCombination_apply] using h
  have hprod (e : I → K) :
      (∑ p : I × G, e p.1 • b p.1 p.2) =
        ∑ i : I, e i • multiOrbitSum b i := by
    simp only [multiOrbitSum]
    simp_rw [Finset.smul_sum]
    rw [← Finset.sum_product (Finset.univ : Finset I) (Finset.univ : Finset G)
      (fun p : I × G => e p.1 • b p.1 p.2)]
    simp
  have hcoeff : (fun p : I × G => c p.1) = fun p => d p.1 := by
    apply hind.fintypeLinearCombination_injective
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply]
    calc
      (∑ p : I × G, c p.1 • b p.1 p.2) =
          ∑ i : I, c i • multiOrbitSum b i := hprod c
      _ = ∑ i : I, d i • multiOrbitSum b i := h'
      _ = ∑ p : I × G, d p.1 • b p.1 p.2 := (hprod d).symm
  funext i
  exact congrFun hcoeff (i, 1)

theorem multiOrbitFixed_finrank_eq_card
    (rho : G →* (V ≃ₗ[K] V)) (b : I → G → V)
    (hperm : ∀ h i g, rho h (b i g) = b i (h * g))
    (hind : LinearIndependent K (fun p : I × G => b p.1 p.2)) :
    Module.finrank K (multiOrbitFixedSubmodule rho b) = Fintype.card I := by
  rw [multiOrbitFixed_eq_span_sums rho b hperm hind]
  exact finrank_span_eq_card (multiOrbitSum_linearIndependent b hind)

end D5.S3.VertexAlgebra.Lattice.FiniteGroupOrbitFixedLine
