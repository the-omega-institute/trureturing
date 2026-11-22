/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LocalDirectionKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LocalDirectionKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A closed unmarked direction cut produces a signed Huang crossing kernel vector. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells

/-! The coordinate anticommutators give a local obstruction to injectivity of the
exterior columns of the Huang matrix restricted to selected rows. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LocalDirectionKernel

noncomputable section

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q flip gamma gamma_apply)
open TwentyPointEightWord (gamma_square)
open Q9IsotropicHuang (weightedLinear)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private weighted_sum weighted_square unit_weight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

private abbrev Vec := Q 9 → ℝ

open Classical in
private def delta (z : Q 9) : Vec := fun x => if x = z then 1 else 0

private def cutVector (I : Finset (Fin 9)) (z : Q 9) : Vec :=
  ∑ i ∈ I, gamma i (delta z)

private theorem gamma_delta_zero {x z : Q 9} {i : Fin 9} (h : x ≠ flip z i) :
    gamma i (delta z) x = 0 := by
  have h' : flip x i ≠ z := fun e => h (by rw [← e, BalancedCriticalSpectrum.flip_flip])
  simp [gamma_apply, delta, h']

private theorem cutVector_at_flip_ne_zero (I : Finset (Fin 9)) (z : Q 9)
    {i : Fin 9} (hi : i ∈ I) : cutVector I z (flip z i) ≠ 0 := by
  classical
  simp only [cutVector, Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem i hi]
  · intro hz
    have hs := congrFun (gamma_square i (delta z)) z
    rw [gamma_apply i (gamma i (delta z)) z, hz, mul_zero] at hs
    simp [delta] at hs
  · intro j _ hji
    exact gamma_delta_zero (fun e => hji (flip_injective z e).symm)

private theorem cutVector_expansion (I : Finset (Fin 9)) (z : Q 9) :
    (huangMatrix 9).mulVec (cutVector I z) =
      (I.card : ℝ) • delta z + ∑ j ∈ Iᶜ, ∑ i ∈ I, gamma j (gamma i (delta z)) := by
  classical
  let w : Fin 9 → ℝ := fun i => if i ∈ I then 1 else 0
  have hmasked (f : Vec) : weightedLinear w f = ∑ i ∈ I, gamma i f := by
    rw [weighted_sum]
    simp only [w, ite_smul, one_smul, zero_smul, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hweight : ∑ i, w i ^ 2 = (I.card : ℝ) := by
    simp only [w, apply_ite (fun t : ℝ => t ^ 2), one_pow, zero_pow two_ne_zero,
      ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsquare : ∑ j ∈ I, gamma j (cutVector I z) = (I.card : ℝ) • delta z := by
    simpa only [hmasked, cutVector, hweight] using weighted_square w (delta z)
  change Matrix.toLin' (huangMatrix 9) (cutVector I z) = _
  rw [← unit_weight, weighted_sum]
  simp only [one_smul]
  rw [← Finset.sum_add_sum_compl I, hsquare]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => map_sum (gamma j) _ _)

/-- A nonempty set of directions with no marks and no selected two-flip edge
leaving it gives a nonzero kernel vector supported on its exterior neighbors. -/
theorem exists_exterior_kernel_of_direction_cut (U : Set (Q 9)) (z : Q 9)
    (I : Finset (Fin 9)) (hI : I.Nonempty) (hz : z ∉ U)
    (hmark : ∀ i ∈ I, flip z i ∉ U)
    (hcut : ∀ i ∈ I, ∀ j ∉ I, flip (flip z i) j ∉ U) :
    ∃ f : Q 9 → ℝ, f ≠ 0 ∧ (∀ x, (∀ i ∈ I, x ≠ flip z i) → f x = 0) ∧
      (∀ x ∈ U, f x = 0) ∧ ∀ x ∈ U, (huangMatrix 9).mulVec f x = 0 := by
  classical
  have hsupp (x : Q 9) (hx : ∀ i ∈ I, x ≠ flip z i) : cutVector I z x = 0 := by
    rw [cutVector, Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i hi => gamma_delta_zero (hx i hi))
  obtain ⟨i, hi⟩ := hI
  refine ⟨cutVector I z, ?_, hsupp, ?_, ?_⟩
  · exact fun h => cutVector_at_flip_ne_zero I z hi (by simpa using congrFun h (flip z i))
  · exact fun x hx => hsupp x (fun i hi e => hmark i hi (e ▸ hx))
  · intro x hx
    rw [cutVector_expansion]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, delta,
      ite_eq_right (fun e : x = z => hz (e ▸ hx)), mul_zero, zero_add, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro i hi
    have hne : flip x j ≠ flip z i := by
      intro e
      apply hcut i hi j (Finset.mem_compl.mp hj)
      rw [← e, BalancedCriticalSpectrum.flip_flip]
      exact hx
    rw [gamma_apply, gamma_delta_zero hne, mul_zero]

#print axioms exists_exterior_kernel_of_direction_cut

end

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LocalDirectionKernel
