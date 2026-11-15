/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Every positive cut in a balanced cubic nine-cube subgraph has at least three edges. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import Batteries.Tactic.OpenPrivate

/-! Actual cuts of balanced cubic subgraphs and their integer Huang energy. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeCut

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap (Q9)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private switching_sq inside_equation matrix_support from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

open Classical in
/-- Actual cut edges, each recorded once with its endpoint in `T` first. -/
def cutEdges (C T : Finset Q9) : Finset (Sigma (fun _ : Q9 => Q9)) :=
  T.sigma (fun x => (C \ T).filter (fun y => (hypercube 9).Adj x y))

open Classical in
private theorem exists_cut_energy (C T : Finset Q9) (sigma : Q9 → Real)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hTC : T ⊆ C) :
    ∃ f : Q9 → Int,
      (fun x => (f x : Real)) = switchingVector T sigma ∧
      HuangIntegralNormGap.energy f = ((cutEdges C T).card : Real) := by
  classical
  let tau : Q9 → Int := fun x => if sigma x = 1 then 1 else -1
  let f : Q9 → Int := fun x => if x ∈ T then tau x else 0
  let g : Q9 → Real := switchingVector T sigma
  let h : Q9 → Real := switchingVector (C \ T) sigma
  have hf : (fun x => (f x : Real)) = g := by
    funext x
    by_cases hx : x ∈ T
    · rcases hs.1 x (hTC hx) with hxsign | hxsign <;>
        norm_num [f, tau, g, switchingVector, hx, hxsign]
    · simp [f, g, switchingVector, hx]
  have hz : switchingVector C sigma = g + h := by
    funext x
    by_cases hxT : x ∈ T
    · simp [g, h, switchingVector, hxT, hTC hxT]
    · by_cases hxC : x ∈ C <;>
        simp [g, h, switchingVector, hxT, hxC]
  have hinside (x : Q9) (hx : x ∈ T) :
      (3 : Real) * g x - (huangMatrix 9).mulVec g x =
        (huangMatrix 9).mulVec h x := by
    have heq := inside_equation C sigma hr hs (hTC hx)
    rw [hz, Matrix.mulVec_add] at heq
    change (huangMatrix 9).mulVec g x + (huangMatrix 9).mulVec h x =
      (3 : Real) * (g x + h x) at heq
    have hh : h x = 0 := by simp [h, switchingVector, hx]
    rw [hh, add_zero] at heq
    linarith
  have hrow (x : Q9) (hx : x ∈ T) :
      sigma x * (huangMatrix 9).mulVec h x =
        ∑ y ∈ C \ T, if (hypercube 9).Adj x y then (1 : Real) else 0 := by
    have hrestrict : (huangMatrix 9).mulVec h x =
        ∑ y ∈ C \ T, huangMatrix 9 x y * sigma y := by
      rw [Matrix.mulVec, dotProduct]
      calc
        ∑ y, huangMatrix 9 x y * h y =
            ∑ y ∈ C \ T, huangMatrix 9 x y * h y := by
          symm
          apply Finset.sum_subset (Finset.subset_univ (C \ T))
          intro y _ hy
          simp [h, switchingVector, hy]
        _ = ∑ y ∈ C \ T, huangMatrix 9 x y * sigma y := by
          apply Finset.sum_congr rfl
          intro y hy
          simp [h, switchingVector, hy]
    rw [hrestrict, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have hyC : y ∈ C := (Finset.mem_sdiff.mp hy).1
    by_cases hadj : (hypercube 9).Adj x y
    · rw [ite_eq_left hadj, hs.2 x (hTC hx) y hyC hadj]
      calc
        sigma x * (sigma x * sigma y * sigma y) =
            sigma x ^ 2 * sigma y ^ 2 := by ring
        _ = 1 := by
          rw [switching_sq hs (hTC hx), switching_sq hs hyC]
          norm_num
    · have hzero : huangMatrix 9 x y = 0 := by
        have hsupport := matrix_support x y
        rw [ite_eq_right hadj] at hsupport
        exact abs_eq_zero.mp hsupport
      simp [hadj, hzero]
  refine ⟨f, hf, ?_⟩
  calc
    HuangIntegralNormGap.energy f =
        ∑ x, g x * ((3 : Real) * g x - (huangMatrix 9).mulVec g x) := by
      unfold HuangIntegralNormGap.energy
      rw [hf]
      rfl
    _ = ∑ x ∈ T, g x * ((3 : Real) * g x - (huangMatrix 9).mulVec g x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro x _ hx
      simp [g, switchingVector, hx]
    _ = ∑ x ∈ T, sigma x * (huangMatrix 9).mulVec h x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hinside x hx]
      simp [g, switchingVector, hx]
    _ = ∑ x ∈ T, ∑ y ∈ C \ T,
        if (hypercube 9).Adj x y then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hrow x hx
    _ = ∑ x ∈ T, (((C \ T).filter (fun y => (hypercube 9).Adj x y)).card : Real) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter]
      simp
    _ = ((cutEdges C T).card : Real) := by
      simp only [cutEdges, Finset.card_sigma, Nat.cast_sum]

open Classical in
/-- A positive actual cut in a balanced induced cubic subgraph has at least three edges. -/
theorem three_le_cutEdges_card (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hTC : T ⊆ C) (hpos : 0 < (cutEdges C T).card) :
    3 ≤ (cutEdges C T).card := by
  obtain ⟨sigma, hs⟩ := hb
  obtain ⟨f, _hfvector, hf⟩ := exists_cut_energy C T sigma hr hs hTC
  have henergy : 0 < HuangIntegralNormGap.energy f := by
    rw [hf]
    exact_mod_cast hpos
  have hgap := HuangIntegralNormGap.three_le_energy f henergy
  rw [hf] at hgap
  exact_mod_cast hgap

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeCut
