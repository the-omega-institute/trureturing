/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TwoCoordinatePeriod
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TwoCoordinatePeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A 258-point induced subcubic Q9 subgraph has no two-coordinate translation period. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension
import Batteries.Tactic.OpenPrivate

/-! Two-coordinate periods are incompatible with a 258-point subcubic cube support. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeComponentBoundary (directions directions_card mem_directions)
open BalancedCubeGirth (flip_comm)
open SupportedEigenSaturation (matrix_abs_of_adj selected_neighbor_card)
open ComponentBoundary.Q9IsotropicHuang (flipSign weightedAction weightedLinear)
open ComponentBoundary.Q9SignedContactCells (weighted_square)
open private complement_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension
open private weightedLinear_apply flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

set_option autoImplicit false

noncomputable section

private theorem weight_square_le (U : Finset (Q 9)) (hU : U.card = 258)
    (w : Fin 9 → ℝ) (hw : ∀ k, 0 ≤ w k) (d : ℝ) (hd : 0 ≤ d)
    (hrow : ∀ x ∈ U, ∑ k ∈ directions U x, w k ≤ d) :
    ∑ k, w k ^ 2 ≤ d ^ 2 := by
  classical
  let extend : (↥U → ℝ) →ₗ[ℝ] (Q 9 → ℝ) :=
    LinearMap.pi fun x => if hx : x ∈ U then LinearMap.proj ⟨x, hx⟩ else 0
  let outside : (Q 9 → ℝ) →ₗ[ℝ] ({x : Q 9 // x ∉ U} → ℝ) :=
    LinearMap.pi fun x => LinearMap.proj x.1
  let H := weightedLinear w
  let L := outside.comp (H.comp extend)
  have hdim : Module.finrank ℝ ({x : Q 9 // x ∉ U} → ℝ) < Module.finrank ℝ (↥U → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      complement_card U hU, Fintype.card_coe, hU]
    decide
  obtain ⟨v, hvker, hv⟩ := (LinearMap.ker L).ne_bot_iff.mp
    (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  let f := extend v
  have hzero (x : Q 9) (hx : x ∉ U) : f x = 0 := by
    simp [f, extend, hx]
  have hf : f ≠ 0 := by
    intro hf
    apply hv
    funext x
    simpa [f, extend, x.property] using congrFun hf x.1
  have hHzero (x : Q 9) (hx : x ∉ U) : H f x = 0 :=
    congrFun (LinearMap.mem_ker.mp hvker) ⟨x, hx⟩
  have row_bound (g : Q 9 → ℝ) (hg : ∀ x ∉ U, g x = 0) (M : ℝ)
      (hM : ∀ x, |g x| ≤ M) (x : Q 9) (hx : x ∈ U) : |H g x| ≤ d * M := by
    have hM0 := (abs_nonneg (g x)).trans (hM x)
    have hsum : H g x = ∑ k ∈ directions U x, w k * (flipSign k x : ℝ) * g (flip x k) := by
      change weightedLinear w g x = _
      rw [weightedLinear_apply, weightedAction, directions, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : flip x k ∈ U
      · simp [hk]
      · simp [hk, hg _ hk]
    rw [hsum]
    calc
      |∑ k ∈ directions U x, w k * (flipSign k x : ℝ) * g (flip x k)| ≤
          ∑ k ∈ directions U x, |w k * (flipSign k x : ℝ) * g (flip x k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ directions U x, w k * M := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_mul, abs_of_nonneg (hw k), flipSign_cast,
          matrix_abs_of_adj (flip_adj x k), mul_one]
        exact mul_le_mul_of_nonneg_left (hM _) (hw k)
      _ = (∑ k ∈ directions U x, w k) * M := by rw [Finset.sum_mul]
      _ ≤ d * M := mul_le_mul_of_nonneg_right (hrow x hx) hM0
  obtain ⟨x, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun x => |f x|)
    ⟨fun _ => false, Finset.mem_univ _⟩
  have hmax' (y : Q 9) : |f y| ≤ |f x| := hmax y (Finset.mem_univ _)
  have hpos : 0 < |f x| := by
    refine lt_of_le_of_ne (abs_nonneg _) (Ne.symm ?_)
    intro hx
    apply hf
    funext y
    exact abs_eq_zero.mp (le_antisymm ((hmax' y).trans_eq hx) (abs_nonneg _))
  have hx : x ∈ U := by
    by_contra hx
    simp [hzero x hx] at hpos
  have hH (y : Q 9) : |H f y| ≤ d * |f x| := by
    by_cases hy : y ∈ U
    · exact row_bound f hzero _ hmax' y hy
    · simpa [hHzero y hy] using mul_nonneg hd (abs_nonneg (f x))
  have hHH := row_bound (H f) hHzero _ hH x hx
  change |weightedLinear w (weightedLinear w f) x| ≤ _ at hHH
  rw [weighted_square, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg (w k)), ← mul_assoc, ← pow_two] at hHH
  exact le_of_mul_le_mul_right hHH hpos

open Classical in
/-- A subcubic induced subgraph on 258 vertices of Q9 cannot be closed under the
composition of two distinct coordinate flips. -/
theorem not_two_coordinate_period (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3)
    (i j : Fin 9) (hij : i ≠ j) :
    ¬ ∀ x ∈ U, flip (flip x i) j ∈ U := by
  classical
  intro hperiod
  have hsame (x : Q 9) : flip x i ∈ U ↔ flip x j ∈ U := by
    constructor
    · intro hxi
      simpa only [BalancedCriticalSpectrum.flip_flip] using hperiod (flip x i) hxi
    · intro hxj
      simpa only [flip_comm (flip x j) i j, BalancedCriticalSpectrum.flip_flip] using
        hperiod (flip x j) hxj
  let w (k : Fin 9) : ℝ := if k = i then 0 else if k = j then 2 else 1
  let rest := (Finset.univ.erase i).erase j
  have hj : j ∈ Finset.univ.erase i := by simp [hij.symm]
  have split_sum (g : Fin 9 → ℝ) : ∑ k, g k = (∑ k ∈ rest, g k) + g j + g i := by
    rw [Finset.sum_erase_add _ _ hj, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hrow (x : Q 9) (hx : x ∈ U) : ∑ k ∈ directions U x, w k ≤ (3 : ℝ) := by
    have hdegree : (directions U x).card ≤ 3 := by
      have hfilter : U.filter (fun z => (hypercube 9).Adj x z) =
          (hypercube 9).neighborFinset x ∩ U := by
        ext z
        simp [SimpleGraph.mem_neighborFinset, and_comm]
      rw [directions_card, hfilter, selected_neighbor_card hx]
      exact (((hypercube 9).induce (U : Set (Q 9))).degree_le_maxDegree ⟨x, hx⟩).trans hdeg
    calc
      ∑ k ∈ directions U x, w k = ∑ k ∈ directions U x, (1 : ℝ) := by
        simp only [directions, Finset.sum_filter]
        rw [split_sum, split_sum (fun k => if flip x k ∈ U then (1 : ℝ) else 0)]
        have hrest : (∑ k ∈ rest, if flip x k ∈ U then w k else 0) =
            ∑ k ∈ rest, if flip x k ∈ U then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkj := (Finset.mem_erase.mp hk).1
          have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
          simp [w, hki, hkj]
        rw [hrest]
        by_cases hjx : flip x j ∈ U <;> simp [w, hij.symm, hsame x, hjx] <;> ring
      _ = ((directions U x).card : ℝ) := by simp
      _ ≤ 3 := by exact_mod_cast hdegree
  have hbound := weight_square_le U hU w (fun k => by dsimp [w]; split_ifs <;> norm_num)
    3 (by norm_num) hrow
  have hrest : rest.card = 7 := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hsquare : ∑ k, w k ^ 2 = 11 := by
    rw [split_sum]
    have hsum : (∑ k ∈ rest, w k ^ 2) = (rest.card : ℝ) := by
      calc
        ∑ k ∈ rest, w k ^ 2 = ∑ _k ∈ rest, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkj := (Finset.mem_erase.mp hk).1
          have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
          simp [w, hki, hkj]
        _ = _ := by simp
    rw [hsum, hrest]
    norm_num [w, hij.symm]
  rw [hsquare] at hbound
  norm_num at hbound

end
end D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod
