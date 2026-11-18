/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Edge saturation and balanced supports of Huang eigenvectors. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsSwitching IsBalanced)
open private huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_support from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

/-- The selected vertices on which the supported eigenvector is nonzero. -/
def nonzeroSupport {n : ℕ} (U : Finset (Q n)) (z : Q n → ℝ) : Finset (Q n) :=
  U.filter fun x => z x ≠ 0

@[simp] theorem mem_nonzeroSupport {n : ℕ} {U : Finset (Q n)}
    {z : Q n → ℝ} {x : Q n} :
    x ∈ nonzeroSupport U z ↔ x ∈ U ∧ z x ≠ 0 := by
  classical
  simp [nonzeroSupport]

/-- The signing has unit absolute value on every actual cube edge. -/
theorem matrix_abs_of_adj {n : ℕ} {x y : Q n}
    (hxy : (hypercube n).Adj x y) : |huangMatrix n x y| = 1 := by
  rw [matrix_support, if_pos hxy]

/-- The signing vanishes away from actual cube edges. -/
theorem matrix_eq_zero_of_not_adj {n : ℕ} {x y : Q n}
    (hxy : ¬ (hypercube n).Adj x y) : huangMatrix n x y = 0 := by
  apply abs_eq_zero.mp
  rw [matrix_support, if_neg hxy]

/-- Squaring removes the actual edge sign. -/
theorem matrix_sq_of_adj {n : ℕ} {x y : Q n}
    (hxy : (hypercube n).Adj x y) : huangMatrix n x y ^ 2 = 1 := by
  have h := matrix_abs_of_adj hxy
  nlinarith [sq_abs (huangMatrix n x y)]

/-- Count actual selected neighbors using the induced graph, with no subtype transport. -/
private theorem selected_neighbor_card {n : ℕ} {U : Finset (Q n)}
    {x : Q n} (hx : x ∈ U) :
    ((hypercube n).neighborFinset x ∩ U).card =
      ((hypercube n).induce (U : Set (Q n))).degree ⟨x, hx⟩ := by
  classical
  let N := (hypercube n).neighborFinset x ∩ U
  have himage : ((((hypercube n).induce (U : Set (Q n))).neighborFinset
      ⟨x, hx⟩).image (fun y => y.1)) = N := by
    ext y
    simp [N, SimpleGraph.mem_neighborFinset, and_comm]
    change (∃ (_ : y ∈ U), (hypercube n).Adj x y) ↔ _
    simp [and_comm]
  change N.card = _
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Restrict the actual ambient eigen-equation using the support hypothesis. -/
theorem selected_eigen_row {n d : ℕ} (U : Finset (Q n)) (z : Q n → ℝ)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix n).mulVec z = (d : ℝ) • z) (x : Q n) :
    ∑ y ∈ U, huangMatrix n x y * z y = (d : ℝ) * z x := by
  classical
  calc
    ∑ y ∈ U, huangMatrix n x y * z y =
        ∑ y, huangMatrix n x y * z y := by
      apply Finset.sum_subset (Finset.subset_univ U)
      intro y _ hy
      rw [hsupport y hy, mul_zero]
    _ = (d : ℝ) * z x := by
      change ((huangMatrix n).mulVec z) x = _
      simpa only [Pi.smul_apply, smul_eq_mul] using congrFun heigen x

/-- The nonnegative defect measured on the actual selected cube edges. -/
def edgeEnergy {n : ℕ} (U : Finset (Q n)) (z : Q n → ℝ) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ U,
    if (hypercube n).Adj x y then (z x - huangMatrix n x y * z y) ^ 2 else 0

private theorem edge_energy_term {n : ℕ} (z : Q n → ℝ) (x y : Q n) :
    (if (hypercube n).Adj x y then (z x - huangMatrix n x y * z y) ^ 2 else 0) =
      (if (hypercube n).Adj x y then z x ^ 2 else 0) +
        (if (hypercube n).Adj x y then z y ^ 2 else 0) -
          2 * (huangMatrix n x y * z x * z y) := by
  classical
  by_cases hxy : (hypercube n).Adj x y
  · simp only [if_pos hxy]
    calc
      (z x - huangMatrix n x y * z y) ^ 2 =
          z x ^ 2 + huangMatrix n x y ^ 2 * z y ^ 2 -
            2 * (huangMatrix n x y * z x * z y) := by ring
      _ = _ := by rw [matrix_sq_of_adj hxy, one_mul]
  · simp [hxy, matrix_eq_zero_of_not_adj hxy]

private theorem row_square_sum {n : ℕ} (U : Finset (Q n))
    (z : Q n → ℝ) (x : Q n) :
    (∑ y ∈ U, if (hypercube n).Adj x y then z x ^ 2 else 0) =
      (((hypercube n).neighborFinset x ∩ U).card : ℝ) * z x ^ 2 := by
  classical
  have hfilter : U.filter (fun y => (hypercube n).Adj x y) =
      (hypercube n).neighborFinset x ∩ U := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [← Finset.sum_filter, hfilter]
  simp

/-- Exact energy expansion; degrees here count actual selected cube neighbors. -/
theorem edgeEnergy_eq {n d : ℕ} (U : Finset (Q n)) (z : Q n → ℝ)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix n).mulVec z = (d : ℝ) • z) :
    edgeEnergy U z =
      2 * (∑ x ∈ U, (((hypercube n).neighborFinset x ∩ U).card : ℝ) * z x ^ 2) -
        2 * (d : ℝ) * ∑ x ∈ U, z x ^ 2 := by
  classical
  let A : ℝ := ∑ x ∈ U, ∑ y ∈ U,
    if (hypercube n).Adj x y then z x ^ 2 else 0
  let B : ℝ := ∑ x ∈ U, ∑ y ∈ U,
    if (hypercube n).Adj x y then z y ^ 2 else 0
  let T : ℝ := ∑ x ∈ U, ∑ y ∈ U, huangMatrix n x y * z x * z y
  have hBA : B = A := by
    dsimp [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hxy : (hypercube n).Adj x y
    · simp only [if_pos hxy, if_pos hxy.symm]
    · have hyx : ¬ (hypercube n).Adj y x := fun h => hxy h.symm
      simp only [if_neg hxy, if_neg hyx]
  have hA : A = ∑ x ∈ U,
      (((hypercube n).neighborFinset x ∩ U).card : ℝ) * z x ^ 2 := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro x hx
    exact row_square_sum U z x
  have hT : T = (d : ℝ) * ∑ x ∈ U, z x ^ 2 := by
    calc
      T = ∑ x ∈ U, z x * (∑ y ∈ U, huangMatrix n x y * z y) := by
        dsimp [T]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = ∑ x ∈ U, (d : ℝ) * z x ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [selected_eigen_row U z hsupport heigen x]
        ring
      _ = (d : ℝ) * ∑ x ∈ U, z x ^ 2 := (Finset.mul_sum ..).symm
  calc
    edgeEnergy U z = A + B - 2 * T := by
      simp only [edgeEnergy, A, B, T, edge_energy_term,
        Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hBA, hA, hT]; ring

/-- A degree-bounded supported eigenvector has no edge energy defect. -/
theorem edgeEnergy_eq_zero {n d : ℕ} (U : Finset (Q n)) (z : Q n → ℝ)
    (hdeg : ∀ x : (U : Set (Q n)),
      ((hypercube n).induce (U : Set (Q n))).degree x ≤ d)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix n).mulVec z = (d : ℝ) • z) :
    edgeEnergy U z = 0 := by
  classical
  have hmass :
      (∑ x ∈ U, (((hypercube n).neighborFinset x ∩ U).card : ℝ) * z x ^ 2) ≤
        (d : ℝ) * ∑ x ∈ U, z x ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have hc : ((hypercube n).neighborFinset x ∩ U).card ≤ d := by
      rw [selected_neighbor_card hx]
      exact hdeg ⟨x, hx⟩
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg (z x))
  have hle : edgeEnergy U z ≤ 0 := by
    rw [edgeEnergy_eq U z hsupport heigen]
    nlinarith
  apply le_antisymm hle
  exact Finset.sum_nonneg fun x hx => Finset.sum_nonneg fun y hy => by
    split_ifs <;> positivity

/-- Every actual edge of the selected graph aligns the eigenvector with Huang's sign. -/
theorem edge_identity {n d : ℕ} (U : Finset (Q n)) (z : Q n → ℝ)
    (hdeg : ∀ x : (U : Set (Q n)),
      ((hypercube n).induce (U : Set (Q n))).degree x ≤ d)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix n).mulVec z = (d : ℝ) • z)
    {x y : Q n} (hx : x ∈ U) (hy : y ∈ U) (hxy : (hypercube n).Adj x y) :
    z x = huangMatrix n x y * z y := by
  classical
  have hrow :
      (∑ y ∈ U, if (hypercube n).Adj x y then
        (z x - huangMatrix n x y * z y) ^ 2 else 0) ≤ edgeEnergy U z := by
    apply Finset.single_le_sum _ hx
    intro a ha
    exact Finset.sum_nonneg fun b hb => by split_ifs <;> positivity
  have hterm :
      (if (hypercube n).Adj x y then
        (z x - huangMatrix n x y * z y) ^ 2 else 0) ≤
      ∑ b ∈ U, if (hypercube n).Adj x b then
        (z x - huangMatrix n x b * z b) ^ 2 else 0 := by
    apply Finset.single_le_sum _ hy
    intro b hb
    split_ifs <;> positivity
  have hsq : (z x - huangMatrix n x y * z y) ^ 2 ≤ 0 := by
    have h := hterm.trans hrow
    simpa only [if_pos hxy, edgeEnergy_eq_zero U z hdeg hsupport heigen] using h
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _)))

private theorem selected_neighbor_sum_const {n : ℕ} (U : Finset (Q n))
    (x : Q n) (a : ℝ) :
    (∑ y ∈ U, if (hypercube n).Adj x y then a else 0) =
      (((hypercube n).neighborFinset x ∩ U).card : ℝ) * a := by
  classical
  have hfilter : U.filter (fun y => (hypercube n).Adj x y) =
      (hypercube n).neighborFinset x ∩ U := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [← Finset.sum_filter, hfilter]
  simp

/-- Zero propagates across actual edges whose two endpoints belong to `U`. -/
theorem zero_of_adj_zero {n d : ℕ} (U : Finset (Q n)) (z : Q n → ℝ)
    (hdeg : ∀ x : (U : Set (Q n)),
      ((hypercube n).induce (U : Set (Q n))).degree x ≤ d)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix n).mulVec z = (d : ℝ) • z)
    {x y : Q n} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : (hypercube n).Adj x y) (hx0 : z x = 0) : z y = 0 := by
  rw [edge_identity U z hdeg hsupport heigen hy hx hxy.symm, hx0, mul_zero]

/-- Every nonzero selected vertex has the full actual induced degree. -/
theorem degree_eq_of_ne_zero {n d : ℕ} (U : Finset (Q n)) (z : Q n → ℝ)
    (hdeg : ∀ x : (U : Set (Q n)),
      ((hypercube n).induce (U : Set (Q n))).degree x ≤ d)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix n).mulVec z = (d : ℝ) • z)
    {x : Q n} (hx : x ∈ U) (hzx : z x ≠ 0) :
    ((hypercube n).induce (U : Set (Q n))).degree ⟨x, hx⟩ = d := by
  classical
  have hrow : (d : ℝ) * z x =
      (((hypercube n).neighborFinset x ∩ U).card : ℝ) * z x := by
    calc
      (d : ℝ) * z x = ∑ y ∈ U, huangMatrix n x y * z y :=
        (selected_eigen_row U z hsupport heigen x).symm
      _ = ∑ y ∈ U, if (hypercube n).Adj x y then z x else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hxy : (hypercube n).Adj x y
        · simpa only [if_pos hxy] using
            (edge_identity U z hdeg hsupport heigen hx hy hxy).symm
        · simp [hxy, matrix_eq_zero_of_not_adj hxy]
      _ = _ := selected_neighbor_sum_const U x (z x)
  have hmul : ((d : ℝ) - (((hypercube n).neighborFinset x ∩ U).card : ℝ)) *
      z x = 0 := by nlinarith [hrow]
  have hc : (d : ℝ) = (((hypercube n).neighborFinset x ∩ U).card : ℝ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hzx)
  have hnat : d = ((hypercube n).neighborFinset x ∩ U).card := by
    exact_mod_cast hc
  calc
    ((hypercube n).induce (U : Set (Q n))).degree ⟨x, hx⟩ =
        ((hypercube n).neighborFinset x ∩ U).card := (selected_neighbor_card hx).symm
    _ = d := hnat.symm

/-- The signs of the actual nonzero coordinates switch every selected edge to positive. -/
theorem nonzeroSupport_isBalanced {n d : ℕ} (U : Finset (Q n)) (z : Q n → ℝ)
    (hdeg : ∀ x : (U : Set (Q n)),
      ((hypercube n).induce (U : Set (Q n))).degree x ≤ d)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix n).mulVec z = (d : ℝ) • z) :
    IsBalanced (nonzeroSupport U z) := by
  classical
  refine ⟨fun x => if 0 < z x then (1 : ℝ) else -1, ?_⟩
  constructor
  · intro x hx
    by_cases hp : 0 < z x <;> simp [hp]
  · intro x hx y hy hxy
    have hx' := mem_nonzeroSupport.mp hx
    have hy' := mem_nonzeroSupport.mp hy
    have hrel := edge_identity U z hdeg hsupport heigen hx'.1 hy'.1 hxy
    have habs := matrix_abs_of_adj hxy
    have hunit : huangMatrix n x y = 1 ∨ huangMatrix n x y = -1 := by
      rcases le_total 0 (huangMatrix n x y) with hnonneg | hnonpos
      · left
        rwa [abs_of_nonneg hnonneg] at habs
      · right
        rw [abs_of_nonpos hnonpos] at habs
        linarith
    change huangMatrix n x y =
      (if 0 < z x then (1 : ℝ) else -1) * (if 0 < z y then (1 : ℝ) else -1)
    rcases hunit with hm | hm
    · have hz : z x = z y := by simpa only [hm, one_mul] using hrel
      by_cases hp : 0 < z y <;> simp [hm, hz, hp]
    · have hz : z x = -z y := by simpa only [hm, neg_one_mul] using hrel
      by_cases hp : 0 < z y
      · have hxnot : ¬ 0 < z x := by linarith [hz]
        simp [hm, hp, hxnot]
      · have hyneg : z y < 0 := by
          rcases lt_trichotomy (z y) 0 with hn | hz0 | hpos
          · exact hn
          · exact (hy'.2 hz0).elim
          · exact (hp hpos).elim
        have hxpos : 0 < z x := by linarith [hz]
        simp [hm, hp, hxpos]


end D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
