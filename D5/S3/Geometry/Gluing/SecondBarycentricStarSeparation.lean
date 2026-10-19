/- GID: D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/SecondBarycentricStarSeparation
   mirror-E: none(waiver:coordinate-separation-core-has-no-empirical-mirror)
   anchors: []
   utility: none
   digest: The 25/48 coordinate regions in the standard tetrahedron are separated by 1/24 and have disjoint 1/48 neighborhoods. -/

import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Geometry.Gluing.SecondBarycentricStarSeparation

abbrev Coordinate := Fin 4 → ℝ

def standardSimplex : Set Coordinate :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

def coordinateStarRegion (i : Fin 4) : Set Coordinate :=
  {x | x ∈ standardSimplex ∧ (25 : ℝ) / 48 ≤ x i}

def coordinateStarNeighborhood (i : Fin 4) (r : ℝ) : Set Coordinate :=
  ⋃ x : coordinateStarRegion i, Metric.ball (x : Coordinate) r

private lemma coordinate_sum_le_one {x : Coordinate} (hx : x ∈ standardSimplex)
    (i j : Fin 4) (hij : i ≠ j) : x i + x j ≤ 1 := by
  rcases hx with ⟨hnonneg, hsum⟩
  fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_succ] <;>
    linarith [hnonneg 0, hnonneg 1, hnonneg 2, hnonneg 3]

private lemma coordinate_difference_lower_bound {i j : Fin 4} (hij : i ≠ j)
    {x y : Coordinate} (hx : x ∈ coordinateStarRegion i)
    (hy : y ∈ coordinateStarRegion j) :
    (1 : ℝ) / 24 ≤ |x i - y i| := by
  rcases hx with ⟨hxSimplex, hxi⟩
  rcases hy with ⟨hySimplex, hyj⟩
  have hsum : y i + y j ≤ 1 := coordinate_sum_le_one hySimplex i j hij
  have hyi : y i ≤ (23 : ℝ) / 48 := by
    linarith
  have hdiff : (1 : ℝ) / 24 ≤ x i - y i := by
    linarith
  exact le_trans hdiff (le_abs_self _)

theorem coordinate_star_regions_disjoint {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (coordinateStarRegion i) (coordinateStarRegion j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hsum : z i + z j ≤ 1 := coordinate_sum_le_one hzi.1 i j hij
  linarith [hzi.2, hzj.2]

theorem coordinate_star_regions_separated {i j : Fin 4} (hij : i ≠ j)
    {x y : Coordinate} (hx : x ∈ coordinateStarRegion i)
    (hy : y ∈ coordinateStarRegion j) :
    (1 : ℝ) / 24 ≤ ‖x - y‖ := by
  have hcoord := coordinate_difference_lower_bound hij hx hy
  calc
    (1 : ℝ) / 24 ≤ |(x - y) i| := by simpa using hcoord
    _ = ‖(x - y) i‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖x - y‖ := norm_le_pi_norm _ i

theorem coordinate_star_neighborhood_isOpen {i : Fin 4} {r : ℝ} (_hr : 0 < r) :
    IsOpen (coordinateStarNeighborhood i r) := by
  unfold coordinateStarNeighborhood
  exact isOpen_iUnion (fun x => Metric.isOpen_ball)

theorem coordinate_star_region_subset_neighborhood {i : Fin 4} {r : ℝ} (_hr : 0 < r) :
    coordinateStarRegion i ⊆ coordinateStarNeighborhood i r := by
  intro x hx
  refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
  simpa [Metric.mem_ball, dist_eq_norm] using _hr

theorem coordinate_star_neighborhoods_disjoint {i j : Fin 4} (hij : i ≠ j)
    {r : ℝ} (_hr0 : 0 < r) (hr : r < (1 : ℝ) / 48) :
    Disjoint (coordinateStarNeighborhood i r) (coordinateStarNeighborhood j r) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  rcases Set.mem_iUnion.1 hzi with ⟨x, hzx⟩
  rcases Set.mem_iUnion.1 hzj with ⟨y, hzy⟩
  have hxy := coordinate_star_regions_separated hij
    (x := (x : Coordinate)) (y := (y : Coordinate)) x.property y.property
  have hxz : ‖z - (x : Coordinate)‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzx
  have hyz : ‖z - (y : Coordinate)‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzy
  have htriangle : ‖(x : Coordinate) - (y : Coordinate)‖ ≤
      ‖(x : Coordinate) - z‖ + ‖z - (y : Coordinate)‖ := by
    calc
      ‖(x : Coordinate) - (y : Coordinate)‖ =
          ‖((x : Coordinate) - z) + (z - (y : Coordinate))‖ := by
            congr 1 <;> abel
      _ ≤ ‖(x : Coordinate) - z‖ + ‖z - (y : Coordinate)‖ := norm_add_le _ _
  have hxz' : ‖(x : Coordinate) - z‖ < r := by
    simpa [norm_sub_rev] using hxz
  linarith

end D5.S3.Geometry.Gluing.SecondBarycentricStarSeparation
