import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9RootStabilizer
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SixAxisTwelveMasks
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

/-! The root contact stabilizer of the dense six-axis twelve-mask family. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DenseSixRootNormalization

open Finset
open BalancedCubeComponentBoundary (directions)
open BalancedCriticalSpectrum (Q)
open Q9FiveAxisMissingContact (Geometry rightRoot)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactCNF (Axis)
open Q9SharedContactNormalized (LocalRules)
open Q9SixAxisTwelveMasks (recipe)
open Q9TightDistanceTwoCNF (support)
open Q9TightDistanceTwoNormalized (normalize_minimumDisplacements)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private directions_subset_agreement from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
open private normalize_hammingDist normalize_local_rules from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private normalize_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

private abbrev Triple := Fin 35

/-- The triples are ranked by their increasing axis lists in lexicographic order. -/
abbrev RootPair := Fin 35 × Fin 35

def tripleAxes : Fin 35 → List Axis :=
  ![[2, 3, 4], [2, 3, 5], [2, 3, 6], [2, 3, 7], [2, 3, 8], [2, 4, 5], [2, 4, 6],
    [2, 4, 7], [2, 4, 8], [2, 5, 6], [2, 5, 7], [2, 5, 8], [2, 6, 7], [2, 6, 8],
    [2, 7, 8], [3, 4, 5], [3, 4, 6], [3, 4, 7], [3, 4, 8], [3, 5, 6], [3, 5, 7],
    [3, 5, 8], [3, 6, 7], [3, 6, 8], [3, 7, 8], [4, 5, 6], [4, 5, 7], [4, 5, 8],
    [4, 6, 7], [4, 6, 8], [4, 7, 8], [5, 6, 7], [5, 6, 8], [5, 7, 8], [6, 7, 8]]

def triple (a : Fin 35) : Finset Axis := (tripleAxes a).toFinset

-- Axis permutations act on the labels in the forward direction.
private def axisMap : Fin 24 → Axis → Axis :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![0, 1, 2, 3, 4, 5, 6, 8, 7],
    ![0, 1, 2, 3, 4, 5, 7, 6, 8],
    ![0, 1, 2, 3, 4, 5, 7, 8, 6],
    ![0, 1, 2, 3, 4, 5, 8, 6, 7],
    ![0, 1, 2, 3, 4, 5, 8, 7, 6],
    ![0, 1, 2, 3, 5, 4, 6, 7, 8],
    ![0, 1, 2, 3, 5, 4, 6, 8, 7],
    ![0, 1, 2, 3, 5, 4, 7, 6, 8],
    ![0, 1, 2, 3, 5, 4, 7, 8, 6],
    ![0, 1, 2, 3, 5, 4, 8, 6, 7],
    ![0, 1, 2, 3, 5, 4, 8, 7, 6],
    ![0, 1, 3, 2, 4, 5, 6, 7, 8],
    ![0, 1, 3, 2, 4, 5, 6, 8, 7],
    ![0, 1, 3, 2, 4, 5, 7, 6, 8],
    ![0, 1, 3, 2, 4, 5, 7, 8, 6],
    ![0, 1, 3, 2, 4, 5, 8, 6, 7],
    ![0, 1, 3, 2, 4, 5, 8, 7, 6],
    ![0, 1, 3, 2, 5, 4, 6, 7, 8],
    ![0, 1, 3, 2, 5, 4, 6, 8, 7],
    ![0, 1, 3, 2, 5, 4, 7, 6, 8],
    ![0, 1, 3, 2, 5, 4, 7, 8, 6],
    ![0, 1, 3, 2, 5, 4, 8, 6, 7],
    ![0, 1, 3, 2, 5, 4, 8, 7, 6]]

private def inverseIndex : Fin 24 → Fin 24 :=
  ![0, 1, 2, 4, 3, 5, 6, 7, 8, 10, 9, 11, 12, 13, 14, 16, 15, 17, 18, 19, 20, 22, 21, 23]

private def imageIndex : Fin 24 → Triple → Triple :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
    ![0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 11, 10, 13, 12, 14, 15, 16, 18, 17, 19, 21, 20, 23, 22, 24, 25, 27, 26, 29, 28, 30, 32, 31, 33, 34],
    ![0, 1, 3, 2, 4, 5, 7, 6, 8, 10, 9, 11, 12, 14, 13, 15, 17, 16, 18, 20, 19, 21, 22, 24, 23, 26, 25, 27, 28, 30, 29, 31, 33, 32, 34],
    ![0, 1, 3, 4, 2, 5, 7, 8, 6, 10, 11, 9, 14, 12, 13, 15, 17, 18, 16, 20, 21, 19, 24, 22, 23, 26, 27, 25, 30, 28, 29, 33, 31, 32, 34],
    ![0, 1, 4, 2, 3, 5, 8, 6, 7, 11, 9, 10, 13, 14, 12, 15, 18, 16, 17, 21, 19, 20, 23, 24, 22, 27, 25, 26, 29, 30, 28, 32, 33, 31, 34],
    ![0, 1, 4, 3, 2, 5, 8, 7, 6, 11, 10, 9, 14, 13, 12, 15, 18, 17, 16, 21, 20, 19, 24, 23, 22, 27, 26, 25, 30, 29, 28, 33, 32, 31, 34],
    ![1, 0, 2, 3, 4, 5, 9, 10, 11, 6, 7, 8, 12, 13, 14, 15, 19, 20, 21, 16, 17, 18, 22, 23, 24, 25, 26, 27, 31, 32, 33, 28, 29, 30, 34],
    ![1, 0, 2, 4, 3, 5, 9, 11, 10, 6, 8, 7, 13, 12, 14, 15, 19, 21, 20, 16, 18, 17, 23, 22, 24, 25, 27, 26, 32, 31, 33, 29, 28, 30, 34],
    ![1, 0, 3, 2, 4, 5, 10, 9, 11, 7, 6, 8, 12, 14, 13, 15, 20, 19, 21, 17, 16, 18, 22, 24, 23, 26, 25, 27, 31, 33, 32, 28, 30, 29, 34],
    ![1, 0, 3, 4, 2, 5, 10, 11, 9, 7, 8, 6, 14, 12, 13, 15, 20, 21, 19, 17, 18, 16, 24, 22, 23, 26, 27, 25, 33, 31, 32, 30, 28, 29, 34],
    ![1, 0, 4, 2, 3, 5, 11, 9, 10, 8, 6, 7, 13, 14, 12, 15, 21, 19, 20, 18, 16, 17, 23, 24, 22, 27, 25, 26, 32, 33, 31, 29, 30, 28, 34],
    ![1, 0, 4, 3, 2, 5, 11, 10, 9, 8, 7, 6, 14, 13, 12, 15, 21, 20, 19, 18, 17, 16, 24, 23, 22, 27, 26, 25, 33, 32, 31, 30, 29, 28, 34],
    ![0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
    ![0, 1, 2, 4, 3, 15, 16, 18, 17, 19, 21, 20, 23, 22, 24, 5, 6, 8, 7, 9, 11, 10, 13, 12, 14, 25, 27, 26, 29, 28, 30, 32, 31, 33, 34],
    ![0, 1, 3, 2, 4, 15, 17, 16, 18, 20, 19, 21, 22, 24, 23, 5, 7, 6, 8, 10, 9, 11, 12, 14, 13, 26, 25, 27, 28, 30, 29, 31, 33, 32, 34],
    ![0, 1, 3, 4, 2, 15, 17, 18, 16, 20, 21, 19, 24, 22, 23, 5, 7, 8, 6, 10, 11, 9, 14, 12, 13, 26, 27, 25, 30, 28, 29, 33, 31, 32, 34],
    ![0, 1, 4, 2, 3, 15, 18, 16, 17, 21, 19, 20, 23, 24, 22, 5, 8, 6, 7, 11, 9, 10, 13, 14, 12, 27, 25, 26, 29, 30, 28, 32, 33, 31, 34],
    ![0, 1, 4, 3, 2, 15, 18, 17, 16, 21, 20, 19, 24, 23, 22, 5, 8, 7, 6, 11, 10, 9, 14, 13, 12, 27, 26, 25, 30, 29, 28, 33, 32, 31, 34],
    ![1, 0, 2, 3, 4, 15, 19, 20, 21, 16, 17, 18, 22, 23, 24, 5, 9, 10, 11, 6, 7, 8, 12, 13, 14, 25, 26, 27, 31, 32, 33, 28, 29, 30, 34],
    ![1, 0, 2, 4, 3, 15, 19, 21, 20, 16, 18, 17, 23, 22, 24, 5, 9, 11, 10, 6, 8, 7, 13, 12, 14, 25, 27, 26, 32, 31, 33, 29, 28, 30, 34],
    ![1, 0, 3, 2, 4, 15, 20, 19, 21, 17, 16, 18, 22, 24, 23, 5, 10, 9, 11, 7, 6, 8, 12, 14, 13, 26, 25, 27, 31, 33, 32, 28, 30, 29, 34],
    ![1, 0, 3, 4, 2, 15, 20, 21, 19, 17, 18, 16, 24, 22, 23, 5, 10, 11, 9, 7, 8, 6, 14, 12, 13, 26, 27, 25, 33, 31, 32, 30, 28, 29, 34],
    ![1, 0, 4, 2, 3, 15, 21, 19, 20, 18, 16, 17, 23, 24, 22, 5, 11, 9, 10, 8, 6, 7, 13, 14, 12, 27, 25, 26, 32, 33, 31, 29, 30, 28, 34],
    ![1, 0, 4, 3, 2, 15, 21, 20, 19, 18, 17, 16, 24, 23, 22, 5, 11, 10, 9, 8, 7, 6, 14, 13, 12, 27, 26, 25, 33, 32, 31, 30, 29, 28, 34]]

/-- Lexicographically least representatives of the 48-action orbits. -/
def representatives : List RootPair :=
  [(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 9), (0, 12), (0, 25),
    (0, 28), (0, 31), (0, 34), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7),
    (2, 12), (2, 14), (2, 25), (2, 26), (2, 28), (2, 30), (2, 34), (5, 5),
    (5, 6), (5, 12), (5, 15), (5, 16), (5, 22), (5, 25), (5, 28), (5, 34),
    (6, 6), (6, 7), (6, 9), (6, 10), (6, 12), (6, 14), (6, 16), (6, 17),
    (6, 19), (6, 20), (6, 22), (6, 24), (6, 25), (6, 26), (6, 28), (6, 30),
    (6, 31), (6, 33), (6, 34), (12, 12), (12, 13), (12, 22), (12, 23), (12, 25),
    (12, 27), (12, 28), (12, 29), (12, 34), (25, 25), (25, 26), (25, 28), (25, 30),
    (25, 34), (28, 28), (28, 29), (28, 31), (28, 32), (28, 34), (34, 34)]

-- A minimizing action, indexed by the two original triple ranks.
private def minimizingAction : Triple → Triple → Fin 48 :=
  ![![0, 0, 0, 2, 3, 0, 0, 2, 3, 0, 2, 3, 0, 1, 4, 12, 12, 14, 15, 12, 14, 15, 12, 13, 16, 0, 2, 3, 0, 1, 4, 0, 1, 4, 0],
    ![6, 6, 6, 8, 9, 6, 6, 8, 9, 6, 8, 9, 6, 7, 10, 18, 18, 20, 21, 18, 20, 21, 18, 19, 22, 6, 8, 9, 6, 7, 10, 6, 7, 10, 6],
    ![24, 30, 0, 0, 1, 0, 0, 0, 1, 6, 6, 7, 0, 1, 0, 12, 12, 12, 13, 18, 18, 19, 12, 13, 12, 0, 0, 1, 0, 1, 0, 6, 7, 6, 0],
    ![26, 32, 2, 2, 4, 2, 2, 2, 4, 8, 8, 10, 2, 2, 4, 14, 14, 14, 16, 20, 20, 22, 14, 14, 16, 2, 2, 4, 2, 2, 4, 8, 8, 10, 2],
    ![27, 33, 3, 5, 3, 3, 3, 5, 3, 9, 11, 9, 3, 3, 5, 15, 15, 17, 15, 21, 23, 21, 15, 15, 17, 3, 5, 3, 3, 3, 5, 9, 9, 11, 3],
    ![24, 30, 24, 26, 27, 0, 0, 2, 3, 6, 8, 9, 0, 1, 4, 0, 0, 2, 3, 6, 8, 9, 0, 1, 4, 0, 2, 3, 0, 1, 4, 6, 7, 10, 0],
    ![24, 30, 24, 26, 27, 24, 0, 0, 1, 0, 0, 1, 0, 1, 0, 36, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0],
    ![26, 32, 24, 26, 29, 26, 2, 2, 4, 2, 2, 4, 2, 2, 4, 38, 2, 2, 4, 2, 2, 4, 2, 2, 4, 2, 2, 4, 2, 2, 4, 2, 2, 4, 2],
    ![27, 33, 25, 28, 27, 27, 3, 5, 3, 3, 5, 3, 3, 3, 5, 39, 3, 5, 3, 3, 5, 3, 3, 3, 5, 3, 5, 3, 3, 3, 5, 3, 3, 5, 3],
    ![24, 30, 30, 32, 33, 30, 6, 6, 7, 6, 6, 7, 6, 7, 6, 42, 6, 6, 7, 6, 6, 7, 6, 7, 6, 6, 6, 7, 6, 7, 6, 6, 7, 6, 6],
    ![26, 32, 30, 32, 35, 32, 8, 8, 10, 8, 8, 10, 8, 8, 10, 44, 8, 8, 10, 8, 8, 10, 8, 8, 10, 8, 8, 10, 8, 8, 10, 8, 8, 10, 8],
    ![27, 33, 31, 34, 33, 33, 9, 11, 9, 9, 11, 9, 9, 9, 11, 45, 9, 11, 9, 9, 11, 9, 9, 9, 11, 9, 11, 9, 9, 9, 11, 9, 9, 11, 9],
    ![24, 30, 24, 26, 27, 24, 24, 26, 27, 30, 32, 33, 0, 0, 2, 36, 36, 38, 39, 42, 44, 45, 0, 0, 2, 0, 2, 0, 0, 0, 2, 6, 6, 8, 0],
    ![25, 31, 25, 26, 27, 25, 25, 26, 27, 31, 32, 33, 1, 1, 3, 37, 37, 38, 39, 43, 44, 45, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7, 7, 9, 1],
    ![28, 34, 24, 28, 29, 28, 24, 28, 29, 30, 34, 35, 4, 5, 4, 40, 36, 40, 41, 42, 46, 47, 4, 5, 4, 4, 4, 5, 4, 5, 4, 10, 11, 10, 4],
    ![36, 42, 36, 38, 39, 12, 12, 14, 15, 18, 20, 21, 12, 13, 16, 12, 12, 14, 15, 18, 20, 21, 12, 13, 16, 12, 14, 15, 12, 13, 16, 18, 19, 22, 12],
    ![36, 42, 36, 38, 39, 24, 12, 12, 13, 12, 12, 13, 12, 13, 12, 36, 12, 12, 13, 12, 12, 13, 12, 13, 12, 12, 12, 13, 12, 13, 12, 12, 13, 12, 12],
    ![38, 44, 36, 38, 41, 26, 14, 14, 16, 14, 14, 16, 14, 14, 16, 38, 14, 14, 16, 14, 14, 16, 14, 14, 16, 14, 14, 16, 14, 14, 16, 14, 14, 16, 14],
    ![39, 45, 37, 40, 39, 27, 15, 17, 15, 15, 17, 15, 15, 15, 17, 39, 15, 17, 15, 15, 17, 15, 15, 15, 17, 15, 17, 15, 15, 15, 17, 15, 15, 17, 15],
    ![36, 42, 42, 44, 45, 30, 18, 18, 19, 18, 18, 19, 18, 19, 18, 42, 18, 18, 19, 18, 18, 19, 18, 19, 18, 18, 18, 19, 18, 19, 18, 18, 19, 18, 18],
    ![38, 44, 42, 44, 47, 32, 20, 20, 22, 20, 20, 22, 20, 20, 22, 44, 20, 20, 22, 20, 20, 22, 20, 20, 22, 20, 20, 22, 20, 20, 22, 20, 20, 22, 20],
    ![39, 45, 43, 46, 45, 33, 21, 23, 21, 21, 23, 21, 21, 21, 23, 45, 21, 23, 21, 21, 23, 21, 21, 21, 23, 21, 23, 21, 21, 21, 23, 21, 21, 23, 21],
    ![36, 42, 36, 38, 39, 24, 24, 26, 27, 30, 32, 33, 12, 12, 14, 36, 36, 38, 39, 42, 44, 45, 12, 12, 14, 12, 14, 12, 12, 12, 14, 18, 18, 20, 12],
    ![37, 43, 37, 38, 39, 25, 25, 26, 27, 31, 32, 33, 13, 13, 15, 37, 37, 38, 39, 43, 44, 45, 13, 13, 15, 13, 13, 15, 13, 13, 15, 19, 19, 21, 13],
    ![40, 46, 36, 40, 41, 28, 24, 28, 29, 30, 34, 35, 16, 17, 16, 40, 36, 40, 41, 42, 46, 47, 16, 17, 16, 16, 16, 17, 16, 17, 16, 22, 23, 22, 16],
    ![24, 30, 24, 26, 27, 24, 24, 26, 27, 30, 32, 33, 24, 25, 28, 36, 36, 38, 39, 42, 44, 45, 36, 37, 40, 0, 0, 1, 0, 1, 0, 6, 7, 6, 0],
    ![26, 32, 24, 26, 29, 26, 24, 26, 29, 30, 32, 35, 26, 25, 28, 38, 36, 38, 41, 42, 44, 47, 38, 37, 40, 2, 2, 4, 2, 2, 4, 8, 8, 10, 2],
    ![27, 33, 25, 28, 27, 27, 25, 28, 27, 31, 34, 33, 24, 27, 29, 39, 37, 40, 39, 43, 46, 45, 36, 39, 41, 3, 5, 3, 3, 3, 5, 9, 9, 11, 3],
    ![24, 30, 24, 26, 27, 24, 24, 26, 27, 30, 32, 33, 24, 25, 28, 36, 36, 38, 39, 42, 44, 45, 36, 37, 40, 24, 26, 27, 0, 0, 2, 0, 0, 2, 0],
    ![25, 31, 25, 26, 27, 25, 25, 26, 27, 31, 32, 33, 24, 25, 29, 37, 37, 38, 39, 43, 44, 45, 36, 37, 41, 25, 26, 27, 1, 1, 3, 1, 1, 3, 1],
    ![28, 34, 24, 28, 29, 28, 24, 28, 29, 30, 34, 35, 26, 27, 28, 40, 36, 40, 41, 42, 46, 47, 38, 39, 40, 24, 28, 29, 4, 5, 4, 4, 5, 4, 4],
    ![24, 30, 30, 32, 33, 30, 24, 26, 27, 30, 32, 33, 30, 31, 34, 42, 36, 38, 39, 42, 44, 45, 42, 43, 46, 30, 32, 33, 6, 6, 8, 6, 6, 8, 6],
    ![25, 31, 31, 32, 33, 31, 25, 26, 27, 31, 32, 33, 30, 31, 35, 43, 37, 38, 39, 43, 44, 45, 42, 43, 47, 31, 32, 33, 7, 7, 9, 7, 7, 9, 7],
    ![28, 34, 30, 34, 35, 34, 24, 28, 29, 30, 34, 35, 32, 33, 34, 46, 36, 40, 41, 42, 46, 47, 44, 45, 46, 30, 34, 35, 10, 11, 10, 10, 11, 10, 10],
    ![24, 30, 24, 26, 27, 24, 24, 26, 27, 30, 32, 33, 24, 25, 28, 36, 36, 38, 39, 42, 44, 45, 36, 37, 40, 24, 26, 27, 24, 25, 28, 30, 31, 34, 0]]

set_option maxHeartbeats 0 in
private theorem inverse_ok (k : Fin 24) :
    (∀ i, axisMap (inverseIndex k) (axisMap k i) = i) ∧
      (∀ i, axisMap k (axisMap (inverseIndex k) i) = i) := by
  fin_cases k <;> decide +kernel

/-- Independently permute the other two centers, the other two leaves, and the inactive axes. -/
def axisPerm (k : Fin 24) : Equiv.Perm Axis where
  toFun := axisMap k
  invFun := axisMap (inverseIndex k)
  left_inv := (inverse_ok k).1
  right_inv := (inverse_ok k).2

set_option maxHeartbeats 0 in
private theorem image_ok (k : Fin 24) :
    ∀ a, triple (imageIndex k a) = (triple a).map (axisPerm k).toEmbedding := by
  fin_cases k <;> decide +kernel

private def permIndex (g : Fin 48) : Fin 24 :=
  ⟨g.val % 24, Nat.mod_lt _ (by decide)⟩

/-- The second half of the stabilizer exchanges the two supports. -/
def exchangesRoots (g : Fin 48) : Bool := decide (24 ≤ g.val)

/-- Translation by the root displacement is accompanied by exchange of the supports. -/
def act (g : Fin 48) (p : RootPair) : RootPair :=
  let k := permIndex g
  if exchangesRoots g then (imageIndex k p.2, imageIndex k p.1)
  else (imageIndex k p.1, imageIndex k p.2)

private def pairKey (p : RootPair) : Nat := 35 * p.1.val + p.2.val

theorem representatives_count : representatives.length = 71 ∧ representatives.Nodup := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem minimum_ok (a : Triple) :
    ∀ b, act (minimizingAction a b) (a, b) ∈ representatives ∧
      ∀ g, pairKey (act (minimizingAction a b) (a, b)) ≤ pairKey (act g (a, b)) := by
  fin_cases a <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem listed_minima :
    ∀ p ∈ representatives, ∀ g, pairKey p ≤ pairKey (act g p) := by
  intro p hp
  have h : representatives.all (fun q => decide (∀ g, pairKey q ≤ pairKey (act g q))) = true := by
    decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp h) p hp)

set_option maxHeartbeats 0 in
private theorem action_zero (a : Triple) :
    ∀ b, act 0 (a, b) = (a, b) := by
  fin_cases a <;> decide +kernel

private theorem pairKey_injective : Function.Injective pairKey := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change 35 * a.val + b.val = 35 * c.val + d.val at h
  have hb := b.isLt
  have hd := d.isLt
  have hfirst : a.val = c.val := by omega
  have hsecond : b.val = d.val := by omega
  exact Prod.ext (Fin.ext hfirst) (Fin.ext hsecond)

/-- The table lists exactly the lexicographic minima under the indexed actions. -/
theorem mem_representatives_iff (p : RootPair) :
    p ∈ representatives ↔ ∀ g, pairKey p ≤ pairKey (act g p) := by
  constructor
  · exact listed_minima p
  · intro h
    obtain ⟨a, b⟩ := p
    obtain ⟨hm, hle⟩ := minimum_ok a b
    have hle' := hle 0
    rw [action_zero] at hle'
    have he := pairKey_injective (le_antisymm hle' (h (minimizingAction a b)))
    exact he ▸ hm

private def availableAxes : Finset Axis := {2, 3, 4, 5, 6, 7, 8}

set_option maxHeartbeats 0 in
private theorem triple_ok :
    ∀ i : Triple, triple i ∈ availableAxes.powersetCard 3 := by
  decide +kernel

theorem triple_card (a : Fin 35) : (triple a).card = 3 :=
  (mem_powersetCard.mp (triple_ok a)).2

set_option maxHeartbeats 0 in
theorem triple_injective : Function.Injective triple := by
  intro a
  change ∀ b : Triple, triple a = triple b → a = b
  fin_cases a <;> decide +kernel

private theorem exists_triple {A : Finset Axis} (hA : A ⊆ availableAxes)
    (hc : A.card = 3) : ∃ a, triple a = A := by
  have hset : (univ : Finset Triple).map ⟨triple, triple_injective⟩ =
      availableAxes.powersetCard 3 := by
    apply eq_of_subset_of_card_le
    · intro B hB
      obtain ⟨a, _, rfl⟩ := mem_map.mp hB
      exact triple_ok a
    · rw [card_map]
      decide +kernel
  have hm : A ∈ (univ : Finset Triple).map ⟨triple, triple_injective⟩ := by
    rw [hset]
    exact mem_powersetCard.mpr ⟨hA, hc⟩
  obtain ⟨a, _, ha⟩ := mem_map.mp hm
  exact ⟨a, ha⟩

private def root (s : Bool) : Q 9 := if s then rightRoot else origin

/-- A normalization reads the axes in the inverse order of their action on direction sets. -/
def framePerm (g : Fin 48) : Equiv.Perm Axis := (axisPerm (permIndex g)).symm

/-- The translation is by cube word 3 exactly when the roots are exchanged. -/
def translation (g : Fin 48) : Q 9 := root (exchangesRoots g)

/-- The occupied directions at the left and right roots are exactly a canonical pair. -/
def Canonical (C D : Finset (Q 9)) : Prop :=
  ∃ p ∈ representatives, directions C origin = triple p.1 ∧
    directions D rightRoot = triple p.2

private theorem direction_subsets {C D : Finset (Q 9)} (h : Geometry C D) :
    directions C origin ⊆ availableAxes ∧ directions D rightRoot ⊆ availableAxes := by
  have hdist : hammingDist origin rightRoot = 2 := by decide +kernel
  have hagree (i : Axis) : origin i = rightRoot i ↔ i ∈ availableAxes := by
    fin_cases i <;> decide +kernel
  constructor
  · intro i hi
    apply (hagree i).mp
    have hm := directions_subset_agreement (C := C) (D := D) (x := origin) (y := rightRoot)
      h.right_root (fun u hu v hv => by rw [hdist]; exact h.separated u hu v hv) hi
    exact (mem_filter.mp hm).2
  · intro i hi
    apply (hagree i).mp
    have hm := directions_subset_agreement (C := D) (D := C) (x := rightRoot) (y := origin)
      h.left_root
      (fun u hu v hv => by
        rw [hammingDist_comm rightRoot origin, hdist, hammingDist_comm u v]
        exact h.separated v hv u hu) hi
    exact (mem_filter.mp hm).2.symm

private theorem root_even (t : Bool) : parity (root t) = false := by
  cases t <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem transform_root (k : Fin 24) (t s : Bool) :
    normalize (axisPerm k).symm (root t) (root (if t then !s else s)) = root s := by
  funext i
  revert t s i
  fin_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem preserve_family (k : Fin 24) :
    (recipe 1).family.map (mapEmbedding (axisPerm k).toEmbedding).toEmbedding =
      (recipe 1).family := by
  fin_cases k <;> decide +kernel

private theorem transform_geometry {C D : Finset (Q 9)} (h : Geometry C D)
    (τ : Equiv.Perm Axis) (z : Q 9) (t : Bool)
    (h0 : normalize τ z (root t) = origin)
    (h3 : normalize τ z (root (!t)) = rightRoot) :
    Geometry ((support C D t).map (normalize τ z).toEmbedding)
      ((support C D (!t)).map (normalize τ z).toEmbedding) := by
  have hroot (s : Bool) : root s ∈ support C D s := by
    cases s
    · exact h.left_root
    · exact h.right_root
  have hrules (s : Bool) : LocalRules (support C D s) := by
    cases s
    · exact h.left_rules
    · exact h.right_rules
  refine ⟨mem_map.mpr ⟨_, hroot t, h0⟩, mem_map.mpr ⟨_, hroot (!t), h3⟩,
    normalize_local_rules τ z _ (hrules t), normalize_local_rules τ z _ (hrules (!t)), ?_⟩
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
  change 2 ≤ hammingDist (normalize τ z u) (normalize τ z v)
  rw [normalize_hammingDist]
  cases t
  · exact h.separated u hu v hv
  · rw [hammingDist_comm]
    exact h.separated v hv u hu

/-- Reframe the actual supports so their occupied root directions are canonical. -/
theorem normalize_root_neighborhoods {C D : Finset (Q 9)} (h : Geometry C D)
    (hf : minimumDisplacements C D false 2 = (recipe 1).family) :
    ∃ g : Fin 48, parity (translation g) = false ∧
      let e := normalize (framePerm g) (translation g)
      let X := (support C D (exchangesRoots g)).map e.toEmbedding
      let Y := (support C D (!(exchangesRoots g))).map e.toEmbedding
      Geometry X Y ∧ minimumDisplacements X Y false 2 = (recipe 1).family ∧ Canonical X Y := by
  obtain ⟨hA, hB⟩ := direction_subsets h
  obtain ⟨a, ha⟩ := exists_triple hA (h.left_rules.occupied_degree _ h.left_root)
  obtain ⟨b, hb⟩ := exists_triple hB (h.right_rules.occupied_degree _ h.right_root)
  let g := minimizingAction a b
  let k := permIndex g
  let t := exchangesRoots g
  let z := root t
  let τ := (axisPerm k).symm
  let e := normalize τ z
  let X := (support C D t).map e.toEmbedding
  let Y := (support C D (!t)).map e.toEmbedding
  have h0 : e z = origin := normalize_center τ z
  have h3 : e (root (!t)) = rightRoot := by
    have he : (if t then !true else true) = !t := by cases t <;> rfl
    rw [← he]
    exact transform_root k t true
  have hz : parity z = false := root_even t
  refine ⟨g, hz, transform_geometry h τ z t h0 h3, ?_, ?_⟩
  · have hordered : minimumDisplacements (support C D t) (support C D (!t)) false 2 =
        (recipe 1).family := by
      cases ht : exchangesRoots g
      · simpa only [t, ht, Bool.not_false, support, Bool.false_eq_true, ite_false, ite_true] using hf
      · simpa only [t, ht, Bool.not_true, support, Bool.false_eq_true, ite_false, ite_true]
          using (minimumDisplacements_swap_two D C false).trans hf
    change minimumDisplacements X Y false 2 = (recipe 1).family
    have hmap := normalize_minimumDisplacements τ z (support C D t) (support C D (!t)) false 2
    simpa only [hz, show (false : Bool) + false = false from rfl, hordered,
      τ, Equiv.symm_symm, preserve_family k] using hmap
  · refine ⟨act g (a, b), (minimum_ok a b).1, ?_, ?_⟩
    · change directions X origin = _
      rw [← h0]
      change directions ((support C D t).map (normalize τ z).toEmbedding) (normalize τ z z) = _
      rw [normalize_directions]
      change (directions (support C D t) (root t)).map (axisPerm k).toEmbedding =
        triple (act g (a, b)).1
      cases ht : exchangesRoots g
      · simpa only [t, ht, support, Bool.false_eq_true, ite_false, root, ← ha, act, k]
          using (image_ok k a).symm
      · simpa only [t, ht, support, ite_true, root, ← hb, act, k]
          using (image_ok k b).symm
    · change directions Y rightRoot = _
      rw [← h3]
      change directions ((support C D (!t)).map (normalize τ z).toEmbedding)
        (normalize τ z (root (!t))) = _
      rw [normalize_directions]
      change (directions (support C D (!t)) (root (!t))).map (axisPerm k).toEmbedding =
        triple (act g (a, b)).2
      cases ht : exchangesRoots g
      · simpa only [t, ht, Bool.not_false, support, ite_true, root, ← hb, act, k, ite_false,
          Bool.false_eq_true] using (image_ok k b).symm
      · simpa only [t, ht, Bool.not_true, support, ite_true, root, ← ha, act, k, ite_false,
          Bool.false_eq_true] using (image_ok k a).symm

#print axioms normalize_root_neighborhoods

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DenseSixRootNormalization
