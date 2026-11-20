import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixModelDistances
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCubeMetric

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixPlacementChecks

open private modelAt from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixModelDistances
open private listedHalves from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction
open private embeddings oppositeSize from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck
open private liftPoint from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCubeMetric

private def possiblePlacement (placed : List Nat) : Bool :=
  oppositeSize placed != 46 ||
    listedHalves.any (fun half => (placed.map liftPoint).toFinset == half.toFinset)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
private theorem placements_checked (index : Fin 663) :
    (embeddings (modelAt index) [0] 0).all possiblePlacement = true := by
  fin_cases index <;> decide +kernel

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixPlacementChecks
