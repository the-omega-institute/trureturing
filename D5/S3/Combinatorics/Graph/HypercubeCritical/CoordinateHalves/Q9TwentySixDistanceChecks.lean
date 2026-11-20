import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixModelDistances

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixDistanceChecks

open private valid from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixModelDistances

set_option maxRecDepth 8192 in
private instance (index : Fin 663) : Decidable (valid index) := by
  unfold valid
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
private theorem valid_model (index : Fin 663) : valid index := by
  fin_cases index <;> decide +kernel

#print axioms valid_model

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixDistanceChecks
