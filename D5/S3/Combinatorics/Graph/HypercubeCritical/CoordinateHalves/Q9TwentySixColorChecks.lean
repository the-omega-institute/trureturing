import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColors

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorChecks

open private checkCase from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColors

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
private theorem checked (index : Fin 110) : checkCase index.val = true := by
  fin_cases index <;> decide +kernel

#print axioms checked

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorChecks
