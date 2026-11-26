/- GID: D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A two-conformally rigid graph need not be one-conformally rigid. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#26026; Proved)
   escape_witness: none. All theorem proofs are bind-only under the inlining rule.
   The source weighted matrix and endpoint differences are expanded in eigenvalue.
   laplacian_wLap and laplacian_incidence connect them to the existing wLap and delta owners.
   Each undirected edge is counted once, and zero weights are permitted.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30083
   Edge: proof_shape: bind-only; escape_witness: none; consumers: KConformallyRigid, ValidWeight, all_weights_bounds, edgeAt, edgeEquiv, edge_card, eigenvalue, graph_not_one_rigid, graph_two_rigid, instFintypeEdge, lap_X_trace, lap_hermitian, lap_matrix, lap_psd, lap_trace, laplacian_incidence, laplacian_wLap, largestSum, orbitWeight, orbit_diagonalized, orbit_lap, perturbed_eigenvalues, perturbed_valid, smallestSum, uniform, uniform_eigenvalues, uniform_orbit.
   Direct frozen dependencies: none.
   instFintypeEdge: proof_shape: bind-only; escape_witness: none; consumers: ValidWeight, all_weights_bounds, edge_card, eigenvalue, graph_not_one_rigid, lap_X_trace, lap_hermitian, lap_matrix, lap_psd, lap_trace, laplacian_incidence, laplacian_wLap, orbit_diagonalized, orbit_lap, perturbed_eigenvalues, perturbed_valid, uniform_eigenvalues.
   Direct frozen dependencies: none.
   laplacian_incidence: proof_shape: bind-only; escape_witness: none; consumers: lap_psd.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta
     declaration statement_id: sha256:ed748bba225d96d8d6a4d64d6562868c6ad6d2e9cb7644dc4461078f8ad2837f
   laplacian_wLap: proof_shape: bind-only; escape_witness: none; consumers: lap_hermitian.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
   lap_hermitian: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds, eigenvalue, perturbed_eigenvalues, uniform_eigenvalues.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
   uniform: proof_shape: bind-only; escape_witness: none; consumers: KConformallyRigid, graph_not_one_rigid, graph_two_rigid, uniform_eigenvalues, uniform_orbit.
   Direct frozen dependencies: none.
   ValidWeight: proof_shape: bind-only; escape_witness: none; consumers: KConformallyRigid, all_weights_bounds, graph_not_one_rigid, graph_two_rigid, perturbed_valid.
   Direct frozen dependencies: none.
   eigenvalue: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds, graph_not_one_rigid, graph_two_rigid, largestSum, perturbed_eigenvalues, smallestSum, uniform_eigenvalues.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
   smallestSum: proof_shape: bind-only; escape_witness: none; consumers: KConformallyRigid, all_weights_bounds, graph_not_one_rigid, graph_two_rigid.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
   largestSum: proof_shape: bind-only; escape_witness: none; consumers: KConformallyRigid, all_weights_bounds, graph_not_one_rigid, graph_two_rigid.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
   KConformallyRigid: proof_shape: bind-only; escape_witness: none; consumers: claim, graph_not_one_rigid, graph_two_rigid, result.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
   claim: proof_shape: bind-only; escape_witness: none; consumers: result.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
   graph: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds, edgeAt, edgeEquiv, edge_card, graph_connected, graph_not_one_rigid, graph_two_rigid, lap_X_trace, lap_matrix, lap_trace, orbitWeight, orbit_diagonalized, orbit_lap, perturbed_eigenvalues, perturbed_valid, result, uniform_eigenvalues, uniform_orbit.
   Direct frozen dependencies: none.
   edgeAt: proof_shape: bind-only; escape_witness: none; consumers: edgeEquiv, lap_X_trace, lap_matrix, lap_trace, orbit_lap.
   Direct frozen dependencies: none.
   edgeEquiv: proof_shape: bind-only; escape_witness: none; consumers: edge_card, lap_X_trace, lap_matrix, lap_trace, perturbed_valid.
   Direct frozen dependencies: none.
   graph_connected: proof_shape: bind-only; escape_witness: none; consumers: result.
   Direct frozen dependencies: none.
   edge_card: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds, perturbed_valid.
   Direct frozen dependencies: none.
   lap_psd: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta
     declaration statement_id: sha256:ed748bba225d96d8d6a4d64d6562868c6ad6d2e9cb7644dc4461078f8ad2837f
   diagonalized_eigenvalues: proof_shape: bind-only; escape_witness: none; consumers: X_eigenvalues, perturbed_eigenvalues, uniform_eigenvalues.
   Direct frozen dependencies:
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
   P: proof_shape: bind-only; escape_witness: none; consumers: PR_identity, X_diagonalized, X_eigenvalues, orbit_diagonalized, perturbed_eigenvalues, uniform_eigenvalues.
   Direct frozen dependencies: none.
   R: proof_shape: bind-only; escape_witness: none; consumers: PR_identity, X_eigenvalues, perturbed_eigenvalues, uniform_eigenvalues.
   Direct frozen dependencies: none.
   X: proof_shape: bind-only; escape_witness: none; consumers: X_diagonalized, X_eigenvalues, X_hermitian, all_weights_bounds, lap_X_trace, trace_certificate_bound.
   Direct frozen dependencies: none.
   PR_identity: proof_shape: bind-only; escape_witness: none; consumers: X_eigenvalues, perturbed_eigenvalues, uniform_eigenvalues.
   Direct frozen dependencies: none.
   X_hermitian: proof_shape: bind-only; escape_witness: none; consumers: X_eigenvalues, trace_certificate_bound.
   Direct frozen dependencies: none.
   X_diagonalized: proof_shape: bind-only; escape_witness: none; consumers: X_eigenvalues.
   Direct frozen dependencies: none.
   X_eigenvalues: proof_shape: bind-only; escape_witness: none; consumers: trace_certificate_bound.
   Direct frozen dependencies:
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
   lap_matrix: proof_shape: bind-only; escape_witness: none; consumers: lap_X_trace, lap_trace, orbit_lap.
   Direct frozen dependencies: none.
   lap_trace: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds.
   Direct frozen dependencies: none.
   lap_X_trace: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds.
   Direct frozen dependencies: none.
   orbitWeight: proof_shape: bind-only; escape_witness: none; consumers: graph_not_one_rigid, orbit_diagonalized, orbit_lap, perturbed_eigenvalues, perturbed_valid, uniform_eigenvalues, uniform_orbit.
   Direct frozen dependencies: none.
   orbit_lap: proof_shape: bind-only; escape_witness: none; consumers: orbit_diagonalized.
   Direct frozen dependencies: none.
   orbit_diagonalized: proof_shape: bind-only; escape_witness: none; consumers: perturbed_eigenvalues, uniform_eigenvalues.
   Direct frozen dependencies: none.
   uniform_orbit: proof_shape: bind-only; escape_witness: none; consumers: uniform_eigenvalues.
   Direct frozen dependencies: none.
   uniform_eigenvalues: proof_shape: bind-only; escape_witness: none; consumers: graph_not_one_rigid, graph_two_rigid.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
   perturbed_valid: proof_shape: bind-only; escape_witness: none; consumers: graph_not_one_rigid.
   Direct frozen dependencies: none.
   perturbed_eigenvalues: proof_shape: bind-only; escape_witness: none; consumers: graph_not_one_rigid.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
   trace_five: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds.
   Direct frozen dependencies:
     D5/S3/Weil/ZetaLinear/PosIndex.sum_eigenvalues_reindex
     declaration statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
   trace_certificate_bound: proof_shape: bind-only; escape_witness: none; consumers: all_weights_bounds.
   Direct frozen dependencies:
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
     D5/S3/Weil/ZetaLinear/VonNeumann.vonNeumann_trace_ineq
     declaration statement_id: sha256:e4d2e8d594a181e2ae6b690deb46229692ff71b3739f9527b63dfac987faa7d7
   all_weights_bounds: proof_shape: bind-only; escape_witness: none; consumers: graph_two_rigid.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta
     declaration statement_id: sha256:ed748bba225d96d8d6a4d64d6562868c6ad6d2e9cb7644dc4461078f8ad2837f
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
     D5/S3/Weil/ZetaLinear/PosIndex.eigEquiv
     declaration statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
     D5/S3/Weil/ZetaLinear/PosIndex.eigenvalues_eigEquiv
     declaration statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
     D5/S3/Weil/ZetaLinear/PosIndex.sum_eigenvalues_reindex
     declaration statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
     D5/S3/Weil/ZetaLinear/VonNeumann.vonNeumann_trace_ineq
     declaration statement_id: sha256:e4d2e8d594a181e2ae6b690deb46229692ff71b3739f9527b63dfac987faa7d7
   graph_two_rigid: proof_shape: bind-only; escape_witness: none; consumers: result.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta
     declaration statement_id: sha256:ed748bba225d96d8d6a4d64d6562868c6ad6d2e9cb7644dc4461078f8ad2837f
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
     D5/S3/Weil/ZetaLinear/PosIndex.eigEquiv
     declaration statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
     D5/S3/Weil/ZetaLinear/PosIndex.eigenvalues_eigEquiv
     declaration statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
     D5/S3/Weil/ZetaLinear/PosIndex.sum_eigenvalues_reindex
     declaration statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
     D5/S3/Weil/ZetaLinear/VonNeumann.vonNeumann_trace_ineq
     declaration statement_id: sha256:e4d2e8d594a181e2ae6b690deb46229692ff71b3739f9527b63dfac987faa7d7
   graph_not_one_rigid: proof_shape: bind-only; escape_witness: none; consumers: result.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
   result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
   Direct frozen dependencies:
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap
     declaration statement_id: sha256:c711529df7d29888d4192467be5fae7d8697b641c151f0ad3b4a10f4caa731b0
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta
     declaration statement_id: sha256:ed748bba225d96d8d6a4d64d6562868c6ad6d2e9cb7644dc4461078f8ad2837f
     D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian
     declaration statement_id: sha256:1c53436d510902e28b0a3f4ecc4ee3b824fffa44e0f140a3bad172f9f72b5dd0
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum
     declaration statement_id: sha256:12dad8aa32bfca36ccce2305d99cfdd7f2db18813143d1396346f8c8f0e12712
     D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
     declaration statement_id: sha256:1432e8d88c5446f92eb737aabe9d8591628d94dc82ed93077dd0f8db3534ed39
     D5/S3/Weil/ZetaLinear/PosIndex.eigEquiv
     declaration statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
     D5/S3/Weil/ZetaLinear/PosIndex.eigenvalues_eigEquiv
     declaration statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
     D5/S3/Weil/ZetaLinear/PosIndex.sum_eigenvalues_reindex
     declaration statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
     D5/S3/Weil/ZetaLinear/VonNeumann.vonNeumann_trace_ineq
     declaration statement_id: sha256:e4d2e8d594a181e2ae6b690deb46229692ff71b3739f9527b63dfac987faa7d7
-/


import D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths
import D5.S3.Weil.ZetaLinear.VonNeumann
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

namespace D5.S3.Combinatorics.SpectralGraph.TotalConformalRigidityTwoNotOne

noncomputable section
open scoped BigOperators

/-- One representative (a,b), a < b, for each undirected edge. -/
abbrev Edge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ G.Adj e.1 e.2}

private noncomputable instance instFintypeEdge {n : ℕ} (G : SimpleGraph (Fin n)) : Fintype (Edge G) :=
  Fintype.ofFinite _

private theorem laplacian_incidence {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Edge G → ℝ) : (Matrix.of (fun row col =>
      ∑ e : Edge G, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) =
      ∑ e : Edge G, w e • Matrix.vecMulVec
        (D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.delta e.val.1 e.val.2)
        (D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.delta e.val.1 e.val.2) := by
  ext a b
  simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.delta,
    Pi.sub_apply, Pi.single_apply]
  simp only [eq_comm]
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem laplacian_wLap {n : ℕ} (G : SimpleGraph (Fin n)) (w : Edge G → ℝ) :
    (Matrix.of (fun row col =>
      ∑ e : Edge G, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) = @D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation.wLap n G (Classical.decRel G.Adj)
      (fun p => ∑ e : Edge G, if s(e.val.1,e.val.2) = p then w e else 0) := by
  classical
  ext a b
  simp only [Matrix.of_apply, D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation.wLap]
  by_cases hab : a = b
  · subst b
    simp only [Finset.sum_filter]
    trans ∑ e : Edge G, ∑ k : Fin n,
      if G.Adj a k then (if s(e.val.1,e.val.2) = s(a,k) then w e else 0) else 0
    · apply Finset.sum_congr rfl
      intro e _
      by_cases ha : a = e.val.1
      · subst a
        simp [Sym2.eq_iff, Prod.ext_iff, e.property.1.ne, e.property.1.ne.symm, e.property.2]
        rw [Finset.sum_eq_single e.val.2] <;> simp_all [e.property.2, eq_comm]
      · by_cases hb : a = e.val.2
        · subst a
          simp [Sym2.eq_iff, Prod.ext_iff, e.property.1.ne, e.property.1.ne.symm, G.adj_comm, e.property.2]
          rw [Finset.sum_eq_single e.val.1] <;> simp_all [e.property.2, eq_comm]
        · simp [Sym2.eq_iff, Prod.ext_iff, ha, hb, eq_comm]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : G.Adj a k <;> simp [h]
  · simp only [ite_eq_right hab]
    by_cases hg : G.Adj a b
    · rw [ite_eq_left hg, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases ha : a = e.val.1 <;> by_cases ha' : a = e.val.2 <;>
        by_cases hb : b = e.val.1 <;> by_cases hb' : b = e.val.2 <;>
        simp_all [Sym2.eq_iff, Prod.ext_iff, e.property.1.ne, eq_comm]
    · rw [ite_eq_right hg]
      apply Finset.sum_eq_zero
      intro e _
      by_cases ha : a = e.val.1 <;> by_cases ha' : a = e.val.2 <;>
        by_cases hb : b = e.val.1 <;> by_cases hb' : b = e.val.2 <;>
        simp_all [G.adj_comm, e.property.2]

private theorem lap_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) (w : Edge G → ℝ) :
    ((Matrix.of (fun row col =>
      ∑ e : Edge G, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0))))).IsHermitian := by
  classical
  rw [laplacian_wLap]
  exact D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.lap_hermitian G _

/-- The uniform edge weighting. -/
def uniform {n : ℕ} (G : SimpleGraph (Fin n)) : Edge G → ℝ := fun _ => 1

/-- The source simplex Delta_E, allowing zero weights. -/
def ValidWeight {n : ℕ} (G : SimpleGraph (Fin n)) (w : Edge G → ℝ) : Prop :=
  (∀ e : Edge G, 0 ≤ w e) ∧ ∑ e : Edge G, w e = (Fintype.card (Edge G) : ℝ)

/-- The source's eigenvalues in increasing order, with zero-based indices.
The inline proof establishes only that the defining matrix is Hermitian. -/
def eigenvalue {n : ℕ} (G : SimpleGraph (Fin n)) (w : Edge G → ℝ) (i : Fin n) : ℝ :=
  let h : ((Matrix.of (fun row col =>
      ∑ e : Edge G, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0))))).IsHermitian := lap_hermitian G w
  h.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i.rev)

/-- s_k: the k smallest nontrivial eigenvalues, lambda_2 through lambda_(k+1). -/
def smallestSum {n : ℕ} (G : SimpleGraph (Fin n)) (w : Edge G → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, if 0 < i.val ∧ i.val ≤ k then eigenvalue G w i else 0

/-- S_k: the k largest eigenvalues; k < n excludes the mandatory zero. -/
def largestSum {n : ℕ} (G : SimpleGraph (Fin n)) (w : Edge G → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, if n ≤ i.val + k then eigenvalue G w i else 0

/-- Definition 1.2: the same uniform weighting attains both required extremes. -/
def KConformallyRigid {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧
    ∀ (w : Edge G → ℝ) (u : Edge G → ℝ),
      ValidWeight G w → ValidWeight G u →
        smallestSum G w k ≤ smallestSum G (uniform G) k ∧
          largestSum G (uniform G) k ≤ largestSum G u k

/-- Section 9, printed p.20: affirmative answer to the unnumbered existence question. -/
def claim : Prop :=
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ (∃ a : Fin n, ∃ b : Fin n, G.Adj a b) ∧
      KConformallyRigid G 2 ∧ ¬ KConformallyRigid G 1

end
end D5.S3.Combinatorics.SpectralGraph.TotalConformalRigidityTwoNotOne

namespace D5.S3.Combinatorics.SpectralGraph.TotalConformalRigidityTwoNotOne
noncomputable section
open scoped BigOperators
open Matrix
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

@[reducible] private def graph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun a b => 2 ≤ a.val ∨ 2 ≤ b.val

@[reducible] private def edgeAt : Fin 9 → Edge graph :=
  ![⟨(0,2), by decide⟩, ⟨(0,3), by decide⟩, ⟨(0,4), by decide⟩,
    ⟨(1,2), by decide⟩, ⟨(1,3), by decide⟩, ⟨(1,4), by decide⟩,
    ⟨(2,3), by decide⟩, ⟨(2,4), by decide⟩, ⟨(3,4), by decide⟩]

private def edgeEquiv : Fin 9 ≃ Edge graph where
  toFun := edgeAt
  invFun e := if e.val.1 = 0 then ⟨e.val.2.val-2, by omega⟩
    else if e.val.1 = 1 then ⟨e.val.2.val+1, by omega⟩
    else if e.val.2 = 3 then 6 else if e.val.1 = 2 then 7 else 8
  left_inv := by intro i; fin_cases i <;> norm_num [edgeAt]
  right_inv := by
    rintro ⟨⟨a,b⟩,h⟩
    fin_cases a <;> fin_cases b <;>
      norm_num [graph, SimpleGraph.fromRel_adj, edgeAt] at h <;> rfl

private theorem graph_connected : graph.Connected := by
  apply SimpleGraph.Connected.of_isUniversal (v := 2)
  intro w hw
  simp [graph, SimpleGraph.fromRel_adj, hw]

private theorem edge_card : Fintype.card (Edge graph) = 9 := by
  exact (Fintype.card_congr edgeEquiv).symm.trans (Fintype.card_fin 9)

private theorem lap_psd {n : ℕ} (G : SimpleGraph (Fin n)) (w : Edge G → ℝ)
    (hw : ∀ e, 0 ≤ w e) : ((Matrix.of (fun row col =>
      ∑ e : Edge G, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0))))).PosSemidef := by
  rw [laplacian_incidence]
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using
    (Matrix.posSemidef_vecMulVec_self_star
      (D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.delta e.val.1 e.val.2)).smul (hw e)

private theorem diagonalized_eigenvalues {n : ℕ} (A P R : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hA : A.IsHermitian) (hPR : P * R = 1)
    (hAP : A * P = P * diagonal d) (hd : Antitone d) :
    ∀ i : Fin n, hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) = d i := by
  have hchar : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i)) := by
    rw [Matrix.charpoly_eq_of_mul_eq_mul (Matrix.det_ne_zero_of_right_inverse hPR) hAP,
      Matrix.charpoly_diagonal]
  let e : Fin n → ℝ := fun i => d i.rev
  have he : Monotone e := fun i j hij => hd (Fin.rev_le_rev.mpr hij)
  have hc : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (RCLike.ofReal (e i) : ℝ)) := by
    rw [hchar]
    simpa only [e, RCLike.ofReal_real_eq_id, id_eq, Fin.revPerm_apply] using
      (Equiv.prod_comp Fin.revPerm (fun i => Polynomial.X - Polynomial.C (d i))).symm
  have hvals : D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths.increasingSpectrum hA = e :=
    D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly
      hA e he hc
  intro i
  have hi := congrFun hvals i.rev
  simpa only [D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths.increasingSpectrum,
    e, Fin.rev_rev] using hi


@[reducible] private def P : Matrix (Fin 5) (Fin 5) ℝ :=
  !![3,0,0,1,1; 3,0,0,-1,1; -2,1,1,0,1; -2,-1,1,0,1; -2,0,-2,0,1]
@[reducible] private def R : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1/10,1/10,-1/15,-1/15,-1/15; 0,0,1/2,-1/2,0;
     0,0,1/6,1/6,-1/3; 1/2,-1/2,0,0,0; 1/5,1/5,1/5,1/5,1/5]
@[reducible] private def X : Matrix (Fin 5) (Fin 5) ℝ :=
  !![12/45,12/45,-8/45,-8/45,-8/45;
     12/45,12/45,-8/45,-8/45,-8/45;
     -8/45,-8/45,22/45,-3/45,-3/45;
     -8/45,-8/45,-3/45,22/45,-3/45;
     -8/45,-8/45,-3/45,-3/45,22/45]

private theorem PR_identity : P * R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,R, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem X_hermitian : X.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [X]

private theorem X_diagonalized : X * P = P * diagonal ![8/9,5/9,5/9,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X,P,Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]

private theorem X_eigenvalues (i : Fin 5) :
    X_hermitian.eigenvalues₀ (Fin.cast (Fintype.card_fin 5).symm i) =
      (![8/9,5/9,5/9,0,0] : Fin 5 → ℝ) i := by
  apply diagonalized_eigenvalues X P R _ X_hermitian PR_identity X_diagonalized
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at *

private theorem lap_matrix (w : Edge graph → ℝ) :
    (Matrix.of (fun row col =>
      ∑ e : Edge graph, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) = !![w (edgeAt 0) + w (edgeAt 1) + w (edgeAt 2), 0, -w (edgeAt 0), -w (edgeAt 1), -w (edgeAt 2);
      0, w (edgeAt 3) + w (edgeAt 4) + w (edgeAt 5), -w (edgeAt 3), -w (edgeAt 4), -w (edgeAt 5);
      -w (edgeAt 0), -w (edgeAt 3), w (edgeAt 0) + w (edgeAt 3) + w (edgeAt 6) + w (edgeAt 7), -w (edgeAt 6), -w (edgeAt 7);
      -w (edgeAt 1), -w (edgeAt 4), -w (edgeAt 6), w (edgeAt 1) + w (edgeAt 4) + w (edgeAt 6) + w (edgeAt 8), -w (edgeAt 8);
      -w (edgeAt 2), -w (edgeAt 5), -w (edgeAt 7), -w (edgeAt 8), w (edgeAt 2) + w (edgeAt 5) + w (edgeAt 7) + w (edgeAt 8)] := by
  ext a b
  change (∑ e : Edge graph, w e *
    ((if a = e.val.1 then 1 else 0) - (if a = e.val.2 then 1 else 0)) *
    ((if b = e.val.1 then 1 else 0) - (if b = e.val.2 then 1 else 0))) = _
  rw [← edgeEquiv.sum_comp]
  fin_cases a <;> fin_cases b <;>
    norm_num [edgeEquiv, edgeAt, Fin.sum_univ_succ] <;> ring

private theorem lap_trace (w : Edge graph → ℝ) :
    ((Matrix.of (fun row col =>
      ∑ e : Edge graph, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0))))).trace = 2 * ∑ e : Edge graph, w e := by
  rw [lap_matrix, ← edgeEquiv.sum_comp]
  norm_num [Matrix.trace, Matrix.diag, edgeEquiv, edgeAt, Fin.sum_univ_succ]
  ring

private theorem lap_X_trace (w : Edge graph → ℝ) :
    ((Matrix.of (fun row col =>
      ∑ e : Edge graph, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) * X).trace = (10/9) * ∑ e : Edge graph, w e := by
  rw [lap_matrix, ← edgeEquiv.sum_comp]
  norm_num [X, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    edgeEquiv, edgeAt, Fin.sum_univ_succ]
  ring

@[reducible] private def orbitWeight (a b : ℝ) : Edge graph → ℝ :=
  fun e => if e.val.1.val < 2 then a else b

private theorem orbit_lap (a b : ℝ) :
    (Matrix.of (fun row col =>
      ∑ e : Edge graph, (orbitWeight a b) e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) =
      !![3*a,0,-a,-a,-a; 0,3*a,-a,-a,-a;
         -a,-a,2*a+2*b,-b,-b; -a,-a,-b,2*a+2*b,-b;
         -a,-a,-b,-b,2*a+2*b] := by
  rw [lap_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orbitWeight, edgeAt] <;> ring

private theorem orbit_diagonalized (a b : ℝ) :
    (Matrix.of (fun row col =>
      ∑ e : Edge graph, (orbitWeight a b) e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) * P =
      P * diagonal ![5*a,2*a+3*b,2*a+3*b,3*a,0] := by
  rw [orbit_lap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply] <;> ring


private theorem uniform_orbit : uniform graph = orbitWeight 1 1 := by
  funext e
  simp only [uniform, orbitWeight, ite_self]

private theorem uniform_eigenvalues (i : Fin 5) :
    eigenvalue graph (uniform graph) i = (![0,3,5,5,5] : Fin 5 → ℝ) i := by
  have hdiag : (Matrix.of (fun row col =>
      ∑ e : Edge graph, (uniform graph) e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) * P =
      P * diagonal (![5,5,5,3,0] : Fin 5 → ℝ) := by
    rw [uniform_orbit]
    convert orbit_diagonalized 1 1 using 1 <;> norm_num
  have hd : Antitone (![5,5,5,3,0] : Fin 5 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  have h := diagonalized_eigenvalues _ P R _ (lap_hermitian _ _) PR_identity hdiag hd i.rev
  change (lap_hermitian _ _).eigenvalues₀ (Fin.cast (Fintype.card_fin 5).symm i.rev) = _
  rw [h]
  fin_cases i <;> norm_num

private theorem perturbed_valid : ValidWeight graph (orbitWeight (6/5) (3/5)) := by
  constructor
  · intro e
    obtain ⟨i,rfl⟩ := edgeEquiv.surjective e
    fin_cases i <;> norm_num [edgeEquiv, edgeAt, orbitWeight]
  · rw [edge_card, ← edgeEquiv.sum_comp]
    norm_num [edgeEquiv, edgeAt, orbitWeight, Fin.sum_univ_succ]

private theorem perturbed_eigenvalues (i : Fin 5) :
    eigenvalue graph (orbitWeight (6/5) (3/5)) i =
      (![0,18/5,21/5,21/5,6] : Fin 5 → ℝ) i := by
  have hdiag : (Matrix.of (fun row col =>
      ∑ e : Edge graph, (orbitWeight (6/5) (3/5)) e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) * P =
      P * diagonal (![6,21/5,21/5,18/5,0] : Fin 5 → ℝ) := by
    convert orbit_diagonalized (6/5) (3/5) using 1 <;> norm_num
  have hd : Antitone (![6,21/5,21/5,18/5,0] : Fin 5 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  have h := diagonalized_eigenvalues _ P R _ (lap_hermitian _ _) PR_identity hdiag hd i.rev
  change (lap_hermitian _ _).eigenvalues₀ (Fin.cast (Fintype.card_fin 5).symm i.rev) = _
  rw [h]
  fin_cases i <;> norm_num

private theorem trace_five (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.IsHermitian) :
    A.trace = ∑ i : Fin 5, hA.eigenvalues₀ (Fin.cast (Fintype.card_fin 5).symm i) := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  trans ∑ i : Fin (Fintype.card (Fin 5)), hA.eigenvalues₀ i
  · exact RHLinalg.sum_eigenvalues_reindex hA id
  · exact ((finCongr (Fintype.card_fin 5)).symm.sum_comp hA.eigenvalues₀).symm

private theorem trace_certificate_bound (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A.IsHermitian) :
    (A * X).trace ≤
      hA.eigenvalues₀ (Fin.cast (Fintype.card_fin 5).symm 0) +
        hA.eigenvalues₀ (Fin.cast (Fintype.card_fin 5).symm 1) := by
  have h := RHLinalg.vonNeumann_trace_ineq hA X_hermitian
  have hx (i : Fin (Fintype.card (Fin 5))) :
      X_hermitian.eigenvalues₀ i =
        (![8/9,5/9,5/9,0,0] : Fin 5 → ℝ) (Fin.cast (Fintype.card_fin 5) i) := by
    simpa using X_eigenvalues (Fin.cast (Fintype.card_fin 5) i)
  simp_rw [hx] at h
  rw [← (finCongr (Fintype.card_fin 5)).symm.sum_comp] at h
  norm_num [Fin.sum_univ_succ] at h
  have h02 := hA.eigenvalues₀_antitone
    (show (Fin.cast (Fintype.card_fin 5).symm 0) ≤
      Fin.cast (Fintype.card_fin 5).symm 2 by decide)
  have h12 := hA.eigenvalues₀_antitone
    (show (Fin.cast (Fintype.card_fin 5).symm 1) ≤
      Fin.cast (Fintype.card_fin 5).symm 2 by decide)
  have hz : Fin.cast (Fintype.card_fin 5).symm (0 : Fin 5) =
      (0 : Fin (Fintype.card (Fin 5))) := by
    exact Fin.cast_zero (Fintype.card_fin 5).symm
  rw [hz] at h02 ⊢
  linarith

private theorem all_weights_bounds (w : Edge graph → ℝ) (hw : ValidWeight graph w) :
    smallestSum graph w 2 ≤ 8 ∧ 10 ≤ largestSum graph w 2 := by
  have hs : ∑ e : Edge graph, w e = 9 := by
    simpa only [edge_card, Nat.cast_ofNat] using hw.2
  have ht : ((Matrix.of (fun row col =>
      ∑ e : Edge graph, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0))))).trace = 18 := by rw [lap_trace, hs]; norm_num
  have hx : ((Matrix.of (fun row col =>
      ∑ e : Edge graph, w e *
        ((if row = e.val.1 then 1 else 0) - (if row = e.val.2 then 1 else 0)) *
        ((if col = e.val.1 then 1 else 0) - (if col = e.val.2 then 1 else 0)))) * X).trace = 10 := by rw [lap_X_trace, hs]; norm_num
  have hb := trace_certificate_bound _ (lap_hermitian graph w)
  rw [hx] at hb
  have he0 : 0 ≤ eigenvalue graph w 0 := by
    have hp := (lap_psd graph w hw.1).eigenvalues_nonneg
      (RHLinalg.eigEquiv (n := Fin 5) (Fin.cast (Fintype.card_fin 5).symm (0 : Fin 5).rev))
    simpa only [eigenvalue, RHLinalg.eigenvalues_eigEquiv] using hp
  have ht' := trace_five _ (lap_hermitian graph w)
  rw [ht] at ht'
  have he (i : Fin 5) :
      (lap_hermitian graph w).eigenvalues₀ (Fin.cast (Fintype.card_fin 5).symm i) =
        eigenvalue graph w i.rev := by simp only [eigenvalue, Fin.rev_rev]
  simp_rw [he] at hb ht'
  norm_num [Fin.sum_univ_succ] at ht'
  norm_num [Fin.rev] at hb
  constructor
  · norm_num [smallestSum, Fin.sum_univ_succ]
    linarith
  · norm_num [largestSum, Fin.sum_univ_succ]
    linarith

private theorem graph_two_rigid : KConformallyRigid graph 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro w u hw hu
  have h := (all_weights_bounds w hw).1
  have h' := (all_weights_bounds u hu).2
  have hu : smallestSum graph (uniform graph) 2 = 8 := by
    norm_num [smallestSum, uniform_eigenvalues, Fin.sum_univ_succ]
  have hu' : largestSum graph (uniform graph) 2 = 10 := by
    norm_num [largestSum, uniform_eigenvalues, Fin.sum_univ_succ]
  exact ⟨hu.symm ▸ h, hu'.symm ▸ h'⟩

private theorem graph_not_one_rigid : ¬ KConformallyRigid graph 1 := by
  intro h
  have hu : ValidWeight graph (uniform graph) := by simp [ValidWeight, uniform]
  have hn := (h.2.2 (orbitWeight (6/5) (3/5)) (uniform graph) perturbed_valid hu).1
  norm_num [smallestSum, uniform_eigenvalues, perturbed_eigenvalues, Fin.sum_univ_succ] at hn

theorem result : claim := by
  exact ⟨5,graph,graph_connected,⟨0,2,by decide⟩,graph_two_rigid,graph_not_one_rigid⟩


end
end D5.S3.Combinatorics.SpectralGraph.TotalConformalRigidityTwoNotOne
