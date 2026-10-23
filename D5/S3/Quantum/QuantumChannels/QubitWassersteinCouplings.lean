/- GID: D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/QubitWassersteinCouplings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Qubit Wasserstein couplings, Pauli cost, and the qubit self-cost formula. -/

/-
admission_basis: escape-witness (self_cost)
literature_attestation: self_cost is literature-attested by Section 4.1, Proposition 3, equation (35).
  product_coupling: proof_shape: bind-only; escape_witness: none; consumers: couplings_nonempty, pure_diag_D2
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_kronecker [sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker [sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988]
  couplings_nonempty: proof_shape: bind-only; escape_witness: none; consumers: D2_rotate_le, diag_self_cost, pure_diag_D2
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_kronecker [sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker [sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988]
  cost_nonneg: proof_shape: bind-only; escape_witness: none; consumers: D2_nonneg_all, cost_bddBelow
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0]
  cost_bddBelow: proof_shape: bind-only; escape_witness: none; consumers: D2_le_cost
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  D2_le_cost: proof_shape: bind-only; escape_witness: none; consumers: D2_le_bound_all, D2_rotate_le, diag_self_cost, endpoint_bound, pure_diag_D2
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  state_diag_le_one: proof_shape: bind-only; escape_witness: none; consumers: state_entry_norm_le_one
    Direct frozen dependencies: none
  state_entry_norm_le_one: proof_shape: bind-only; escape_witness: none; consumers: cost_le_bound
    Same-delivery owner dependency: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound; declaration statement_id: sha256:029989c48264702a7ddb2f7963b30fbc3260f0c293862ce2cf6561a7a358a67e
    Direct frozen dependencies: none
  pauli_hermitian: proof_shape: bind-only; escape_witness: none; consumers: CW_midpoint_bound, D2_rotate_le, diag_self_cost, endpoint_bound, pure_diag_D2, result
    Direct frozen dependencies: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian [sha256:9fed1f3f9e03300e2781ca25ae0d6440873c35552c9588efe7a35204f990652c]
  pauli_cost: proof_shape: bind-only; escape_witness: none; consumers: diag_self_cost, endpoint_bound, midpoint_cross, pauli_cost_rotate
    Direct frozen dependencies: D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli [sha256:679eb24de318cb22b41f0908ee5703cff91956515aa3e96f5c416b5f48a6f18d], D5/S3/Quantum/FiniteDimensional.QubitMatrix [sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30], D5/S3/Quantum/FiniteDimensional.qubitX [sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7], D5/S3/Quantum/FiniteDimensional.qubitZ [sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.match_1 [sha256:7fc2e63389d1eab654dd837875a0c02ece045a699e8b31f1275e0c20980c3be9]
  cost_le_bound: proof_shape: bind-only; escape_witness: none; consumers: D2_le_bound_all
    Direct frozen dependencies: none
  D2_nonneg_all: proof_shape: bind-only; escape_witness: none; consumers: dA_le_bound
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  costBound_nonneg: proof_shape: bind-only; escape_witness: none; consumers: D2_le_bound_all
    Direct frozen dependencies: none
  D2_le_bound_all: proof_shape: bind-only; escape_witness: none; consumers: dA_le_bound
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  dA_le_bound: proof_shape: bind-only; escape_witness: none; consumers: CW_bddAbove
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  CW_bddAbove: proof_shape: bind-only; escape_witness: none; consumers: CW_midpoint_bound
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.Mat [sha256:a26aa3c8142307876f979b8a3dec6c69cc2ba6cc38c57e460b655fbc4031e6d7]
  pureCoupling_psd: proof_shape: bind-only; escape_witness: none; consumers: diag_self_cost, phase_pure_coupling
    Direct frozen dependencies: none
  ptrace2_pure: proof_shape: bind-only; escape_witness: none; consumers: diag_self_cost, phase_pure_coupling, trace_pure
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity [sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3]
  ptrace1_pure: proof_shape: bind-only; escape_witness: none; consumers: diag_self_cost, phase_pure_coupling
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity [sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3]
  trace_pure: proof_shape: bind-only; escape_witness: none; consumers: diag_self_cost
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight [sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813], D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity [sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3]
  overlap_pure: proof_shape: bind-only; escape_witness: none; consumers: diag_self_cost, endpoint_bound
    Direct frozen dependencies: D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity [sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3]
  overlap_explicit: proof_shape: bind-only; escape_witness: none; consumers: diag_overlap_le
    Direct frozen dependencies: none
  diagState_isState: proof_shape: bind-only; escape_witness: none; consumers: CW_endpoint_bound, diag_self_cost, midpoint_cross, midpoint_self_input, midpoint_self_output, plus_isState, pure_diag_D2, self_cost_spectral
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.diagonalState [sha256:013cba828a03ee76551ea835a546d37fc9ec5e1fa7e7ece2b17cefe093a661e9]
  diag_overlap_le: proof_shape: bind-only; escape_witness: none; consumers: diag_self_cost
    Same-delivery owner dependency: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound; declaration statement_id: sha256:029989c48264702a7ddb2f7963b30fbc3260f0c293862ce2cf6561a7a358a67e
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.diagonalState [sha256:013cba828a03ee76551ea835a546d37fc9ec5e1fa7e7ece2b17cefe093a661e9], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  diag_self_cost: proof_shape: content; escape_witness: diag_self_cost; consumers: midpoint_self_input, midpoint_self_output, self_cost_spectral
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.diagonalState [sha256:013cba828a03ee76551ea835a546d37fc9ec5e1fa7e7ece2b17cefe093a661e9], D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli [sha256:679eb24de318cb22b41f0908ee5703cff91956515aa3e96f5c416b5f48a6f18d], D5/S3/Quantum/FiniteDimensional.QubitMatrix [sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30], D5/S3/Quantum/FiniteDimensional.qubitX [sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7], D5/S3/Quantum/FiniteDimensional.qubitZ [sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c], D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_kronecker [sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker [sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673], D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight [sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.match_1 [sha256:7fc2e63389d1eab654dd837875a0c02ece045a699e8b31f1275e0c20980c3be9], D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian [sha256:9fed1f3f9e03300e2781ca25ae0d6440873c35552c9588efe7a35204f990652c], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988], D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity [sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3]
  ptrace2_left: proof_shape: bind-only; escape_witness: none; consumers: ptrace2_conjLift
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  ptrace1_right: proof_shape: bind-only; escape_witness: none; consumers: ptrace1_conjLift
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d]
  ptrace2_right: proof_shape: bind-only; escape_witness: none; consumers: ptrace2_conjLift
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  ptrace1_left: proof_shape: bind-only; escape_witness: none; consumers: ptrace1_conjLift
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d]
  conjLift_factor: proof_shape: bind-only; escape_witness: none; consumers: ptrace2_conjLift
    Direct frozen dependencies: none
  conjTranspose_transpose_unitary: proof_shape: bind-only; escape_witness: none; consumers: conjLift_unitary, ptrace2_conjLift
    Direct frozen dependencies: none
  conjLift_unitary: proof_shape: bind-only; escape_witness: none; consumers: overlap_conjLift, pauli_cost_rotate, rotate_coupling
    Direct frozen dependencies: none
  conjLift_bell: proof_shape: bind-only; escape_witness: none; consumers: overlap_conjLift
    Direct frozen dependencies: none
  overlap_conjLift: proof_shape: bind-only; escape_witness: none; consumers: pauli_cost_rotate
    Direct frozen dependencies: none
  ptrace2_conjLift: proof_shape: bind-only; escape_witness: none; consumers: rotate_coupling
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  ptrace1_conjLift: proof_shape: bind-only; escape_witness: none; consumers: rotate_coupling
    Direct frozen dependencies: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d]
  rotate_isState: proof_shape: bind-only; escape_witness: none; consumers: D2_rotate, phase_pure_coupling, plus_isState
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988]
  rotate_inverse: proof_shape: bind-only; escape_witness: none; consumers: D2_rotate
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5]
  rotate_coupling: proof_shape: bind-only; escape_witness: none; consumers: D2_rotate_le
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
  pauli_cost_rotate: proof_shape: bind-only; escape_witness: none; consumers: D2_rotate_le
    Direct frozen dependencies: D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli [sha256:679eb24de318cb22b41f0908ee5703cff91956515aa3e96f5c416b5f48a6f18d], D5/S3/Quantum/FiniteDimensional.QubitMatrix [sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30], D5/S3/Quantum/FiniteDimensional.qubitX [sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7], D5/S3/Quantum/FiniteDimensional.qubitZ [sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.match_1 [sha256:7fc2e63389d1eab654dd837875a0c02ece045a699e8b31f1275e0c20980c3be9]
  D2_rotate_le: proof_shape: content; escape_witness: D2_rotate_le; consumers: D2_rotate
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5], D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli [sha256:679eb24de318cb22b41f0908ee5703cff91956515aa3e96f5c416b5f48a6f18d], D5/S3/Quantum/FiniteDimensional.QubitMatrix [sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30], D5/S3/Quantum/FiniteDimensional.qubitX [sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7], D5/S3/Quantum/FiniteDimensional.qubitZ [sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c], D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_kronecker [sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker [sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.match_1 [sha256:7fc2e63389d1eab654dd837875a0c02ece045a699e8b31f1275e0c20980c3be9], D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian [sha256:9fed1f3f9e03300e2781ca25ae0d6440873c35552c9588efe7a35204f990652c], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988]
  D2_rotate: proof_shape: content; escape_witness: D2_rotate_le; consumers: endpoint_bound, midpoint_cross, midpoint_self_input, midpoint_self_output, self_cost_spectral
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5], D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli [sha256:679eb24de318cb22b41f0908ee5703cff91956515aa3e96f5c416b5f48a6f18d], D5/S3/Quantum/FiniteDimensional.QubitMatrix [sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30], D5/S3/Quantum/FiniteDimensional.qubitX [sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7], D5/S3/Quantum/FiniteDimensional.qubitZ [sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c], D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_kronecker [sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker [sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.match_1 [sha256:7fc2e63389d1eab654dd837875a0c02ece045a699e8b31f1275e0c20980c3be9], D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian [sha256:9fed1f3f9e03300e2781ca25ae0d6440873c35552c9588efe7a35204f990652c], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988]
  exists_diagonalization: proof_shape: bind-only; escape_witness: none; consumers: self_cost_spectral
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.diagonalState [sha256:013cba828a03ee76551ea835a546d37fc9ec5e1fa7e7ece2b17cefe093a661e9], D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988]
  self_cost_spectral: proof_shape: content; escape_witness: diag_self_cost; consumers: self_cost, trace_sqrt_sq_le_two
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.diagonalState [sha256:013cba828a03ee76551ea835a546d37fc9ec5e1fa7e7ece2b17cefe093a661e9], D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5], D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli [sha256:679eb24de318cb22b41f0908ee5703cff91956515aa3e96f5c416b5f48a6f18d], D5/S3/Quantum/FiniteDimensional.QubitMatrix [sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30], D5/S3/Quantum/FiniteDimensional.qubitX [sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7], D5/S3/Quantum/FiniteDimensional.qubitZ [sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c], D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_kronecker [sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker [sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673], D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight [sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.match_1 [sha256:7fc2e63389d1eab654dd837875a0c02ece045a699e8b31f1275e0c20980c3be9], D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian [sha256:9fed1f3f9e03300e2781ca25ae0d6440873c35552c9588efe7a35204f990652c], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988], D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity [sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3]
  self_cost: proof_shape: content; escape_witness: self_cost_spectral; consumers: endpoint_bound
    Direct frozen dependencies: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.diagonalState [sha256:013cba828a03ee76551ea835a546d37fc9ec5e1fa7e7ece2b17cefe093a661e9], D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution [sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5], D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli [sha256:679eb24de318cb22b41f0908ee5703cff91956515aa3e96f5c416b5f48a6f18d], D5/S3/Quantum/FiniteDimensional.QubitMatrix [sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30], D5/S3/Quantum/FiniteDimensional.qubitX [sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7], D5/S3/Quantum/FiniteDimensional.qubitZ [sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c], D5/S3/Quantum/Information/PartialTraceMutualInformation.isHermitian_kronecker [sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_kronecker [sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77], D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_kronecker [sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673], D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight [sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli [sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X [sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y [sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z [sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69], D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix.match_1 [sha256:7fc2e63389d1eab654dd837875a0c02ece045a699e8b31f1275e0c20980c3be9], D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian [sha256:9fed1f3f9e03300e2781ca25ae0d6440873c35552c9588efe7a35204f990652c], D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity [sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988], D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity [sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3]
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15443.
The diagonal optimal coupling and simultaneous unitary transport supply the self_cost escape witness.
-/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Matrix.CartesianVariance

open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Matrix.CartesianVariance (psd_entry_bound)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section


def couplings {d : ℕ} (rho omega : Matrix (Fin d) (Fin d) ℂ) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {pi | (pi.PosSemidef ∧ pi.trace = 1) ∧ D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight pi = omega ∧ D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft pi = rho.transpose}

def cost {d k : ℕ} (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (pi : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  ∑ j, RCLike.re (trace ((A j ⊗ₖ 1 - 1 ⊗ₖ (A j).transpose) * pi *
    (A j ⊗ₖ 1 - 1 ⊗ₖ (A j).transpose)))
def D2 {d k : ℕ} (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (rho omega : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf ((cost A) '' couplings rho omega)
def dA {d k : ℕ} (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (rho omega : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.sqrt (D2 A rho omega - (D2 A rho rho + D2 A omega omega) / 2)
def CW {d k : ℕ} (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {x | ∃ rho, D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho ∧ x = dA A rho (Phi rho)}
end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
open D5.S3.Quantum.Information.PartialTraceMutualInformation
noncomputable section

theorem product_coupling {d : ℕ} {rho omega : Matrix (Fin d) (Fin d) ℂ}
    (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) (ho : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity omega) : omega ⊗ₖ rho.transpose ∈ couplings rho omega := by
  refine ⟨⟨ho.1.kronecker hr.1.transpose, ?_⟩, ?_, ?_⟩
  · rw [Matrix.trace_kronecker, Matrix.trace_transpose, hr.2, ho.2, mul_one]
  · change partialTraceRight (Matrix.kronecker omega rho.transpose) = omega
    rw [partialTraceRight_kronecker, Matrix.trace_transpose, hr.2, one_smul]
  · change partialTraceLeft (Matrix.kronecker omega rho.transpose) = rho.transpose
    rw [partialTraceLeft_kronecker, ho.2, one_smul]

theorem couplings_nonempty {d : ℕ} {rho omega : Matrix (Fin d) (Fin d) ℂ}
    (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) (ho : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity omega) : (couplings rho omega).Nonempty :=
  ⟨_, product_coupling hr ho⟩

private theorem cost_nonneg {d k : ℕ} {A : Fin k → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ j, (A j).IsHermitian)
    {pi : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hp : pi.PosSemidef) : 0 ≤ cost A pi := by
  apply Finset.sum_nonneg
  intro j _
  let B := A j ⊗ₖ 1 - 1 ⊗ₖ (A j).transpose
  have hb : B.IsHermitian :=
    (isHermitian_kronecker (hA j) (Matrix.isHermitian_one)).sub
      (isHermitian_kronecker Matrix.isHermitian_one (hA j).transpose)
  have hn := (hp.mul_mul_conjTranspose_same B).trace_nonneg
  rw [hb.eq] at hn
  exact hn.1

private theorem cost_bddBelow {d k : ℕ} {A : Fin k → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (rho omega : Matrix (Fin d) (Fin d) ℂ) : BddBelow ((cost A) '' couplings rho omega) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨pi,hp,rfl⟩
  exact cost_nonneg hA hp.1.1


theorem D2_le_cost {d k : ℕ} {A : Fin k → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ j, (A j).IsHermitian)
    {rho omega : Matrix (Fin d) (Fin d) ℂ} {pi : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hp : pi ∈ couplings rho omega) :
    D2 A rho omega ≤ cost A pi :=
  csInf_le (cost_bddBelow hA rho omega) ⟨pi,hp,rfl⟩

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section

private theorem state_diag_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hp : P.PosSemidef) (ht : P.trace = 1) (i : n) :
    (P i i).re ≤ 1 := by
  have hs : (P i i).re ≤ ∑ j, (P j j).re :=
    Finset.single_le_sum (fun j _ => (hp.diag_nonneg (i := j)).1) (Finset.mem_univ i)
  have ht' : (∑ j, (P j j).re) = 1 := by
    simpa [Matrix.trace] using congrArg Complex.re ht
  rwa [ht'] at hs

private theorem state_entry_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hp : P.PosSemidef) (ht : P.trace = 1) (i j : n) :
    ‖P i j‖ ≤ 1 := by
  have h := psd_entry_bound hp i j
  have hi := state_diag_le_one hp ht i
  have hj := state_diag_le_one hp ht j
  have hni := (hp.diag_nonneg (i := i)).1
  have hnj := (hp.diag_nonneg (i := j)).1
  rw [Complex.normSq_eq_norm_sq] at h
  have hm := mul_le_mul hi hj hnj (by norm_num : (0 : ℝ) ≤ 1)
  have hn := norm_nonneg (P i j)
  nlinarith

theorem pauli_hermitian : ∀ j, (pauli j).IsHermitian := by
  intro j
  exact D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian
    (![D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X,
       D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y,
       D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z] j)

def overlap (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := (star (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⬝ᵥ (P *ᵥ (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)))).re

theorem pauli_cost (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : cost pauli P = 8 * P.trace.re - 4 * overlap P := by
  simp [cost, D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Function.uncurry, Matrix.one_apply, Fin.sum_univ_succ, Fintype.sum_prod_type, overlap, Function.uncurry, Matrix.one_apply,
    Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Pi.star_apply, Complex.star_def]
  <;> ring

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section

private def costBound {d k : ℕ} (A : Fin k → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ j, ∑ i : Fin d × Fin d, ∑ a : Fin d × Fin d, ∑ b : Fin d × Fin d,
    ‖(A j ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) - (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (A j).transpose) i a‖ *
      ‖(A j ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) - (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (A j).transpose) b i‖

private theorem cost_le_bound {d k : ℕ} (A : Fin k → Matrix (Fin d) (Fin d) ℂ) {P : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hp : P.PosSemidef) (ht : P.trace = 1) : cost A P ≤ costBound A := by
  unfold cost costBound
  apply Finset.sum_le_sum
  intro j _
  let B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := A j ⊗ₖ 1 - 1 ⊗ₖ (A j).transpose
  change (trace (B * P * B)).re ≤ ∑ i, ∑ a, ∑ b, ‖B i a‖ * ‖B b i‖
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  calc
    (B i a * P a b * B b i).re ≤ ‖B i a * P a b * B b i‖ := Complex.re_le_norm _
    _ = ‖B i a‖ * ‖P a b‖ * ‖B b i‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖B i a‖ * 1 * ‖B b i‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (state_entry_norm_le_one hp ht a b) (norm_nonneg _))
        (norm_nonneg _)
    _ = ‖B i a‖ * ‖B b i‖ := by ring


end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section

private theorem D2_nonneg_all {d k : ℕ} {A : Fin k → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (rho omega : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ D2 A rho omega := by
  by_cases h : (couplings rho omega).Nonempty
  · apply le_csInf (h.image _)
    rintro _ ⟨pi,hp,rfl⟩
    exact cost_nonneg hA hp.1.1
  · simp [D2, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

private theorem costBound_nonneg {d k : ℕ} (A : Fin k → Matrix (Fin d) (Fin d) ℂ) : 0 ≤ costBound A := by
  unfold costBound
  positivity

private theorem D2_le_bound_all {d k : ℕ} {A : Fin k → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (rho omega : Matrix (Fin d) (Fin d) ℂ) : D2 A rho omega ≤ costBound A := by
  by_cases h : (couplings rho omega).Nonempty
  · obtain ⟨P,hp⟩ := h
    exact (D2_le_cost hA hp).trans (cost_le_bound A hp.1.1 hp.1.2)
  · simpa [D2, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty] using costBound_nonneg A

private theorem dA_le_bound {d k : ℕ} {A : Fin k → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (rho omega : Matrix (Fin d) (Fin d) ℂ) : dA A rho omega ≤ Real.sqrt (costBound A) := by
  apply Real.sqrt_le_sqrt
  have h1 := D2_nonneg_all hA rho rho
  have h2 := D2_nonneg_all hA omega omega
  have h3 := D2_le_bound_all hA rho omega
  linarith

theorem CW_bddAbove {d k : ℕ} {A : Fin k → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    BddAbove {x | ∃ rho, D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho ∧ x = dA A rho (Phi rho)} := by
  refine ⟨Real.sqrt (costBound A), ?_⟩
  rintro x ⟨rho,_,rfl⟩
  exact dA_le_bound hA rho (Phi rho)

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open Matrix
namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section


def pureCoupling {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (Function.uncurry S)

theorem pureCoupling_psd {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ) : (pureCoupling S).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (Function.uncurry S)

theorem ptrace2_pure {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ) : D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (pureCoupling S) = S * S.conjTranspose := by
  ext i j
  simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, pureCoupling,
    D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity, Function.uncurry, Matrix.vecMulVec, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm]

theorem ptrace1_pure {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ) : D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft (pureCoupling S) = (S.conjTranspose * S).transpose := by
  ext i j
  simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft, pureCoupling,
    D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity, Function.uncurry, Matrix.vecMulVec, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm]

private theorem trace_pure {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ) : (pureCoupling S).trace = (S * S.conjTranspose).trace := by
  have h := congrArg Matrix.trace (ptrace2_pure S)
  change trace (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (pureCoupling S)) = _ at h
  rwa [D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight] at h

theorem overlap_pure (S : Matrix (Fin 2) (Fin 2) ℂ) : overlap (pureCoupling S) = Complex.normSq S.trace := by
  simp [overlap, pureCoupling, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    Function.uncurry, Matrix.vecMulVec, Matrix.trace,
    Matrix.mulVec, dotProduct, Function.uncurry, Matrix.one_apply, Fin.sum_univ_succ, Fintype.sum_prod_type,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def]
  ring

private theorem overlap_explicit {P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hp : P.IsHermitian) :
    overlap P = (P (0,0) (0,0)).re + (P (1,1) (1,1)).re + 2 * (P (0,0) (1,1)).re := by
  have hh := congrArg Complex.re (hp.apply (0,0) (1,1))
  simp [overlap, Function.uncurry, Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Fintype.sum_prod_type, Pi.star_apply] at *
  linarith


theorem diagState_isState {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) := by
  refine ⟨Matrix.PosSemidef.diagonal ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨ha,rfl⟩
    · exact ⟨hb,rfl⟩
  · simp [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState, Matrix.trace, Fin.sum_univ_succ, ← Complex.ofReal_add, hab]

private theorem diag_overlap_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hp : P ∈ couplings (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b])) :
    overlap P ≤ (Real.sqrt a + Real.sqrt b)^2 := by
  have hp0 := (hp.1.1.diag_nonneg (i := (0,0))).1
  have hp1 := (hp.1.1.diag_nonneg (i := (1,1))).1
  have hp01 := (hp.1.1.diag_nonneg (i := (0,1))).1
  have hp10 := (hp.1.1.diag_nonneg (i := (1,0))).1
  have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hp.2.1
  have hy := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hp.2.1
  simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState, Fin.sum_univ_succ] at hx hy
  simp only [Complex.zero_re] at hp0 hp1 hp01 hp10
  have hxa : (P (0,0) (0,0)).re ≤ a := by linarith
  have hyb : (P (1,1) (1,1)).re ≤ b := by linarith
  have hxy := psd_entry_bound hp.1.1 (0,0) (1,1)
  have hm := mul_le_mul hxa hyb hp1 ha
  have ha2 := Real.sq_sqrt ha
  have hb2 := Real.sq_sqrt hb
  have hs : (Real.sqrt a * Real.sqrt b)^2 = a*b := by rw [mul_pow, ha2, hb2]
  have hn : 0 ≤ Real.sqrt a * Real.sqrt b := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hre : (P (0,0) (1,1)).re ≤ Real.sqrt a * Real.sqrt b := by
    simp only [Complex.normSq_apply] at hxy
    nlinarith [sq_nonneg (P (0,0) (1,1)).im]
  rw [overlap_explicit hp.1.1.1]
  nlinarith

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section

theorem diag_self_cost {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    D2 pauli (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) = 8 - 4*(Real.sqrt a + Real.sqrt b)^2 := by
  let S := D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![Real.sqrt a, Real.sqrt b]
  have hs : S.IsHermitian := (Matrix.PosSemidef.diagonal (by
    intro i; fin_cases i <;> exact ⟨Real.sqrt_nonneg _,rfl⟩)).1
  have hss : S * S = D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState, Matrix.mul_apply, Fin.sum_univ_succ, ← Complex.ofReal_mul,
        Real.mul_self_sqrt ha, Real.mul_self_sqrt hb]
  have htr : (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]).trace = 1 := (diagState_isState ha hb hab).2
  have hc : pureCoupling S ∈ couplings (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) := by
    refine ⟨⟨pureCoupling_psd S, ?_⟩, ?_, ?_⟩
    · rw [trace_pure, hs.eq, hss, htr]
    · rw [ptrace2_pure, hs.eq, hss]
    · rw [ptrace1_pure, hs.eq, hss]
  apply le_antisymm
  · calc
      D2 pauli (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) ≤ cost pauli (pureCoupling S) :=
        D2_le_cost pauli_hermitian hc
      _ = _ := by
        rw [pauli_cost, hc.1.2, overlap_pure]
        simp [S, D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState, Matrix.trace, Fin.sum_univ_succ, Complex.normSq_apply]
        ring
  · apply le_csInf ((couplings_nonempty (diagState_isState ha hb hab) (diagState_isState ha hb hab)).image _)
    rintro _ ⟨P,hp,rfl⟩
    rw [pauli_cost, hp.1.2]
    have hh := diag_overlap_le ha hb hp
    simp only [Complex.one_re]
    linarith

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section


theorem ptrace2_left (U : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * P * ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))).conjTranspose) = U * D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight P * U.conjTranspose := by
  ext i j
  simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
  ring

private theorem ptrace1_right (V : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * P * (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)).conjTranspose) = V * D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft P * V.conjTranspose := by
  ext i j
  simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
  ring

private theorem ptrace2_right (V : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hv : V.conjTranspose * V = 1) :
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * P * (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)).conjTranspose) = D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight P := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hv
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hv
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hv
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hv
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (0,0) (0,0) * h00 + P (0,0) (0,1) * h10 +
      P (0,1) (0,0) * h01 + P (0,1) (0,1) * h11
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (0,0) (1,0) * h00 + P (0,0) (1,1) * h10 +
      P (0,1) (1,0) * h01 + P (0,1) (1,1) * h11
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (1,0) (0,0) * h00 + P (1,0) (0,1) * h10 +
      P (1,1) (0,0) * h01 + P (1,1) (0,1) * h11
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (1,0) (1,0) * h00 + P (1,0) (1,1) * h10 +
      P (1,1) (1,0) * h01 + P (1,1) (1,1) * h11

private theorem ptrace1_left (U : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hu : U.conjTranspose * U = 1) :
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * P * ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))).conjTranspose) = D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft P := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hu
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hu
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hu
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hu
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (0,0) (0,0) * h00 + P (0,0) (1,0) * h10 +
      P (1,0) (0,0) * h01 + P (1,0) (1,0) * h11
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (0,0) (0,1) * h00 + P (0,0) (1,1) * h10 +
      P (1,0) (0,1) * h01 + P (1,0) (1,1) * h11
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (0,1) (0,0) * h00 + P (0,1) (1,0) * h10 +
      P (1,1) (0,0) * h01 + P (1,1) (1,0) * h11
  · simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Function.uncurry, Matrix.one_apply]
    linear_combination P (0,1) (0,1) * h00 + P (0,1) (1,1) * h10 +
      P (1,1) (0,1) * h01 + P (1,1) (1,1) * h11

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section

private def conjLift (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := U ⊗ₖ U.conjTranspose.transpose

private theorem conjLift_factor (U : Matrix (Fin 2) (Fin 2) ℂ) : conjLift U = (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose) := by
  rw [conjLift, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

private theorem conjTranspose_transpose_unitary {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1) :
    (U.conjTranspose.transpose).conjTranspose * U.conjTranspose.transpose = 1 := by
  have he : (U.conjTranspose.transpose).conjTranspose = U.transpose := by
    ext i j
    simp
  rw [he, ← Matrix.transpose_mul, hu, Matrix.transpose_one]

private theorem conjLift_unitary {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1)
    (hv : U * U.conjTranspose = 1) : (conjLift U).conjTranspose * conjLift U = 1 := by
  rw [conjLift, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hu,
    conjTranspose_transpose_unitary hu, Matrix.one_kronecker_one]

private theorem conjLift_bell {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U * U.conjTranspose = 1) :
    conjLift U *ᵥ (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have he : conjLift U *ᵥ (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) = Function.uncurry (U * U.conjTranspose) := by
    ext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [conjLift, Function.uncurry, Matrix.one_apply, Function.uncurry, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  rw [he, hu]

private theorem overlap_conjLift {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1)
    (hv : U * U.conjTranspose = 1) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    overlap (conjLift U * P * (conjLift U).conjTranspose) = overlap P := by
  have he : (conjLift U).conjTranspose *ᵥ (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    have h := congrArg (fun v => (conjLift U).conjTranspose *ᵥ v) (conjLift_bell hv)
    rw [Matrix.mulVec_mulVec, conjLift_unitary hu hv, Matrix.one_mulVec] at h
    exact h.symm
  unfold overlap
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, he]
  congr 1
  rw [dotProduct_mulVec]
  have hs : star (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) ᵥ* conjLift U = star (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    have hh := congrArg star he
    simpa only [Matrix.star_mulVec, star_star, Matrix.conjTranspose_conjTranspose] using hh
  rw [hs]

private theorem ptrace2_conjLift {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (conjLift U * P * (conjLift U).conjTranspose) = U * D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight P * U.conjTranspose := by
  rw [conjLift_factor, Matrix.conjTranspose_mul]
  have he : (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose) * P *
      ((((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose)).conjTranspose * ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))).conjTranspose) =
      (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose) * P *
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose)).conjTranspose) * ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))).conjTranspose := by
    simp only [Matrix.mul_assoc]
  rw [he, ptrace2_left, ptrace2_right _ _ (conjTranspose_transpose_unitary hu)]

private theorem ptrace1_conjLift {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft (conjLift U * P * (conjLift U).conjTranspose) =
      U.conjTranspose.transpose * D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft P * (U.conjTranspose.transpose).conjTranspose := by
  have he : conjLift U = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose) * (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [conjLift, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [he, Matrix.conjTranspose_mul]
  have he2 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose) * (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * P *
      (((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))).conjTranspose * (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose)).conjTranspose) =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose) * ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * P * ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))).conjTranspose) *
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U.conjTranspose.transpose)).conjTranspose := by simp only [Matrix.mul_assoc]
  rw [he2, ptrace1_right, ptrace1_left _ _ hu]

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
noncomputable section


theorem rotate_isState {U rho : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1) (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) :
    D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U rho) := by
  refine ⟨hr.1.mul_mul_conjTranspose_same U, ?_⟩
  rw [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, hu, Matrix.one_mul, hr.2]

private theorem rotate_inverse {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U.conjTranspose (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U rho) = rho := by
  simp only [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc
    U.conjTranspose * (U * rho * U.conjTranspose) * U =
        (U.conjTranspose * U) * rho * (U.conjTranspose * U) := by simp only [Matrix.mul_assoc]
    _ = rho := by rw [hu, Matrix.one_mul, Matrix.mul_one]

private theorem rotate_coupling {U rho omega : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1)
    (hv : U * U.conjTranspose = 1) {P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hp : P ∈ couplings rho omega) :
    conjLift U * P * (conjLift U).conjTranspose ∈ couplings (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U rho) (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U omega) := by
  refine ⟨⟨hp.1.1.mul_mul_conjTranspose_same _, ?_⟩, ?_, ?_⟩
  · rw [Matrix.trace_mul_cycle, conjLift_unitary hu hv, Matrix.one_mul, hp.1.2]
  · rw [ptrace2_conjLift hu, hp.2.1]
    rfl
  · rw [ptrace1_conjLift hu, hp.2.2]
    simp only [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution, Matrix.star_eq_conjTranspose, Matrix.transpose_mul, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private theorem pauli_cost_rotate {U : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1)
    (hv : U * U.conjTranspose = 1) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    cost pauli (conjLift U * P * (conjLift U).conjTranspose) = cost pauli P := by
  rw [pauli_cost, pauli_cost, overlap_conjLift hu hv, Matrix.trace_mul_cycle,
    conjLift_unitary hu hv, Matrix.one_mul]

private theorem D2_rotate_le {U rho omega : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1)
    (hv : U * U.conjTranspose = 1) (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) (ho : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity omega) :
    D2 pauli (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U rho) (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U omega) ≤ D2 pauli rho omega := by
  apply le_csInf ((couplings_nonempty hr ho).image _)
  rintro _ ⟨P,hp,rfl⟩
  calc
    _ ≤ cost pauli (conjLift U * P * (conjLift U).conjTranspose) :=
      D2_le_cost pauli_hermitian (rotate_coupling hu hv hp)
    _ = cost pauli P := pauli_cost_rotate hu hv P

theorem D2_rotate {U rho omega : Matrix (Fin 2) (Fin 2) ℂ} (hu : U.conjTranspose * U = 1)
    (hv : U * U.conjTranspose = 1) (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) (ho : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity omega) :
    D2 pauli (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U rho) (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U omega) = D2 pauli rho omega := by
  apply le_antisymm (D2_rotate_le hu hv hr ho)
  have hh := D2_rotate_le (U := U.conjTranspose)
    (by simpa using hv) (by simpa using hu) (rotate_isState hu hr) (rotate_isState hu ho)
  simpa only [rotate_inverse hu] using hh

private theorem exists_diagonalization {rho : Matrix (Fin 2) (Fin 2) ℂ} (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) :
    ∃ (U : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ), U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      0 ≤ a ∧ 0 ≤ b ∧ a+b=1 ∧ rho = D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U (D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b]) := by
  let h := hr.1.1
  let U : Matrix (Fin 2) (Fin 2) ℂ := h.eigenvectorUnitary
  let a := h.eigenvalues 0
  let b := h.eigenvalues 1
  have hu : U.conjTranspose * U = 1 := Unitary.coe_star_mul_self h.eigenvectorUnitary
  have hv : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self h.eigenvectorUnitary
  refine ⟨U,a,b,hu,hv,hr.1.eigenvalues_nonneg 0,hr.1.eigenvalues_nonneg 1,?_,?_⟩
  · have ht := congrArg Complex.re h.trace_eq_sum_eigenvalues
    rw [hr.2] at ht
    simpa [a,b,Fin.sum_univ_two] using ht.symm
  · convert h.spectral_theorem using 1
    simp only [Unitary.conjStarAlgAut_apply, D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState,a,b]

theorem self_cost_spectral {rho : Matrix (Fin 2) (Fin 2) ℂ} (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) :
    ∃ (a b : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ a+b=1 ∧
      D2 pauli rho rho = 8 - 4*(Real.sqrt a + Real.sqrt b)^2 ∧
      (CFC.sqrt rho).trace.re = Real.sqrt a + Real.sqrt b := by
  obtain ⟨U,a,b,hu,hv,ha,hb,hab,he⟩ := exists_diagonalization hr
  let S := D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![Real.sqrt a, Real.sqrt b]
  have hsp : S.PosSemidef := Matrix.PosSemidef.diagonal (by
    intro i; fin_cases i <;> exact ⟨Real.sqrt_nonneg _,rfl⟩)
  have hss : S * S = D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S,D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState,Matrix.mul_apply,Fin.sum_univ_two,← Complex.ofReal_mul,
        Real.mul_self_sqrt ha,Real.mul_self_sqrt hb]
  have hroot : CFC.sqrt rho = D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution U S := by
    apply CFC.sqrt_unique
    · rw [he]
      simp only [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution, Matrix.star_eq_conjTranspose]
      calc
        U * S * U.conjTranspose * (U * S * U.conjTranspose) =
            U * (S * (U.conjTranspose * U) * S) * U.conjTranspose := by simp only [Matrix.mul_assoc]
        _ = U * D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState ![a,b] * U.conjTranspose := by rw [hu,Matrix.mul_one,hss]
    · exact (hsp.mul_mul_conjTranspose_same U).nonneg
  refine ⟨a,b,ha,hb,hab,?_,?_⟩
  · rw [he,D2_rotate hu hv (diagState_isState ha hb hab) (diagState_isState ha hb hab)]
    exact diag_self_cost ha hb hab
  · rw [hroot,D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution, Matrix.star_eq_conjTranspose,Matrix.trace_mul_cycle,hu,Matrix.one_mul]
    simp [S,D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState,Matrix.trace,Fin.sum_univ_two]

theorem self_cost {rho : Matrix (Fin 2) (Fin 2) ℂ} (hr : D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity rho) :
    D2 pauli rho rho = 8 - 4*(CFC.sqrt rho).trace.re^2 := by
  obtain ⟨a,b,_,_,_,hc,ht⟩ := self_cost_spectral hr
  rw [hc,ht]

end
end D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
