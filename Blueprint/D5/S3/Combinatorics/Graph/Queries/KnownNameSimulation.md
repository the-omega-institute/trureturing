# Synthetic misses on undisclosed names

## Abstract

Simulation of a deterministic name-query strategy using only known-name oracle calls.

**Theorem 1.1 (The simulated strategy preserves the query budget).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.simulated_sent_names_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.simulated_sent_names_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a deterministic strategy whose depth is at most a given budget on every answer branch. Start the simulation with a specified set of known names. Each successful reply adds the queried name and all returned neighbor names. A miss leaves the known set as it was. The simulation asks the oracle only when the queried name is in the current known set and returns a synthetic miss internally on any other name. Its number of oracle calls is at most the original budget because each simulated step follows one answer branch and makes at most one call.

**Theorem 1.2 (Only a successful unknown-name query can change the result).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.success_mass_le_simulated_add_guessed_hit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.success_mass_le_simulated_add_guessed_hit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sample an oracle world from an arbitrary probability mass function and run the original deterministic strategy and the simulation on that same world with the same initial known set. A successful reply adds its queried name and neighbor names to the current set. For any success predicate of the world and completed record, the original success probability is at most the simulated success probability plus the probability that the original strategy hits a name outside its current known set. The two records agree up to that hit. A real miss on an unknown name and a synthetic miss select the same continuation.

**Theorem 1.3 (The actual transcript prefix determines the next query).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.nextQuery_of_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.nextQuery_of_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Run the same strategy with and without truncation after a fixed number of steps against the same oracle. Applying the next-query readout to the truncated record returns the queried label at that index in the full record. If the full run has already stopped, the readout returns none.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.nextQuery_of_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.simulated_sent_names_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.success_mass_le_simulated_add_guessed_hit`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../../../ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.md)
