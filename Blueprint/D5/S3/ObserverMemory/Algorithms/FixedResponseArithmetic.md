# Fixed Response Arithmetic

## Abstract

Finite endpoint-tagged progressions describe exact fixed-response paths.

**Definition 1.1 (The instruction successor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.successor`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.successor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A read follows its installed address's reply, an update follows its one successor, and a halt has no successor. The response field is arbitrary; there is no requirement on uninstalled physical addresses.

**Definition 1.2 (A separate absorbing sink).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.step`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The partial successor is totalized on Option Q. None is absorbing. An iterate ending at some y cannot have visited None earlier. Thus totalization does not add paths leaving a halt or halt self-loops.

**Definition 1.3 (Natural update weights).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.weight`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is one at a real update and zero at a read, halt or sink. Its natural prefix Birkhoff sum counts precisely the updates before the endpoint, including the empty prefix.

**Definition 1.4 (Endpoint and progression coefficients).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.Record`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.Record` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A record has an Option Q endpoint, a natural offset and a natural increment. An increment of zero gives a singleton weight without moving the endpoint.

**Definition 1.5 (An executable collision scan).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.records`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.records` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given explicit Fintype and DecidableEq instances for Q, put N equal to the cardinality of Option Q. Emit singleton records for indices below N. Scan mu below N and positive p at most N, retaining exactly collisions with mu plus p at most N. For every residue r below p, emit the endpoint at mu plus r, its prefix weight, and the weight of the p-step cycle. The list may contain repeated records and nonminimal periods. All coefficients are natural computations from the supplied table and response field. A proof of finite collision existence supplies no runtime choice.

**Definition 1.6 (Endpoint-exact progression support).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.Supports`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.Supports` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Supports data y d means that a record in data ends at some y and that d equals its offset plus its increment times some natural m. A record with endpoint None can never support a control state.

**Theorem 1.7 (All natural weights and both endpoints).**

$$\forall Q, A, R: \operatorname{Type},\ [\operatorname{Fintype}(Q)], [\operatorname{DecidableEq}(Q)],\ \forall f: Q \to \operatorname{Instruction}(Q, A, R), v: A \to R,\ \forall x, y\in Q, d\in \mathbb{N},\ \operatorname{FixedPath}(f, v, x, y, d) \iff \operatorname{Supports}(\operatorname{records}(f, v, x), y, d)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.fixed_path_iff_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite control type Q with explicit enumeration and decidable equality, arbitrary address and reply types A and R, one program f, one response field v, controls x and y, and natural d, the native FixedPath relation holds exactly when the computed records support y at weight d.

Induction on the real path and on the totalized iterate gives an exact bridge with the natural Birkhoff sum. The sink excludes artificial edges after halt. FiniteOrbitPeriodBound supplies a bounded collision. IsPeriodicPt.iterate_mod_apply reduces every tail endpoint to a cycle residue. The existing sum_cycle_mod_eq_blocks_remainder, applied to real casts of the natural weights, gives complete-block weights; BirkhoffSum.add attaches the transient prefix. Thus for every m and r below p the count at mu plus m times p plus r equals the count at mu plus r plus m times the computed cycle weight.

No positive cycle-weight assumption is made. Pure-read cycles, initial halts, transient halt endpoints, nonminimal collisions and empty paths remain included. A zero-weight cycle cannot introduce an external endpoint. This is the deterministic finite-orbit progression method, with an exact bridge to the native instruction constructors; no literature novelty is asserted.

Executable definitions take the finite table, its Fintype and equality procedures, and the response function as inputs. No correspondence with a uniform encoding or full descriptor synthesis is asserted.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.Record`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.Supports`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.fixed_path_iff_support`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.records`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.step`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.successor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.weight`
- Dependency: [D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution](GuardedPhaseExecution.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/EventualCycleAverage](../Prediction/EventualCycleAverage.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound](../Prediction/FiniteOrbitPeriodBound.md)
