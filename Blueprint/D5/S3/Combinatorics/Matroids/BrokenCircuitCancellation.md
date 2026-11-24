# Broken-circuit cancellation for finite matroids

## Abstract

Finite matroid broken-circuit cancellation by the least completer involution.

**Definition 1.1 (The finite ground subset).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.matroidGround`

*Formalization.* `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.matroidGround` (`✓ std3`).

*Citation.* ukiyois; OpenCode agent sessions (2026). *Finite-matroid broken-circuit cancellation*. URL: <https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean>.

*Commentary.*

For a finite ambient type alpha and a matroid M on alpha, matroidGround M is the finite subset of M.E obtained by filtering the ambient finite universe. Elements outside M.E are excluded.

**Definition 1.2 (A circuit-completing element).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.IsNBCandidate`

*Formalization.* `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.IsNBCandidate` (`✓ std3`).

*Citation.* ukiyois; OpenCode agent sessions (2026). *Finite-matroid broken-circuit cancellation*. URL: <https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean>.

*Commentary.*

For an arbitrary finite subset A of the ambient type and an element e, IsNBCandidate M A e means that there is a finite circuit C of M containing e, every f in C satisfies f <= e, and the finite set C.erase e is contained in A. Thus the broken circuit is defined by deleting a circuit maximum. The circuit lies in M.E; A may also contain ambient elements outside M.E.

**Definition 1.3 (All circuit-completing elements).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.nbcCandidates`

*Formalization.* `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.nbcCandidates` (`✓ std3`).

*Citation.* ukiyois; OpenCode agent sessions (2026). *Finite-matroid broken-circuit cancellation*. URL: <https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean>.

*Commentary.*

nbcCandidates M A is the finite filter of matroidGround M consisting of all elements e for which a circuit witness as in IsNBCandidate M A e exists.

**Definition 1.4 (A broken-circuit witness).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.IsNBCBad`

*Formalization.* `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.IsNBCBad` (`✓ std3`).

*Citation.* ukiyois; OpenCode agent sessions (2026). *Finite-matroid broken-circuit cancellation*. URL: <https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean>.

*Commentary.*

IsNBCBad M A means that nbcCandidates M A is nonempty. It records exactly the existence of a circuit C and a circuit maximum e whose deletion C.erase e lies in A; no loopless, rank, connectivity, representability, or nonempty-ground assumption is made.

**Definition 1.5 (Ground-contained spanning subsets).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.spanningSubsets`

*Formalization.* `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.spanningSubsets` (`✓ std3`).

*Citation.* ukiyois; OpenCode agent sessions (2026). *Finite-matroid broken-circuit cancellation*. URL: <https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean>.

*Commentary.*

spanningSubsets M is the finite powerset of matroidGround M filtered by M.Spanning of the corresponding Set. It therefore ranges over every ground-contained spanning subset, including the empty and rank-zero cases when they occur.

**Definition 1.6 (Actual no-broken-circuit bases).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.actualNBCBaseSubsets`

*Formalization.* `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.actualNBCBaseSubsets` (`✓ std3`).

*Citation.* ukiyois; OpenCode agent sessions (2026). *Finite-matroid broken-circuit cancellation*. URL: <https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean>.

*Commentary.*

actualNBCBaseSubsets M is the finite filter of matroidGround M powerset elements A satisfying both M.IsBase (A : Set alpha) and not IsNBCBad M A. It is the exact actual-base survivor family, with M.E containment explicit and every broken circuit formed by deleting a circuit maximum. The definition applies to matroids with loops, disconnected matroids, empty grounds, and arbitrary ambient elements outside M.E.

**Definition 1.7 (The integer-power survivor sum).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.actualNBCBasePowerSum`

*Formalization.* `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.actualNBCBasePowerSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

actualNBCBasePowerSum M sums (-1 : Int) ^ A.card over the exact actualNBCBaseSubsets M filter. The exponent is the finite-set cardinality and the coefficient ring is the integers.

**Theorem 1.8 (Broken-circuit cancellation identity).**

Lean statement: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.alternating_spanning_sum_eq_actual_nbc_base_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.alternating_spanning_sum_eq_actual_nbc_base_sum` (`✓ std3`). ∎

*Citation.* ukiyois; OpenCode agent sessions (2026). *Finite-matroid broken-circuit cancellation*. URL: <https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean>.

*Commentary.*

For every finite linearly ordered ambient type alpha and every Matroid alpha, the integer power sum (-1 : Int) ^ A.card over all A in spanningSubsets M equals actualNBCBasePowerSum M. On bad spanning subsets it toggles the least possible circuit maximum, whose witness remains stable under the toggle; this gives a span-preserving, parity-reversing, fixed-point-free involution. A surviving spanning set is independent and hence a base; conversely, every base is spanning, so the surviving sets are precisely the actual bases avoiding broken circuits.

The statement covers empty ambient carriers, empty grounds, rank zero, loops, nonloopless and disconnected matroids, and ambient elements outside M.E.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.IsNBCBad`
- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.IsNBCandidate`
- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.actualNBCBasePowerSum`
- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.actualNBCBaseSubsets`
- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.alternating_spanning_sum_eq_actual_nbc_base_sum`
- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.matroidGround`
- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.nbcCandidates`
- Truth anchor: `D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation.spanningSubsets`
