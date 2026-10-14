# PositiveCircuitSupplier

## Abstract

The exact supplier exists_simpleSignedCircuit_decomposition is retained from Maths/Multitubes/Additive/CirculationDecomposition.lean at elazarg/multitubes commit 20d22aa7ca67f9843e5adf9edf173403a2f4033a. A normalized nonnegative real signed-incidence certificate has a finite convex decomposition into simple circuits, with exact coordinate reconstruction. This does not itself supply a greedy support-decreasing certificate; that certificate is proved in LayeredFlow. Copyright, the upstream license notice, full Apache-2.0 text and the retirement condition against this repository pinned mathlib are in the Lean sources.

Generic declarations use these source contexts: universe uV uE variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} universe uV uE variable {V : Type uV} {E : Type uE} universe uV uE variable {V : Type uV} {E : Type uE}

**Definition 1.1 (IsSimpleCycle).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.IsSimpleCycle`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.IsSimpleCycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def IsSimpleCycle {base : V} (cycle : G.Walk base base) : Prop := 0 < cycle.length ∧ ∀ (vertex : V) (before : G.Walk base vertex) (inner : G.Walk vertex vertex) (after : G.Walk vertex base), cycle.edges = before.edges ++ inner.edges ++ after.edges → 0 < inner.length → 0 < before.length + after.length → False

**Definition 1.2 (CycleMeanDominates).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.CycleMeanDominates`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.CycleMeanDominates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def CycleMeanDominates (weight : E → ℝ) {firstBase secondBase : V} (first : G.Walk firstBase firstBase) (second : G.Walk secondBase secondBase) : Prop := second.length * MaxPlusPotential.walkWeight weight first ≥ first.length * MaxPlusPotential.walkWeight weight second

**Definition 1.3 (signedGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.signedGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.signedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def signedGraph (G : EdgeGraph V E) : EdgeGraph V (SignedEdge E) where source | (edge, false) => G.source edge | (edge, true) => G.target edge target | (edge, false) => G.target edge | (edge, true) => G.source edge

**Definition 1.4 (circuitCoefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.circuitCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.circuitCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def circuitCoefficient [DecidableEq E] {G : EdgeGraph V E} {base : V} (cycle : G.Walk base base) (edge : E) : ℝ := cycle.edgeMultiplicity edge / cycle.length

**Theorem 1.5 (sum edgeMultiplicity eq length).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_eq_length`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_eq_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem sum_edgeMultiplicity_eq_length [Fintype E] [DecidableEq E] {G : EdgeGraph V E} {start finish : V} (walk : G.Walk start finish) : ∑ edge, walk.edgeMultiplicity edge = walk.length

**Definition 1.6 (edgeListCoefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.edgeListCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.edgeListCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def edgeListCoefficient [DecidableEq E] (edges : List E) (edge : E) : ℝ := edges.count edge / edges.length

**Definition 1.7 (simpleSignedCircuitCoefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.simpleSignedCircuitCoefficients`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.simpleSignedCircuitCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def simpleSignedCircuitCoefficients [DecidableEq E] (G : EdgeGraph V E) : Set (SignedEdge E → ℝ) := {coefficient | ∃ (base : V) (cycle : (signedGraph G).Walk base base), IsSimpleCycle cycle ∧ circuitCoefficient cycle = coefficient}

**Theorem 1.8 (length le card).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.length_le_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.length_le_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem IsSimpleCycle.length_le_card [Fintype V] {G : EdgeGraph V E} {base : V} {cycle : G.Walk base base} (hsimple : IsSimpleCycle cycle) : cycle.length ≤ Fintype.card V

**Theorem 1.9 (sum edgeMultiplicity mul eq walkWeight general).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_mul_eq_walkWeight_general`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_mul_eq_walkWeight_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem sum_edgeMultiplicity_mul_eq_walkWeight_general [Fintype E] [DecidableEq E] {G : EdgeGraph V E} (weight : E → ℝ) {start finish : V} (walk : G.Walk start finish) : ∑ edge, (walk.edgeMultiplicity edge : ℝ) * weight edge = MaxPlusPotential.walkWeight weight walk

**Theorem 1.10 (exists simpleSignedCircuit decomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.exists_simpleSignedCircuit_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.exists_simpleSignedCircuit_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem exists_simpleSignedCircuit_decomposition [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ) (hcoefficient : FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient) : ∃ (ι : Type) (_ : Fintype ι) (convexWeight : ι → ℝ) (base : ι → V) (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)), (∀ i, 0 ≤ convexWeight i) ∧ (∑ i, convexWeight i) = 1 ∧ (∀ i, IsSimpleCycle (cycle i)) ∧ ∀ edge, coefficient edge = ∑ i, convexWeight i * circuitCoefficient (cycle i) edge

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.CycleMeanDominates`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.IsSimpleCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.circuitCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.edgeListCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.exists_simpleSignedCircuit_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.length_le_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.signedGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.simpleSignedCircuitCoefficients`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_eq_length`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_mul_eq_walkWeight_general`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual](SupplierDual.md)
