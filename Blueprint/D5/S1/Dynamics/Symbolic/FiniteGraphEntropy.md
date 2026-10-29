# Finite Graph Languages as Symbolic Systems

## Abstract

Finite graph languages are compact, closed and invariant under the one-sided shift.

Let V be a finite vertex type with a discrete topology, and let edge be any directed relation on V. The one-sided graph language consists of the vertex sequences following edge at every consecutive pair. The compactness and shift-invariance results do not require right-totality. These are standard facts about finite graph presentations; no literature novelty is claimed.

**Definition 1.1 (The natural adjacency matrix).**

Lean statement: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.adjacency`

*Formalization.* `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

adjacency(edge) is the V by V matrix over the natural numbers whose entry at (i,j) is 1 when edge(i,j) holds and 0 otherwise. This module defines the matrix but does not yet prove a formula relating its powers to realized prefix counts.

**Definition 1.2 (Every vertex has an outgoing edge).**

Lean statement: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.RightTotal`

*Formalization.* `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.RightTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RightTotal(edge) means that for every v there exists w with edge(v,w). A private helper uses this condition to extend each nonempty finite edge path to an infinite path.

**Definition 1.3 (The graph language with vertex labels).**

Lean statement: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.edgeLanguage`

*Formalization.* `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.edgeLanguage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

edgeLanguage(edge) specializes FiniteObservationSofic.graphLanguage to the identity vertex labelling. Thus its elements are exactly the sequences w with edge(w(n),w(n+1)) for every natural n.

**Theorem 1.4 (The language is compact and closed).**

$$\operatorname{IsCompact}\left(\operatorname{edgeLanguage}\left(\mathit{edge}\right)\right) \land \operatorname{IsClosed}\left(\operatorname{edgeLanguage}\left(\mathit{edge}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.edgeLanguage_isCompact_isClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each consecutive-edge constraint is closed because the finite vertex space is discrete. Their intersection is closed in the compact product V^N, hence compact. The identity-labelled language is its continuous image, and compact subsets of this Hausdorff product are closed. The conclusion includes empty languages and graphs with dead vertices.

**Theorem 1.5 (Dropping the first vertex preserves the language).**

$$\operatorname{MapsTo}\left(\operatorname{shift}\left(1\right), \operatorname{edgeLanguage}\left(\mathit{edge}\right), \operatorname{edgeLanguage}\left(\mathit{edge}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.edgeLanguage_shift_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here shift(1) is SymbolicDynamics.FullShift.shift(1). If a path satisfies every consecutive-edge constraint, its tail does too. The theorem proves forward invariance under the one-step shift; it does not assert surjectivity of that shift or an entropy formula.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.RightTotal`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.adjacency`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.edgeLanguage`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.edgeLanguage_isCompact_isClosed`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.edgeLanguage_shift_invariant`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteObservationSofic](../Shadowing/FiniteObservationSofic.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy](PrefixGrowthEntropy.md)
