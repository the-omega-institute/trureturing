# Finite chordality and perfect elimination

## Abstract

The source theorem ranges over V : Type u for any universe u; the existing native predicate ranges over V : Type 0. NativeChordal denotes FaalNonStable.Chordal. Later(G,ord,v) denotes exactly the set of u in V satisfying ord(v) < ord(u) and G.Adj v u. IsPEO has exactly the injective and isClique_later fields. Both finite equivalences include empty and disconnected graphs and require neither a supplied Fintype nor decidable adjacency.

**Theorem 1.1 (An elimination order implies chordality).**

$$\forall V \in \mathrm{Type}\left(u\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{Finite}\left(V\right) \Rightarrow \left(\forall ord \in V \to \mathrm{Nat},\; \mathrm{IsPEO}\left(G, ord\right) \Rightarrow \mathrm{IsChordal}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Characterization.isChordal` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic, finite chordal elimination and set-form Menger: Lean sources*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

The Option-parent forest has clique bags. On a cycle of length at least four choose a vertex whose top bag has largest rank. Its two cycle neighbors belong to that bag and are distinct. Their adjacency is absent from the cycle edges, so it is a chord. Rotation retains the same cycle support and unordered edges.

**Theorem 1.2 (The complete source characterization).**

$$\forall V \in \mathrm{Type}\left(u\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{Finite}\left(V\right) \Rightarrow \left(\mathrm{IsChordal}\left(G\right) \Leftrightarrow \left(\exists ord \in V \to \mathrm{Nat},\; \mathrm{IsPEO}\left(G, ord\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Characterization.isChordal_iff_exists_isPEO` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic, finite chordal elimination and set-form Menger: Lean sources*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

Dirac elimination supplies the forward implication; the deepest-top bag argument supplies the converse. The natural-number ranking is not required to be a contiguous enumeration. This is the classical known characterization with the original source construction.

**Theorem 1.3 (Positional and off-cycle-edge chordality).**

$$\forall V \in \mathrm{Type}\left(0\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{NativeChordal}\left(G\right) \Leftrightarrow \mathrm{IsChordal}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Characterization.native_chordal_iff_isChordal` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic, finite chordal elimination and set-form Menger: Lean sources*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

Each conversion uses the given cycle. Positions are strictly below its length. A supported occurrence at the closing endpoint is normalized to zero. The unordered edge may have either orientation. Absence from the edge list rules out consecutive positions and the last-to-first pair, and these positional exclusions conversely imply absence from the same edge list. This correspondence needs no finiteness hypothesis.

**Theorem 1.4 (The exact native finite characterization).**

$$\forall V \in \mathrm{Type}\left(0\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{Finite}\left(V\right) \Rightarrow \left(\mathrm{NativeChordal}\left(G\right) \Leftrightarrow \left(\exists ord \in V \to \mathrm{Nat},\; \mathrm{Injective}\left(ord\right) \land \left(\forall v \in V,\; \mathrm{IsClique}\left(G, \mathrm{Later}\left(G, ord, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Characterization.chordal_iff_exists_order` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic, finite chordal elimination and set-form Menger: Lean sources*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

The native correspondence and the full source equivalence give precisely an injective natural-number ranking and clique later-neighborhoods. The two fields are unpacked directly. No connectivity, nonemptiness, Fintype, decidability or preselected simplicial vertex is added.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Characterization.chordal_iff_exists_order`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Characterization.isChordal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Characterization.isChordal_iff_exists_isPEO`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Characterization.native_chordal_iff_isChordal`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/EliminationForest](EliminationForest.md)
- Dependency: [D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable](../CliquePolynomial/FaalNonStable.md)
