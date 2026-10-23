# Five Actual Surviving J2 Path Components

## Abstract

Each independently specified native J2 word constructs an actual simple path exhausting its full component after the six actual marked F2 edges are removed.

**Theorem 1.1 (Every Literal Word Exhausts Its Actual Component).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall i \in \mathrm{Fin}\left(5\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{wordStart}\left(m, i\right), \mathrm{wordFinish}\left(m, i\right)\right),\; \mathrm{IsPath}\left(w\right) \land \left(\mathrm{Length}\left(w\right) = \mathrm{wordLength}\left(m, i\right) \land \left(\mathrm{Support}\left(w\right) = \mathrm{ScanlMul}\left(\mathrm{wordStart}\left(m, i\right), \mathrm{word}\left(m, i\right)\right) \land \left(\left(\forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(w\right)\right) \Leftrightarrow \mathrm{Reachable}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{wordStart}\left(m, i\right), x\right)\right) \land \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \forall y \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Adj}\left(\mathrm{survivingGraph}\left(m\right), x, y\right) \land \mathrm{Reachable}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{wordStart}\left(m, i\right), x\right)\right) \Leftrightarrow \mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, y\right), \mathrm{Edges}\left(w\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges.native_j2_word_full_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and i in Fin(5), there is an actual walk in survivingGraph(m) from the independently specified wordStart(m,i) to wordFinish(m,i). It is simple, has exactly wordLength(m,i) edges, and its complete support is the literal left multiplication scan of word(m,i). A configuration lies in its support exactly when it is reachable from its start in the actual surviving graph. Moreover, an arbitrary actual surviving edge incident to that component occurs in this same walk, and every edge of this walk is such an edge.

The surviving graph is specified before choosing the words or a walk: take the complete actual F2 native edges outside all T/E cuts together with every actual T/E c seam, then remove exactly the six independently specified marked b edges. Literal c-step coordinates identify the exact T or E seam owner. Full lower and contact native-circle complements earn each repeated H row. The short reflected and positive rows separately avoid the actual selected cuts and terminal-marked b edges, including both F2 b cuts in the contact circle. Exact seed products and repeated-block products then concatenate these earned rows into all five complete words.

The same actual F2 Hamilton witness bounds the surviving degree by two and makes each independently specified port a graph leaf after its marked edge is removed. Consecutive literal generators never multiply to the identity. Cancellation turns this letter law into nonbacktracking of the actual constructed walk. The earned leaf/nonbacktracking component theorem then proves simplicity, complete vertex reachability and the complete incident-edge inventory. No path, component coverage, endpoint matching, or step-legality hypothesis is supplied by the caller.

This result constructs the five stated components. Identifying the sixth component and establishing the higher actual recursive expansion and Hamilton cycles for all sizes are further mathematical obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges.native_j2_word_full_component`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingRows](NativeJ2SurvivingRows.md)
