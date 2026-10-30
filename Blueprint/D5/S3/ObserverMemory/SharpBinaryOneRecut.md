# Sharp Binary One Recut

## Abstract

The sharp local cost of one binary recut depends on the actual forward residual width.

**Theorem 1.1 (Length of the optional-index encoding).**

$$\forall N \in \mathit{Nat},\; \forall i \in \operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right),\; \operatorname{length}\left(\operatorname{word}\left(i\right)\right) = N$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/SharpBinaryOneRecut.word_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and every optional index i in Option(Fin N), word(i) has length N. The word lists the Boolean tests i=some t in the order t in Fin N; this includes N=0 and the none input. Equal lengths allow cancellation of consecutive encoding blocks.

**Theorem 1.2 (Recovery of the optional index).**

$$\forall N \in \mathit{Nat},\; \forall i \in \operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right),\; \forall j \in \operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right),\; \operatorname{word}\left(i\right) = \operatorname{word}\left(j\right) \Rightarrow i = j$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/SharpBinaryOneRecut.word_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N the complete encoding function on Option(Fin N) is injective. Every some s is detected at coordinate s; none is the all-false word. Consequently an injective two-letter alphabet transport preserves optional-index recovery, and concatenated fixed-length blocks recover a finite derivative table coordinate by coordinate.

**Theorem 1.3 (Cardinality of a free derivative coordinate).**

$$\forall N \in \mathit{Nat},\; \forall full \in \mathit{Bool},\; \left(\mathit{full} = \mathit{false} \Rightarrow \operatorname{card}\left(\operatorname{Spare}\left(N, \mathit{full}\right)\right) = N + 1\right) \land \left(\mathit{full} = \mathit{true} \Rightarrow \operatorname{card}\left(\operatorname{Spare}\left(N, \mathit{full}\right)\right) = N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/SharpBinaryOneRecut.spare_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and Boolean full, Spare(N,full) consists of i in Option(Fin N) such that full=true implies i is not none. Its cardinality is N plus zero when full=true and N plus one when full=false. This includes N=0 in both regimes and gives the number of choices for each free derivative coordinate.

**Theorem 1.4 (Sharp bounds and simultaneous attainment).**

$$\left(\forall n \in \mathit{Nat},\; \forall C \in \operatorname{Set}\left(\operatorname{List}\left(\mathit{Bool}\right)\right),\; \forall k \in \mathit{Nat},\; \left(\left(\left(\left(\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Member}\left(w, C\right) \Rightarrow \operatorname{length}\left(w\right) = n\right) \land \operatorname{Nonempty}\left(C\right)\right) \land 1 \le k\right) \land k \le n\right) \Rightarrow \left(\left(\left(\left(\operatorname{Finite}\left(\operatorname{residualSet}\left(C, k\right)\right) \land 0 < \operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right)\right) \land \left(\forall z \in \operatorname{Set}\left(\operatorname{List}\left(\mathit{Bool}\right)\right) \times \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Member}\left(z, \operatorname{image}\left(C, k, 1\right)\right) \Rightarrow \operatorname{Member}\left(\operatorname{recut}\left(z\right), \operatorname{residualSet}\left(C, k\right)\right)\right)\right) \land \left(\left(\forall E \in \operatorname{Set}\left(\operatorname{List}\left(\mathit{Bool}\right)\right),\; \operatorname{Member}\left(E, \operatorname{residualSet}\left(C, k\right)\right) \Rightarrow \left(\operatorname{card}\left(\operatorname{currentFiber}\left(C, k, E\right)\right) \le 2 \cdot \left(\operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right) + 1\right) \land \left(\forall b \in \mathit{Bool},\; \operatorname{card}\left(\operatorname{fixedBitFiber}\left(C, k, E, b\right)\right) \le \operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right) + 1\right)\right)\right) \land \operatorname{card}\left(\operatorname{image}\left(C, k, 1\right)\right) \le 2 \cdot \operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right) \cdot \left(\operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right) + 1\right)\right)\right) \land \left(\operatorname{FullBranching}\left(C, k\right) \Rightarrow \left(\left(\forall E \in \operatorname{Set}\left(\operatorname{List}\left(\mathit{Bool}\right)\right),\; \operatorname{Member}\left(E, \operatorname{residualSet}\left(C, k\right)\right) \Rightarrow \left(\operatorname{card}\left(\operatorname{currentFiber}\left(C, k, E\right)\right) \le 2 \cdot \operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right) \land \left(\forall b \in \mathit{Bool},\; \operatorname{card}\left(\operatorname{fixedBitFiber}\left(C, k, E, b\right)\right) \le \operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right)\right)\right)\right) \land \operatorname{card}\left(\operatorname{image}\left(C, k, 1\right)\right) \le 2 \cdot \operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right) \cdot \operatorname{card}\left(\operatorname{residualSet}\left(C, k\right)\right)\right)\right)\right)\right) \land \left(\forall N \in \mathit{Nat},\; 1 \le N \Rightarrow \left(\left(\left(\left(\left(\left(\left(\left(\operatorname{Nonempty}\left(\operatorname{relation}\left(N, \mathit{false}\right)\right) \land \left(\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Member}\left(w, \operatorname{relation}\left(N, \mathit{false}\right)\right) \Rightarrow \operatorname{length}\left(w\right) = 3 \cdot N + 1\right)\right) \land 1 \le 2 \cdot N + 1\right) \land 2 \cdot N + 1 \le 3 \cdot N + 1\right) \land \left(\mathit{false} = \mathit{true} \Rightarrow \operatorname{FullBranching}\left(\operatorname{relation}\left(N, \mathit{false}\right), 2 \cdot N + 1\right)\right)\right) \land \operatorname{card}\left(\operatorname{residualSet}\left(\operatorname{relation}\left(N, \mathit{false}\right), 2 \cdot N + 1\right)\right) = N\right) \land \operatorname{card}\left(\operatorname{image}\left(\operatorname{relation}\left(N, \mathit{false}\right), 2 \cdot N + 1, 1\right)\right) = 2 \cdot N \cdot \left(N + 1\right)\right) \land \left(\forall E \in \operatorname{Set}\left(\operatorname{List}\left(\mathit{Bool}\right)\right),\; \operatorname{Member}\left(E, \operatorname{residualSet}\left(\operatorname{relation}\left(N, \mathit{false}\right), 2 \cdot N + 1\right)\right) \Rightarrow \left(\operatorname{card}\left(\operatorname{currentFiber}\left(\operatorname{relation}\left(N, \mathit{false}\right), 2 \cdot N + 1, E\right)\right) = 2 \cdot \left(N + 1\right) \land \left(\forall b \in \mathit{Bool},\; \operatorname{card}\left(\operatorname{fixedBitFiber}\left(\operatorname{relation}\left(N, \mathit{false}\right), 2 \cdot N + 1, E, b\right)\right) = N + 1\right)\right)\right)\right) \land \left(\left(\left(\left(\left(\left(\left(\operatorname{Nonempty}\left(\operatorname{relation}\left(N, \mathit{true}\right)\right) \land \left(\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Member}\left(w, \operatorname{relation}\left(N, \mathit{true}\right)\right) \Rightarrow \operatorname{length}\left(w\right) = 3 \cdot N + 1\right)\right) \land 1 \le 2 \cdot N + 1\right) \land 2 \cdot N + 1 \le 3 \cdot N + 1\right) \land \left(\mathit{true} = \mathit{true} \Rightarrow \operatorname{FullBranching}\left(\operatorname{relation}\left(N, \mathit{true}\right), 2 \cdot N + 1\right)\right)\right) \land \operatorname{card}\left(\operatorname{residualSet}\left(\operatorname{relation}\left(N, \mathit{true}\right), 2 \cdot N + 1\right)\right) = N\right) \land \operatorname{card}\left(\operatorname{image}\left(\operatorname{relation}\left(N, \mathit{true}\right), 2 \cdot N + 1, 1\right)\right) = 2 \cdot N \cdot N\right) \land \left(\forall E \in \operatorname{Set}\left(\operatorname{List}\left(\mathit{Bool}\right)\right),\; \operatorname{Member}\left(E, \operatorname{residualSet}\left(\operatorname{relation}\left(N, \mathit{true}\right), 2 \cdot N + 1\right)\right) \Rightarrow \left(\operatorname{card}\left(\operatorname{currentFiber}\left(\operatorname{relation}\left(N, \mathit{true}\right), 2 \cdot N + 1, E\right)\right) = 2 \cdot N \land \left(\forall b \in \mathit{Bool},\; \operatorname{card}\left(\operatorname{fixedBitFiber}\left(\operatorname{relation}\left(N, \mathit{true}\right), 2 \cdot N + 1, E, b\right)\right) = N\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/SharpBinaryOneRecut.sharp_binary_one_recut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be one nonempty set of binary words, all of length n, and fix 1 <= k <= n. Write R_k=residualSet(C,k) for the residual languages of actual extendable prefixes of length k. Write Q=image(C,(k,1)) for the actual anchored boundary image with a tail of length one. These are the original carriers of the strict supplied append and bounded deletion model. No independent choice of a residual and a tail is assumed. The residual carrier is finite and has positive cardinal N, as consequences of the binary fixed-length and nonempty hypotheses.

For z=(S,t) in Q, recut(z)={f: tf belongs to S}. This belongs to R_k, so recut restricts to a lawful map Q to R_k. currentFiber(C,k,E) is exactly {z in Q: recut(z)=E}; fixedBitFiber(C,k,E,b) further requires t=[b]. Thus these subsets count the fibers of that actual-image map, with or without the last bit. FullBranching(C,k) means that for every extendable prefix v of length k-1 and each binary b, vb has a completion in this same C.

The displayed bounds abbreviate no extra assumptions: each current fiber has at most 2(N+1) elements, each fixed-bit fiber at most N+1, and Q at most 2N(N+1). With FullBranching the corresponding numbers are 2N, N, and 2N squared. Earlier residuals contain no empty word, since their prefixes have length k-1<n. An earlier residual is therefore exactly the disjoint union of its two first-bit derivatives. Each derivative is empty or an actual member of R_k. Fixing E and b leaves at most N+1 opposite derivatives. The full branching condition excludes the empty option. This gives injective encodings of each fixed-bit fiber, each current fiber and the complete Q into the corresponding finite carriers.

For every positive N, use J=Option(Fin N). Encode none by the all-false word e(none) of length N and some i by the length-N word true only at coordinate i. This encoding is injective, including the distinction between none and every some i. Set v(i,j)=e(i)e(j). In the unrestricted family use all pairs except (none,none); in the full family require both components to be some. The literal words are v(i,j)b e(some s) exactly when the b-selected component is some s, with false selecting i and true selecting j. relation(N,false) and relation(N,true) denote these two actual word sets.

More explicitly, Spare(N,false) is the full optional index set and Spare(N,true) consists of its nonempty options. Point(N,full)=Fin N times Bool times Spare(N,full). A point (s,b,t) sets the selected component to some s and the opposite component to t; code is its literal word. Conversely every literal legal word has such a point. All codewords have length 3N+1 and the cut is 2N+1. A positive N supplies a point and hence a nonempty source. No separate finiteness or positivity premise is imposed.

At length 2N the actual extendable prefixes are exactly v(i,j) with the stated admissibility condition. Their residuals are precisely the languages S(i,j) consisting of false e(some s) when i=some s and true e(some s) when j=some s. Taking the two derivatives recovers i and j, so these predecessor residuals are injective in the pair. At length 2N+1 every actual prefix is exactly the prefix of a Point, and its residual is the singleton containing e(some s). Both directions follow by splitting a literal source word at its fixed lengths; equal-length prefix cancellation and injectivity of e exclude further prefixes or identifications.

The original fine image Q is exactly the range of fine(s,b,t)=(S(i,j),[b]); each point has the actual state (v(i,j),[b]) and completion e(some s). Exhaustion follows by splitting any actual typed state inside a literal source word. fine is injective. Current residuals are exactly the N distinct singletons {e(some s)}. For each such singleton, its entire current fiber is parametrized bijectively by Bool times Spare, and its fixed-bit fiber by Spare. The unrestricted cardinalities are consequently 2N(N+1), 2(N+1), N+1; the full cardinalities are 2N squared, 2N, N. All fibers attain their bounds simultaneously in one C in each regime, including N=1. In the full family the exhaustive predecessor classification proves both append bits legal at every actual earlier prefix.

The universal quantifiers include k=1 and k=n. In the sharpness clauses, lengths vary with N; attainment for every separately prescribed pair of lengths is not asserted. The behavioral interpretation and supplied-deletion separators are provided by strict_anchored_specialization, with parameter d=1, the same C, and the same cut k. The sharp counting argument is the one in Theorem 4.1 of Recursive relational observation: nonlinear recuts, predecessor context and retained memory; the optional one-hot realization makes its arbitrary positive width explicit. This is an attribution of the argument and its scope, with no literature priority claim over reversible automata or trellis theory.

## References

- Truth anchor: `D5/S3/ObserverMemory/SharpBinaryOneRecut.sharp_binary_one_recut`
- Truth anchor: `D5/S3/ObserverMemory/SharpBinaryOneRecut.spare_card`
- Truth anchor: `D5/S3/ObserverMemory/SharpBinaryOneRecut.word_injective`
- Truth anchor: `D5/S3/ObserverMemory/SharpBinaryOneRecut.word_length`
- Dependency: [D5/S3/ObserverMemory/StrictAnchoredBoundary](StrictAnchoredBoundary.md)
