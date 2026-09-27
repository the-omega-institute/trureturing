# Shared Control-Bit Storage Bound

## Abstract

Shared control rewrites force a sharp product bound for two jointly faithful finite codes.

**Definition 1.1 (A control bit is written into one data coordinate).**

$$\forall d: \mathbb{N}, i: \operatorname{Fin}(d), z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)),\\controlRewrite_{i}(z) = (\operatorname{single}(i, z_{2}), 0).$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.controlRewrite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rewrite indexed by i clears every data coordinate except i, copies the control bit into coordinate i, and then clears the control bit.

**Definition 1.2 (The allowed translations and rewrites).**

$$\forall d: \mathbb{N}, sharedControlActions_{d} = \{f: (((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2))) \to ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)) \mid (\exists i: \operatorname{Fin}(d), f = (z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)) \mapsto z + (\operatorname{single}(i, 1), 0))) \lor (f = (z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)) \mapsto z + (0, 1))) \lor (\exists i: \operatorname{Fin}(d), f = controlRewrite_{i})\}.$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.sharedControlActions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The action set contains translation by each data basis vector, translation by the control basis vector, and every indexed control rewrite.

**Definition 1.3 (Every state action descends to the code).**

$$\forall d: \mathbb{N}, \alpha: Type, u: (((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2))) \to \alpha,\\\operatorname{DynamicallyClosed}(u) \iff \forall f \in sharedControlActions_{d}, \exists F: (\alpha) \to \alpha, u \circ f = F \circ u.$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.DynamicallyClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A code is dynamically closed when each allowed action has an induced update on code values, with the two routes from a state to a new code value equal.

**Definition 1.4 (The prefix code).**

$$\forall d: \mathbb{N}, h: \mathbb{N}, p: h \leq d, z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)),\\prefixCode_{p}(z) = ((i: \operatorname{Fin}(h) \mapsto z_{1}(\operatorname{castLE}(p, i))), z_{2}).$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.prefixCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For h at most d, the prefix code retains the first h data coordinates and the shared control bit.

**Definition 1.5 (The suffix code).**

$$\forall d: \mathbb{N}, h: \mathbb{N}, p: h \leq d, z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)),\\suffixCode_{p}(z) = ((i: \operatorname{Fin}(d - h) \mapsto z_{1}(h + i)), z_{2}).$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.suffixCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For h at most d, the suffix code retains data coordinates h through d minus one and the shared control bit.

**Theorem 1.6 (Classification, storage lower bound, and attainment).**

$$\forall d: \mathbb{N}, 2 \leq d, \alpha: Type, \beta: Type, [\operatorname{Finite}(\alpha)], [\operatorname{Finite}(\beta)],\\u: (((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2))) \to \alpha, v: (((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2))) \to \beta,\\(\operatorname{DynamicallyClosed}(u) \land \operatorname{DynamicallyClosed}(v) \land \operatorname{Injective}((z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)) \mapsto (u(z), v(z))))) \Rightarrow\\(\exists K: \operatorname{Submodule}(\operatorname{ZMod}(2), ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2))),\\(\forall z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)), y: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)), (u(z) = u(y)) \iff ((z - y) \in K)) \land\\((K \subseteq \operatorname{range}(\operatorname{inl}(\operatorname{ZMod}(2), (\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)))) \lor (K = \operatorname{top}()))) \land\\(\forall K: \operatorname{Submodule}(\operatorname{ZMod}(2), ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2))),\\((K \subseteq \operatorname{range}(\operatorname{inl}(\operatorname{ZMod}(2), (\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)))) \lor (K = \operatorname{top}())) \Rightarrow\\((\operatorname{DynamicallyClosed}(\operatorname{mkQ}(K))) \land\\(\forall z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)), y: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)), (\operatorname{mkQ}(K)(z) = \operatorname{mkQ}(K)(y)) \iff ((z - y) \in K)))) \land\\(((\neg \operatorname{Injective}(u)) \land (\neg \operatorname{Injective}(v))) \Rightarrow (2^{(d + 2)} \leq (\operatorname{ncard}(\operatorname{range}(u)) \cdot \operatorname{ncard}(\operatorname{range}(v))))) \land\\(\forall h: \mathbb{N}, ((1 \leq h) \land (h \leq (d - 1))) \Rightarrow\\((\operatorname{DynamicallyClosed}(suffixCode_{h \leq d})) \land (\operatorname{DynamicallyClosed}(prefixCode_{h \leq d})) \land\\(\operatorname{Injective}((z: ((\operatorname{Fin}(d)) \to \operatorname{ZMod}(2), \operatorname{ZMod}(2)) \mapsto (suffixCode_{h \leq d}(z), prefixCode_{h \leq d}(z))))) \land\\((\operatorname{ncard}(\operatorname{range}(suffixCode_{h \leq d})) \cdot \operatorname{ncard}(\operatorname{range}(prefixCode_{h \leq d}))) = 2^{(d + 2)}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.shared_control_bit_storage_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation closure makes each fiber relation a coset relation of a ZMod 2 subspace. Stability under the control rewrites then forces that subspace either into the data hyperplane or to be the whole state space.

Conversely, every subspace of the data hyperplane, together with the whole state space, is realized by its finite quotient code. Translations descend by quotient addition, while each linear control rewrite vanishes on the data hyperplane and therefore descends as well. Equality of quotient values is exactly membership of the state difference in the chosen subspace.

For two jointly faithful noninjective codes, their kernel subspaces meet only at zero. The dimension formula for a sum and intersection, together with quotient cardinality, gives the displayed storage product bound.

Complementary prefix and suffix codes are dynamically closed and jointly injective. Each keeps the control bit, and their finite range sizes multiply to the lower bound.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.DynamicallyClosed`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.controlRewrite`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.prefixCode`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.sharedControlActions`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.shared_control_bit_storage_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.suffixCode`
