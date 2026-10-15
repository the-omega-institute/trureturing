# Configurations and rooted transport

## Abstract

Configuration ideal completion, actual finite edge composition and invertible graph transport.

**Definition 1.1 (Finite configurations form an ideal basis).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{PartialOrder}\left(E\right)] (\forall C: \operatorname{Predicate}\left(\operatorname{Finset}\left(E\right)\right), ((\operatorname{Apply}\left(C, \emptyset\right) \land (\forall e: E, \operatorname{Finite}\left(\operatorname{Iic}\left(e\right)\right))) \implies \operatorname{OrderIsomorphic}\left(\operatorname{Configurations}\left(C\right), \operatorname{OrderIdeal}\left(\operatorname{FiniteConfigurations}\left(C\right)\right)\right))))$$

*Formalization.* `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.configurationIdealIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Glynn Winskel (1987). *Event Structures*. URL: <https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf>.

*Commentary.*

A configuration is a lower set whose finite subsets are compatible. Each principal predecessor set is finite, while the ambient poset may be infinite. A nonempty directed family has a compatible lower union: every finite test set lies in one member by finite induction on directedness. The finite subconfigurations of any configuration are nonempty, lower closed and directed. Their union is the configuration because each event lies in its finite principal predecessor set. An ideal is sent to its union; any finite subconfiguration of that union belongs to the ideal by a finite upper-bound argument. These constructions are inverse and preserve inclusion. Empty compatibility supplies the bottom finite configuration.

**Theorem 1.2 (Positive histories and finite observer clocks).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{PartialOrder}\left(E\right)] (\forall C: \operatorname{Finset}\left(E\right), (\forall D: \operatorname{Finset}\left(E\right), (\forall B: \operatorname{Finset}\left(E\right), (\forall o: \operatorname{Predicate}\left(E\right), (\forall w: \operatorname{Function}\left(E, \operatorname{Real}\left(\right)\right), (((((\operatorname{IsLowerSet}\left(C\right) \land \operatorname{IsLowerSet}\left(D\right)) \land (C \subseteq D)) \land (D \subseteq B)) \land (\forall e: E, (\operatorname{Apply}\left(o, e\right) \implies (0 < \operatorname{Apply}\left(w, e\right))))) \implies (\exists l: \operatorname{List}\left(E\right), (((((((\operatorname{Exec}\left(C, l, D\right) \land (\operatorname{Length}\left(l\right) = \operatorname{gapCard}\left(C, D\right))) \land (\forall m: \operatorname{List}\left(E\right), (\operatorname{Exec}\left(C, m, D\right) \implies (\operatorname{Length}\left(m\right) = \operatorname{gapCard}\left(C, D\right))))) \land (\operatorname{gapCard}\left(C, B\right) = (\operatorname{gapCard}\left(C, D\right) + \operatorname{gapCard}\left(D, B\right)))) \land (\operatorname{clockFinite}\left(o, w, C\right) \le \operatorname{clockFinite}\left(o, w, D\right))) \land ((\exists e: E, ((\operatorname{Member}\left(e, D\right) \land \operatorname{NotMember}\left(e, C\right)) \land \operatorname{Apply}\left(o, e\right))) \implies (\operatorname{clockFinite}\left(o, w, C\right) < \operatorname{clockFinite}\left(o, w, D\right)))) \land (\forall m: \operatorname{List}\left(E\right), (\operatorname{Exec}\left(D, m, C\right) \implies (l = \operatorname{Nil}\left(\right))))) \land (\forall e: E, (\forall p: \operatorname{List}\left(E\right), (\forall s: \operatorname{List}\left(E\right), ((\operatorname{pathWeight}\left(w, \operatorname{Cons}\left(e, s\right)\right) = \operatorname{pathWeight}\left(w, \operatorname{Append}\left(p, s\right)\right)) \iff (\operatorname{Apply}\left(w, e\right) = \operatorname{pathWeight}\left(w, p\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.finite_history_clocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For C contained in D contained in B, the actual basic-edge schedule from C to D exists and has exactly |D minus C| steps. Every legal path with those endpoints has this same length. These gap cardinalities add across the nested triple. The finite observer clock sums only observed events with strictly positive weights: inclusion cannot decrease it, and any newly observed event makes it strictly larger. If a reverse execution from D to C exists, the forward history is empty. Replacing one event by a list of pieces preserves duration exactly when the original weight equals the sum of the piece weights. No infinite configuration sum is asserted to be a finite real number.

**Theorem 1.3 (Actual edge diamonds determine finite path composites).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{PartialOrder}\left(E\right)] (\forall R: \operatorname{DependentReadout}\left(E\right), (\operatorname{PathIndependent}\left(R\right) \iff \operatorname{DiamondCompatible}\left(R\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.pathIndependent_iff_diamondCompatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path map is recursively the composite of actual edge maps. The diamond hypothesis concerns only the two legal edge composites, without an assumed surrounding-path interchange. At finite endpoints the frozen EnabledPathSwapConnectivity theorem is applied to the finite endpoint subtype, then lifted back to the arbitrary ambient poset. Adjacent incomparable swaps connect all legal schedules. Equality on each local diamond therefore propagates through prefixes and suffixes. Conversely the two length-two paths give each diamond. ConfigurationReadout restricts this result faithfully to the original fibres defined only at legal configurations.

**Theorem 1.4 (Parallel sections correspond to closed-walk fixed points).**

$$(\forall V: \operatorname{Type}\left(\right), (\forall G: \operatorname{BiGraph}\left(V\right), (\forall F: \operatorname{Function}\left(V, \operatorname{Type}\left(\right)\right), (\forall T: \operatorname{EdgeTransport}\left(G, F\right), (\forall r: V, (\operatorname{GraphConnectedFrom}\left(G, r\right) \implies \operatorname{Bijective}\left(\operatorname{rootSectionMap}\left(T, r\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.rootSectionMap_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Walk transports are constructed recursively from bijective oriented edge maps; reversal uses the given inverse edge maps, and concatenation follows by induction. A root point fixed by every closed walk transports consistently to a parallel section along chosen root paths. Comparing two paths forms a closed walk and proves independence. Evaluation at the root is the inverse map. No claim that a loop operator is the identity is needed: it must fix the chosen root point.

**Theorem 1.5 (Tree coordinates make the reversible edge maps identity).**

$$(\forall V: \operatorname{Type}\left(\right), (\forall G: \operatorname{SimpleGraph}\left(V\right), (\forall F: \operatorname{Function}\left(V, \operatorname{Type}\left(\right)\right), (\forall r: V, (\forall e: \operatorname{EdgeEquivalences}\left(G, F\right), ((\operatorname{IsTree}\left(G\right) \land \operatorname{ReverseIsInverse}\left(G, e\right)) \implies (\exists c: \operatorname{RootFibreCoordinates}\left(F, r\right), (\forall v: V, (\forall w: V, (\operatorname{Adjacent}\left(G, v, w\right) \implies (\operatorname{Compose}\left(\operatorname{Apply}\left(c, v\right), \operatorname{Apply}\left(e, v, w\right), \operatorname{Inverse}\left(\operatorname{Apply}\left(c, w\right)\right)\right) = \operatorname{Identity}\left(\operatorname{Apply}\left(F, r\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.tree_coordinate_trivialization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique simple root path gives the fibre coordinate at every vertex. Tree path uniqueness and edge reversal imply that every transported edge is the identity on the root fibre. The original walk and every literal edge occurrence are unchanged by this coordinate construction. Inverse transport is an algebraic operation on fibre values; it is not a deletion edge in the positive history relation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.configurationIdealIso`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.finite_history_clocks`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.pathIndependent_iff_diamondCompatible`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.rootSectionMap_bijective`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.tree_coordinate_trivialization`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity](../PartialIdentification/EnabledPathSwapConnectivity.md)
