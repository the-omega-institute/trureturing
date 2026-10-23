# Six Actual Repeated-Partner Sources

## Abstract

Six simultaneous actual finite origins have five complete predecessor rows, while every literal native address respects its exact occurrence cone.

Sources are the original finite ordered Boolean trees. False is beta and true is alpha. The substitution sends alpha to beta and beta to the ordered pair (beta,alpha), preserving ordered brackets. Addresses are all finite Boolean lists, with false meaning left. The native replies are alpha, beta, branch and absent. The cut P consists of all eight depth-three addresses, in lexicographic order. Their classes are a,b1,a,b2,c,b3,c,b4. Canonical class names are the first occurrence ordinals 0,1,0,3,4,5,4,7; different classes retain every disequality.

The six source indices 0,1,2,3,4,5 denote 0a,0c,1,2,3,4 respectively. The target label is zero at the first two indices and j at index j+1. Group A consists of indices 0,2,3. The original orbit is T0=alpha and T(n+1)=rho(Tn). The fixed branch images are A=T2, C=T3 and Dj=T(j+3). In group A the a coordinate is beta and c is C; in the other group a is A and c is beta. The right coordinate bj is alpha at index j+1 and Dj elsewhere. Filling uses the same a coordinate at LLL and LRL and the same c coordinate at RLL and RRL.

**Theorem 1.1 (The Complete Cut Is Prefix Free).**

$$\operatorname{CutPrefixFree}\left(P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.prefix_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite addresses a and b in P, if a is a prefix of b then a=b. Every member of P is one of the eight listed positions and has length three. A prefix between equal-length lists is equality. This property lets canonical row naming and class-value recovery use the same literal cut: the recovered coordinate profile and its native-read and predecessor-row identities apply to every origin in the entire fiber.

**Theorem 1.2 (Simultaneous Actual Realization).**

$$(\forall z: \operatorname{Fin}\left(6\right), ((\operatorname{rho}\left(\operatorname{origin}\left(z\right)\right) = \operatorname{current}\left(z\right)) \land (\operatorname{canonicalRow}\left(P, \operatorname{current}\left(z\right)\right) = row) \land (\operatorname{canonicalRow}\left(P, \operatorname{origin}\left(z\right)\right) = \operatorname{predecessor}\left(\operatorname{label}\left(z\right)\right)))) \land (\operatorname{Injective}\left(predecessor\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.six_source_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem additionally asserts injectivity of predecessor on Fin 5. Each origin is an actual finite inverse of its fixed current tree. Its entire canonical current row equals row, so it belongs to the full infinite OriginFiber(P,row). Predecessor zero is the current row. At positive j the pair at qj is replaced by one concrete beta, while the other six occurrences retain their restricted partition with recomputed first occurrence names. The surviving repeated partner remains a hole. These are complete LiteralRow outputs, including their exterior, equality, disequality and absence information.

**Theorem 1.3 (Every Literal Occurrence and Suffix).**

$$\forall p: \operatorname{Fin}\left(8\right), (\forall w: Address, (\forall z: \operatorname{Fin}\left(6\right), (\operatorname{readout}\left(\operatorname{append}\left(\operatorname{position}\left(p\right), w\right), \operatorname{current}\left(z\right)\right) = \operatorname{readout}\left(w, \operatorname{values}\left(z, \operatorname{occurrenceClass}\left(p\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.occurrence_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The suffix is any finite address. It can be empty, continue past a leaf or leave the finite subtree. Absence is the ordinary native reply. Both occurrences of each repeated partner are included, but each address enters one occurrence cone.

**Theorem 1.4 (Exact All-Address Restriction).**

$$\forall a: Address, (\exists f: (Bool) \to (Reply), (\forall z: \operatorname{Fin}\left(6\right), (\operatorname{readout}\left(a, \operatorname{current}\left(z\right)\right) = \operatorname{f}\left(\operatorname{question}\left(a, z\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.all_address_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Location is determined by the first three literal address edges. Shorter addresses are common skeleton branches. Partner cones use the group-A bit, and the four right cones use their respective positive-singleton bit. Thus the actual replies are either constant or induce the stated group or singleton partition, depending on whether f has equal or distinct values. Question is only a mathematical factor of the original native readout; the controller receives no extra query port. The claim concerns these six simultaneous sources and does not make the full infinite fiber binary. Acquisition, authentication, export, lawful entry and isolation from discarded fields remain supplied conditions. No inverse service or physical resource bound follows.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.all_address_factor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.occurrence_read`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.prefix_free`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.six_source_realization`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder](ActualCutPartitionDecoder.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility](NativeFullRootFeasibility.md)
