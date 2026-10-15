# Total computable fixed-menu prediction

## Abstract

Total computable fixed-menu prediction

For each fixed public D and ordered menu S, the finite input type Fin(length(S))->Reply has a primitive-recursive reconstruction table. Its entries are computed by reconstruct, not by an assumed decoder or an assumed normal-form semantics. Lookup uses the first occurrence of an address in the public order, and never sorts the menu.

Restore rejects wrong tuple lengths, inconsistent repeated coordinates and constructor inconsistency as none. Decode returns the fixed all-absent vector after rejection; after success it applies genuine native substitution and four-valued readout to the reconstructed representative. Raw input is an arbitrary list of natural numbers. RawValid requires the correct length and every symbol below four, with alpha,beta,branch,absent represented by 0,1,2,3.

The total functions cover malformed and inconsistent represented inputs. The table is primitive recursive because its domain is finite for this fixed public menu. Unbounded natural iteration and exact readout reuse their existing primitive-recursive implementations. This proves computability, not a time, bit, energy, physical memory or native Read cost bound.

Fix D>=1 and an ordered public menu P in A_D: every literal is Rq with length(q)+1<=D. RelativeMenu removes this first R at every list position, and PublicMenu restores it. Empty, epsilon-containing and nested relative menus all remain in scope. Source is the exact native FreeMagma Bool carrier; no positive-source, right-only-path or restricted-epoch promise is used.

InitialSufficient means there exists one function from the initial reply list and the supplied natural count to a reply list, correct for every v with original height(v)<=D and every count k. EffectiveSufficient adds total ComputableTwo evidence for that same represented function domain. CodeSufficient means that equality of the whole initial vectors of any two such v implies equality of the exact original FM.17 numerical ranks.

These three clauses are equivalent to relative prefix closure. Sufficiency reconstructs an actual representative from the root reply and recursive child blocks; the total computable decoder evaluates its future trajectory. Necessity uses every prescribed missing-prefix pair, which jointly supplies equal initial vectors, unequal original codes and a common legal future distinction. Each selected vector retains the original public order.

The D=1 case allows only epsilon as a relative address, so every admissible menu is prefix-closed. For an empty menu reconstruction returns alpha, the original rank is zero and every future output is empty. Relabeling by the initial R is valid at every count and for blocked suffixes. The four-way statement asserts value prediction under a supplied same-source count; it makes no acquisition, authentication, runtime or physical-efficiency claim.

The four-way criterion follows from the reconstruction theorem and every_missing_prefix_obstruction. Prefix closure gives the total computable decoder and equality of original ranks; a total computable decoder is a function. If a prefix is missing, the prescribed same pair contradicts both functional prediction and rank determination. Thus each of the three conditions is equivalent to prefix closure, with no normal-form semantics premise. This application retains the full original height family and all natural counts.

**Theorem 1.1 (Totality, rejection and all attained vectors).**

$$\forall D: Nat, (\forall S: Menu, (((\operatorname{PrefixClosed}\left(S\right)) \land (\forall q: Address, ((q \in S) \implies (\operatorname{length}\left(q\right) < D)))) \implies ((\operatorname{ComputableTwo}\left(\operatorname{decode}\left(D, S\right)\right)) \land (\forall u: Source, (\forall k: Nat, (\operatorname{decode}\left(D, S, \operatorname{initial}\left(S, u\right), k\right) = \operatorname{future}\left(S, u, k\right)))) \land (\operatorname{PrimrecTwo}\left(\operatorname{rawDecode}\left(D, S\right)\right)) \land (\operatorname{ComputableTwo}\left(\operatorname{rawDecode}\left(D, S\right)\right)) \land (\forall xs: \operatorname{List}\left(Nat\right), (\forall k: Nat, ((\operatorname{rawValid}\left(S, xs\right) = false) \implies (\operatorname{rawDecode}\left(D, S, xs, k\right) = \operatorname{replicate}\left(\operatorname{length}\left(S\right), absent\right))))) \land (\forall xs: \operatorname{List}\left(Nat\right), (\forall k: Nat, ((\operatorname{restore}\left(D, S, \operatorname{map}\left(rawReply, xs\right)\right) = none) \implies (\operatorname{rawDecode}\left(D, S, xs, k\right) = \operatorname{replicate}\left(\operatorname{length}\left(S\right), absent\right))))) \land (\forall u: Source, (\forall k: Nat, (\operatorname{rawDecode}\left(D, S, \operatorname{rawVector}\left(S, u\right), k\right) = \operatorname{future}\left(S, u, k\right)))) \land (\forall u, v: Source, ((\operatorname{initial}\left(S, u\right) = \operatorname{initial}\left(S, v\right)) \implies (\operatorname{code}\left(S, u\right) = \operatorname{code}\left(S, v\right)))) \land (\forall xs: \operatorname{List}\left(Reply\right), (\forall t: Source, ((\operatorname{restore}\left(D, S, xs\right) = \operatorname{some}\left(t\right)) \implies ((\operatorname{height}\left(t\right) \leq D) \land (\operatorname{initial}\left(S, t\right) = xs))))) \land (\forall xs: \operatorname{List}\left(Reply\right), ((\operatorname{restore}\left(D, S, xs\right) = none) \iff (\neg (\exists u: Source, (\operatorname{initial}\left(S, u\right) = xs))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuEffective.total_native_menu_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every attained vector reconstructs one actual representative with its original code and entire future trajectory. Induction on reconstruction fuel shows that acceptance realizes every selected coordinate and bounds the returned tree height. Tuple coherence also checks repeated coordinates. Every realizable list is accepted under prefix closure, so rejection is exactly nonexistence of a realizing source. Equal attained initial lists yield the same representative and hence equal original ranks. The guarantee ranges over all finite actual sources and therefore over the full original height family.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuEffective.total_native_menu_decoder`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuReconstruction](NativeFiniteMenuReconstruction.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformInput](NativeUniformInput.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree](NativeUniformTree.md)
