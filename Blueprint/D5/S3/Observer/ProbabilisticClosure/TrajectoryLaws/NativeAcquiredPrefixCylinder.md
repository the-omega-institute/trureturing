# Native acquired-prefix cylinders and resumption

## Abstract

Native stream execution has exact finite history cylinders and resumes at its unread tail.

Stream is the raw function from natural indices to Letter, with Letter=Fin(2). readLetters erases only Stop operations from an operation list: it retains every acquired letter in its original order, including equal-pair seed rejections, accepted pairs, payload returns and partial cuts. rawTail(omega,k)(i)=omega(i+k). A Read has readCost one and a Stop has readCost zero.

nextOperation reads the first raw letter at seed, early-payload and active-fourth controls. At pending b it selects only Stop b; delivered selects no event. nextNative performs that scheduled operation with the original nativeStep. nativeDrive(c,omega,n) executes exactly n scheduled events: zero returns some([],c,0); a successor executes nextNative, recursively drives its full successor state on rawTail(omega,readCost(op)), then prepends op and adds its Read cost. Any unavailable event or failed transaction returns none. The operation history is an output of this recursion. The event bound n and the returned paid cursor k are distinct mathematical indices.

**Theorem 1.1 (Exact independently emitted history fibers).**

$$\forall h:\operatorname{List}(Operation), (\forall c:AcquiredNativeState, (\forall omega:Stream, (\forall k:Nat, ((\operatorname{nativeDrive}(initial,omega,\operatorname{length}(h))=\operatorname{some}((h,c,k)))\Leftrightarrow(\operatorname{run}(h)=\operatorname{some}(c)\land \operatorname{Prefix}(omega,\operatorname{readLetters}(h))\land k=\operatorname{length}(\operatorname{readLetters}(h)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.native_acquired_prefix_cylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality is universal in the finite operation history, full native state, raw stream and paid cursor. A history has a nonempty fiber exactly when its original run is legal, and its raw source fiber is precisely Prefix(omega,readLetters(h)). Every illegal history has an empty fiber. No completion assumption or uniform history bound occurs. Induction on the number of emitted events compares each independently scheduled nativeStep with supplied-list execute. For Read, the prefix condition splits into its first letter and the prefix of the raw tail; for Stop, neither letters nor paid cursor change. The returned full state is exactly the state of the original transaction fold, including every register and both numeric banks.

In the next formula, map is Option.map and pack(h,k)(v,d,j)=(h++v,d,k+j). The history concatenation joins the original prefix and newly emitted suffix; the full successor state d is unchanged by pack. PrefixFacts and reconstruct are the existing native reconstruction predicate and calculation, including ordered rejected pairs as form data, actual seed, payload phase, unbounded returns, paid letter counts, original writes, the post-third latch and held records. Those form data are mathematical descriptions, not additional retained native fields.

**Theorem 1.2 (Restart with the full state and untouched raw tail).**

$$\forall h:\operatorname{List}(Operation), (\forall c:AcquiredNativeState, (\forall omega:Stream, (\forall k:Nat, (\forall n:Nat, ((\operatorname{nativeDrive}(initial,omega,\operatorname{length}(h))=\operatorname{some}((h,c,k)))\Rightarrow(k=\operatorname{length}(\operatorname{readLetters}(h))\land \operatorname{nativeDrive}(initial,omega,\operatorname{length}(h)+n)=\operatorname{map}(\operatorname{pack}(h,k),\operatorname{nativeDrive}(c,\operatorname{rawTail}(omega,k),n))\land \exists nf:PrefixForm, (\operatorname{render}(nf)=h\land c=\operatorname{reconstruct}(nf)\land \operatorname{PrefixFacts}(nf,c))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.native_acquired_prefix_resumption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any emitted prefix event, the returned paid cursor equals length(readLetters(h)). For every further event count n, driving from the original initialization for length(h)+n events equals driving from its full returned state on exactly rawTail(omega,k), then joining the histories and paid cursors. The equality includes failure of an overlong execution. Induction on the prefix event count proves the driver concatenation identity, using rawTail(rawTail(omega,a),b)=rawTail(omega,a+b). The cylinder identity supplies the exact paid cursor and legal run. The unique existing native normal form then supplies c=reconstruct(nf) and every PrefixFacts field. At pending the next event is its matching zero-cost Stop; after delivery every positive event count fails and zero events retain the state.

All finite cuts are included, with both seeds, arbitrary rejected-pair order, arbitrary early and fourth-segment returns, pending and delivered states, and illegal operations excluded by the original transaction permissions. This deterministic statement does not supply a probability law for a shared hidden depth, a posterior for a finite or countable prior, a conditional-law identification, or a complete measurable continuation and recovery theorem.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.native_acquired_prefix_cylinder`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.native_acquired_prefix_resumption`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction](NativeAcquiredPrefixReconstruction.md)
