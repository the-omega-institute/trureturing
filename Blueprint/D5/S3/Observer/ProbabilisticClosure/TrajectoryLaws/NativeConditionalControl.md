# Native conditional continuation and control projection

## Abstract

Equal native controls give equal visible operation traces at every finite event count.

A full acquired native state contains the original control and registers, the payload-return bank and both acquired-letter counters. Stream is the raw natural-indexed sequence of Fin(2) letters. nativeDrive uses the original native transaction table. A Read advances the raw cursor by one; the matching Stop costs zero Reads. Visible retains the emitted operation list and successor control, including pending color and delivered status. It omits registers and numeric banks only from this projection.

**Theorem 1.1 (Control determines every finite visible trace).**

$$\forall c:AcquiredNativeState, (\forall d:AcquiredNativeState, (\forall omega:Stream, (\forall n:Nat, (\operatorname{control}(c)=\operatorname{control}(d)\Rightarrow\operatorname{visible}(\operatorname{nativeDrive}(c,omega,n))=\operatorname{visible}(\operatorname{nativeDrive}(d,omega,n))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl.drive_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement ranges over arbitrary pairs of full native states, every common raw stream and every natural event count, without a reachability assumption. Equal controls schedule the same operation and give equal successor controls. The recursive comparison applies this relation to the two actual successor states on the same shifted stream, then prepends their common operation. Failure, pending Stop and delivery are included. Equality of the projected trace does not assert equality of the hidden registers or return and count banks.

For depth k in PNat, rate(k)=fib(k+1)/fib(k+3) lies strictly between zero and one. jointLaw(mu) first draws one k from the arbitrary PMF mu and uses its raw Bernoulli law for the entire stream. nativeEvent(h,c) is the exact independently emitted initialized-history cylinder. likelihood(h,k) is the product mass of every acquired Read, including rejected seed pairs, returns and partial cuts; its positive mixture normalizer defines posterior(mu,h,c). No support bound, finite mean or future acceptance event is assumed.

The conditional joint law of the unchanged depth and the unread raw tail equals jointLaw(posterior). The prefix cylinder and tail sigma-algebras involve disjoint raw coordinates, so their fixed-depth product factorization survives the countable posterior mixture. Native stopping comparisons keep the full state, marker writes and the unique unpaid Stop. This conditional-law identity and the control projection serve different purposes: the former preserves the source law and the latter justifies omitting past held fields from the permitted residual transcript.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl.drive_control`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder](NativeAcquiredPrefixCylinder.md)
