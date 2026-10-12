# Full-Support Native Window Laws and Actual Null Continuation

## Abstract

The same full-support natural window laws preserve every proper seam-coordinate joint table while their actual appended-null reply laws remain separated.

Window is the original five-letter alphabet, in the order null, low, high, ends, middle. Its natural displacements are respectively (0,0), (1,0), (1,1), (2,1), (0,1). The original high-to-low reader uses S(a,b)=(a+2b,2a+3b), q(a,b)=2a+3b, and the guard excluding an incoming true seam followed by a true high bit. The initial seam is false and the initial composition is (0,0).

**Definition 1.1 (Natural chronological composition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.composition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.composition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

composition(w), also denoted C(w), folds the original update C'=S(C)+bitComposition(b) along the window list. The coordinates are natural numbers. Every prefix uses the same word and update.

**Definition 1.2 (The same padded binary word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.digits`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.digits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

digits(w) maps the complete existing highBits(w) from Bool to Fin 2, with false mapped to zero and true mapped to one. It reverses each printed three-bit window and preserves the chronological window order, the leading null windows and all original positions.

**Theorem 1.3 (The original reader's complete successful state).**

$$\forall w: \operatorname{List}\left(Window\right), ((\operatorname{legal}\left(false, \operatorname{highBits}\left(w\right)\right)) \implies (\operatorname{eval}\left(\operatorname{rawMachine}\left(0\right), w\right) = \operatorname{some}\left((\operatorname{finalSeam}\left(w\right), \operatorname{residue}\left(0, \operatorname{C}\left(w\right)\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.actual_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

eval is the existing reader's initialized DFA evaluation. finalSeam(w) is false for the empty word and the low bit of its last window otherwise. residue(0,C(w)) casts the two natural coordinates to the integer carrier. The natural history determines both the chronological fold and its terminal seam. Applying this equality to each legal prefix realizes the complete reported seam history in the same reader.

**Theorem 1.4 (Actual natural execution).**

$$\forall w: \operatorname{List}\left(Window\right), ((\operatorname{legal}\left(false, \operatorname{highBits}\left(w\right)\right)) \implies (\operatorname{task}\left(0, w\right) = \operatorname{some}\left(\operatorname{q}\left(\operatorname{C}\left(w\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.actual_quantity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

task(0,w) is the existing integer output, not a reduced modular output. The natural quantity in the displayed formula is cast to the integer carrier ZMod 0. A legal source has the natural composition determined by its actual history. The natural-history realization identifies the existing reader's successful state; folding that same history determines its final composition.

**Theorem 1.5 (Exact Fibonacci coordinates of the source).**

$$\forall w: \operatorname{List}\left(Window\right), (\operatorname{fibPair}\left(\operatorname{digits}\left(w\right)\right) = \operatorname{S}\left(\operatorname{C}\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.composition_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

fibPair is the existing padded Fibonacci two-register evaluator. Appending each original window advances the registers three times and adds precisely S(bitComposition(b)). Induction over the chronological word therefore gives the formula for every finite word. This arithmetic formula alone does not make an illegal word a successful source.

**Definition 1.6 (The entire legal fixed-length source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.Source`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.Source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source(n) consists of all functions from Fin n to Window whose complete high-to-low bits are legal from the false seam. There is no final-seam restriction, End action, leading-nonzero test or independence premise. List.ofFn gives the original window list. Its actual seam vector consists of the initial false seam followed by the low bit of every window.

**Definition 1.7 (The actual natural null reply).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.reply`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.reply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

reply(w)=qS(C(List.ofFn(w))) is a natural number. The appended input is the existing null window. It is legal at either live seam, applies the full clock, and sets the next seam to false.

**Theorem 1.8 (Realization of the specified continuation).**

$$\forall n: \mathbb{N}, (\forall w: \operatorname{Source}\left(n\right), (\operatorname{task}\left(0, \operatorname{appendNull}\left(\operatorname{ofFn}\left(w\right)\right)\right) = \operatorname{some}\left(\operatorname{reply}\left(w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.actual_null_reply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

appendNull(v) denotes v followed by the singleton null window. The displayed natural reply is cast to the same integer output carrier as task(0). The equality ranges over the entire legal source, including the all-null source and sources ending at seam one.

**Theorem 1.9 (Exact separation at fixed length).**

$$\forall n: \mathbb{N}, (\forall u: \operatorname{Source}\left(n\right), (\forall v: \operatorname{Source}\left(n\right), ((\operatorname{reply}\left(u\right) = \operatorname{reply}\left(v\right)) \implies (u = v))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.native_reply_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual null reply is injective on Source(n). Appending the null window and one zero digit makes the first Fibonacci register equal to that reply. The existing equal-width canonical numeric-order theorem identifies its strict order with the padded words' lexicographic order. Equal replies therefore have equal padded bit words, and each original three-bit window recovers its own letter. This is a fixed-length assertion; different amounts of leading padding are not identified with the same source.

**Definition 1.10 (The null and middle letters).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.bitWindow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.bitWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

bitWindow sends zero to null and one to middle. Both letters have false high and low bits.

**Definition 1.11 (The actual zero-seam cube).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.embed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.embed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

embed(n,b) applies bitWindow at each original position. Every resulting source is legal, the map is injective, and its complete seam vector is the all-false vector of length n+1.

**Definition 1.12 (The existing real parity laws).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.cubeLaw`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.cubeLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cubeLaw(n,e) is the real cast of the existing rational fair parityLaw(n,e). A zero coordinate has sign minus one and a one coordinate sign plus one. For positive n and e equal to minus one or one, the mass is one and all proper coordinate restrictions have equal complete tables under the two signs.

**Definition 1.13 (A common positive background on the entire source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.law`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.law` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

law(n,t,e)(w)=(1-t)/card(Source(n))+t*pushforward(embed(n),cubeLaw(n,e))(w). Here pushforward is the existing CapacityMonotone finite-source real pushforward: pushforward(f,p)(y) sums p(x) over the source points with f(x)=y. Its output carrier need not be finite, and signed real tables are allowed. Thus both laws use the uniform background on the entire legal five-mode source, not merely the embedded cube. The parameter t is real.

**Definition 1.14 (The full seam history).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.seams`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.seams` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

seams(w) is false followed by the low bit of every source window, in its original order. It includes the initial and final seams.

**Definition 1.15 (The mass of a finite source event).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.mass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

mass(p,E) sums p(w) over all finite source points satisfying the predicate E. The same mass definition underlies the joint, seam and conditional tables.

**Definition 1.16 (Separate full joint reports for proper coordinate sets).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.jointMass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.jointMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

jointMass(p,A,s,y) sums p(w) over sources with seams(w)=s and w(i)=y(i) for every i in A. The sets A retain the original positions. Empty, noncontiguous and n-1 element sets are included. Although y is written as a full tuple, only its restriction to A is tested. These are separate probability tables, not a paired archive combining all reports from the same sample.

**Definition 1.17 (Events of the complete seam history).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.seamEventMass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.seamEventMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

seamEventMass(p,E) is the total p-mass of sources whose full seam vector lies in E.

**Definition 1.18 (Positive-event conditional coordinate tables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.conditionalMass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.conditionalMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

conditionalMass(p,E,A,y) divides the mass of E together with the coordinate restriction by seamEventMass(p,E). Conditional-law assertions concern positive denominators; no conditional law is asserted at a zero-mass event.

**Definition 1.19 (Fixed linear readouts of actual prefix compositions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.linearReadout`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.linearReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

linearReadout(j,a,b,w)=a*C(take(j,List.ofFn(w))).first+b*C(take(j,List.ofFn(w))).second, with the natural coordinates cast to the reals. The coefficients are fixed; they do not depend on the source or its replies.

**Definition 1.20 (Total variation of finite source laws).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.sourceTV`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.sourceTV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceTV(p,q) is half the sum over the entire Source(n) of the absolute value of p(w)-q(w).

**Definition 1.21 (Total variation of the complete actual reply laws).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.replyTV`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.replyTV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

replyTV(p,q) is half the sum of the absolute reply-mass difference over the actual finite image of reply on Source(n). The masses are pushforward(reply,p) and pushforward(reply,q). Values outside this image have zero mass under both laws.

**Theorem 1.22 (All proper joint reports and actual continuation separation).**

$$\forall n: \mathbb{N}, ((3 \le n) \implies (\forall t: \mathbb{R}, (((0 < t) \land (t < 1)) \implies ((\forall e: \mathbb{Z}, ((e \in \{-1,1\}) \implies ((\forall w: \operatorname{Source}\left(n\right), (0 < \operatorname{law}\left(n, t, e, w\right))) \land (\operatorname{Total}\left(\operatorname{law}\left(n, t, e\right)\right) = 1)))) \land (\forall A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), ((A \neq univ) \implies (\forall s: \operatorname{List}\left(Bool\right), (\forall y: \operatorname{Fin}\left(n\right) \to Window, (\operatorname{J}\left(\operatorname{law}\left(n, t, 1\right), A, s, y\right) = \operatorname{J}\left(\operatorname{law}\left(n, t, -1\right), A, s, y\right)))))) \land (\forall E: \operatorname{List}\left(Bool\right) \to Prop, ((\operatorname{M}\left(\operatorname{law}\left(n, t, 1\right), E\right) = \operatorname{M}\left(\operatorname{law}\left(n, t, -1\right), E\right)) \land ((0 < \operatorname{M}\left(\operatorname{law}\left(n, t, 1\right), E\right)) \implies (\forall A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), ((A \neq univ) \implies (\forall y: \operatorname{Fin}\left(n\right) \to Window, (\operatorname{K}\left(\operatorname{law}\left(n, t, 1\right), E, A, y\right) = \operatorname{K}\left(\operatorname{law}\left(n, t, -1\right), E, A, y\right)))))))) \land (\forall w: \operatorname{Source}\left(n\right), (\operatorname{task}\left(0, \operatorname{appendNull}\left(\operatorname{ofFn}\left(w\right)\right)\right) = \operatorname{some}\left(\operatorname{reply}\left(w\right)\right))) \land ((\operatorname{pushforward}\left(reply, \operatorname{law}\left(n, t, 1\right), 0\right) - \operatorname{pushforward}\left(reply, \operatorname{law}\left(n, t, -1\right), 0\right) = (-1)^{n} t / 2^{(n-1)}) \land ((-1)^{n} t / 2^{(n-1)} \neq 0)) \land (\forall j: \mathbb{N}, ((j \le n) \implies (\forall a: \mathbb{R}, (\forall b: \mathbb{R}, (\operatorname{Expected}\left(\operatorname{law}\left(n, t, 1\right), \operatorname{linearReadout}\left(j, a, b\right)\right) = \operatorname{Expected}\left(\operatorname{law}\left(n, t, -1\right), \operatorname{linearReadout}\left(j, a, b\right)\right)))))) \land (\operatorname{Expected}\left(\operatorname{law}\left(n, t, 1\right), reply\right) = \operatorname{Expected}\left(\operatorname{law}\left(n, t, -1\right), reply\right)) \land (\operatorname{sourceTV}\left(\operatorname{law}\left(n, t, 1\right), \operatorname{law}\left(n, t, -1\right)\right) = t) \land (\operatorname{replyTV}\left(\operatorname{law}\left(n, t, 1\right), \operatorname{law}\left(n, t, -1\right)\right) = t)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.native_probability_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two laws in the formula are law(n,t,1) and law(n,t,-1). Total(p) denotes the finite sum of all source masses. J abbreviates jointMass, M abbreviates seamEventMass, and K abbreviates conditionalMass. Expected(p,H) is the finite sum of p(w)*H(w). The sign set contains minus one and one; A ranges over Finset(Fin n), s over finite Bool lists, y over full Window tuples, and E over all predicates on the complete seam history.

Both laws are strictly positive on every legal word and have total mass one. The embedded cube has one constant actual seam vector, so its joint report tests only the selected binary coordinates. The existing parity marginal equality then gives every proper table, including the empty table. The common uniform background preserves these equalities. Summing over any seam event gives equal event masses; division by a common positive mass gives the conditional tables.

The actual null zero fiber is precisely the all-null source. Its cube sign is minus one to the power n, so the signed zero-event difference is the displayed nonzero quantity. Prefix induction expresses every fixed linear composition readout using the individual window marginals, hence their expectations agree, including the actual null quantity.

The two cube parity laws have disjoint support, each of total mass one. Their signed difference scales by t after the common background is added, giving source total variation t. The actual natural null reply is injective at fixed length, so its pushforward preserves this complete total variation. The entire-law separation is independent of n at fixed t, although the single zero-event difference decreases with n.

These assertions establish the finite probability and actual null-continuation relations. They assert no indicator L2 realization, local Gram spectrum, all-position Fibonacci marginal formula, recovery from paired archives, infinite-source compatibility or finite-sample decision theorem.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.Source`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.actual_null_reply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.actual_quantity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.actual_state`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.bitWindow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.composition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.composition_coordinates`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.conditionalMass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.cubeLaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.digits`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.embed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.jointMass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.law`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.linearReadout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.mass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.native_probability_separation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.native_reply_injective`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.reply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.replyTV`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.seamEventMass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.seams`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.sourceTV`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/NumeralSemantics](../../../../S1/Words/Palindromes/FridPrefix/NumeralSemantics.md)
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments](../../../Analytic/ReflectedSpectrum/ParityConditionedMoments.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber](NullReplyFiber.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../../../Entropy/Forgetting/CapacityMonotone.md)
