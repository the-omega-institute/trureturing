# Effective common-direction digit scheduling

## Abstract

A uniform digit controller combines prime-power tests into common-direction positive experiments and retains their complete scalar replies.

Fix a public natural modulus H>=1 and an arbitrary natural pair v=(a,b), including zero. The original chronological calls are R(a,b)=(b,a+b) and G(a,b)=(a+1,b); true means R in TerminalGcdAcquisitionCost.runWord. Write q(a,b)=2a+3b, K=PositiveProbeCompiler.direction(H), Gamma=PositiveProbeCompiler.graftBound(H), and B=max over p dividing H of factorization(H,p)*(p-1). An experiment word precedes a separately paid current gcd read. The reply is the whole natural number gcd(q(current),H).

**Definition 1.1 (A finite digit record).**

$$\operatorname{Axis}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.Axis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a prime power p^e, a record (s,r,d) consists of a completed digit level, its prefix residue, and the trial digit. Initially it is (0,0,0). Its center is r+p^s*d. The proof invariant for the unknown scalar n is s<=e, r=n mod p^s, 0<=d<p-1, and d<=floor(n/p^s) mod p. The natural rank is (e-s)*(p-1)-d.

**Definition 1.2 (Advance from the full reply).**

$$\operatorname{advance}\left(p, e, a, g\right) = \operatorname{digitUpdate}\left(p, e, a, g\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Completed records stay fixed. Otherwise divisibility of the complete reply g by p^(s+1) accepts the center as the next prefix and resets the trial to zero. A failed test increments d when another tested digit remains. After all p-1 failures the last digit p-1 is inferred, the prefix is extended, and the trial resets. Each active update strictly decreases the rank; accepting a low trial can decrease it by more than one. No valuation or Boolean answer replaces g.

**Definition 1.3 (One computable CRT shift).**

$$\operatorname{shift}\left(H, a\right) = \operatorname{firstCompatibleBelow}\left(H, a\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.shift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each unfinished axis request the negative of its trial center modulo p^e; for a finished axis request the negative of its recovered residue. Compatible(H,a,c) means that desired(p,a)+c is divisible by p^e at every prime divisor. The algorithm searches 0,...,H-1 for the first compatible shift. The existing ZMod CRT equivalence proves that this bounded search succeeds when H>0. The equivalence is used only in the correctness proof; the computation is the finite search. No polynomial local-work bound is attached to it.

**Definition 1.4 (Chronological full-reply execution).**

$$\operatorname{rounds}\left(H, answer, j, a\right) = \operatorname{iterateFullReply}\left(j, a\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.rounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A round computes c from the current finite table, receives g from the reply interface, advances every axis from that same g, and records (c,g) before the recursively generated suffix. After B rounds every prime-power residue is complete. Completed axes remain valid during padding rounds. Negating a final compatible shift in ZMod H reconstructs n modulo H. Thus all axes finish with B paid scalar replies, rather than a sum of their budgets.

**Definition 1.5 (The two public directions).**

$$\operatorname{schedule}\left(H, answer\right) = \operatorname{twoStages}\left(\operatorname{K}\left(H\right), \operatorname{B}\left(H\right), answer\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.schedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same local digit policy runs first at direction K and then at direction K+1. The output contains both recovered scalars and the chronological concatenation of triples (k,c,g). For H=1 both stages return zero with an empty tape. The controller takes only H and incoming replies; it never takes a hidden source coordinate. compiledReply(H,v,k,c) is the mathematical interpreter obtained by executing the actual compiler word at v and reading its gcd. It is not a local primitive supplied to the controller.

**Definition 1.6 (An explicit earned entry residue).**

$$\operatorname{decode}\left(H, y\right) = \operatorname{inverseResidueDirection}\left(\operatorname{K}\left(H\right), \operatorname{inverseQuantityRows}\left(y\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two consecutive quantity rows have matrix [[2,3],[3,5]]. Apply its integer inverse [[5,-3],[-3,2]] in ZMod H, then apply the inverse of the public residue replacement permutation to the K-th power. The resulting pair is the entry residue. This is a computation on the two earned scalars, not a hidden label.

**Theorem 1.7 (All natural sources and the complete reply tape).**

$$\forall H \in \operatorname{Nat}\left(\right), \forall v \in \operatorname{NatPair}\left(\right), \operatorname{positive}\left(H\right) \implies (\operatorname{decodedSchedule}\left(H, v\right) = \operatorname{residue}\left(H, v\right) \land \operatorname{scalars}\left(H, v\right) = \operatorname{consecutiveQuantities}\left(H, v\right) \land \operatorname{tapeLength}\left(H, v\right) = \operatorname{readBudget}\left(H\right) \land \operatorname{allActualCompilerTriples}\left(H, v\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.effective_scheduler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every H>=1 and every actual natural pair v, the decoded output is residueSource(H,v). The two scalar outputs are q(R^K(v)) and q(R^(K+1)(v)) in ZMod H. The tape has zero entries when H=1 and exactly 2B otherwise. Every triple has k in {K,K+1}, c<H, exactly k actual R calls and at most Gamma actual G calls in its compiler word, and its retained g equals both the original complete terminal gcd and gcd(q(R^k(v))+c,H).

Digit correctness uses Nat.mod_pow_succ to split a prefix and its next digit. Since p^(s+1) divides H, its divisibility in gcd(n+c,H) is equivalent to the next prefix matching the center. The rank decreases on every unfinished axis; its initial value is e*(p-1)<=B. A finite induction therefore completes all axes at once. CRT injectivity reconstructs the scalar. The concrete PositiveProbeCompiler.effective_short_compiler supplies the actual word, its two action counts, and the exact full terminal reply identity for every natural source. Finally the inverse scalar rows and the residue replacement permutation recover the entry pair.

The reply-interface interpretation requires an actual cut of the same retained handle before each experiment. At that cut the current residue must equal the entry residue. Execute compile(H,k,c) in its listed chronological order, consume each fixed acknowledgement, perform one paid full current gcd read, close by positive original actions back to the required residue, and commit the local table before the next callable cut. ClosingCut states the residue and complete-reply equalities required at an experiment cut. Constructing those positive closing words, their least period, and their actual concatenated action tape is a separate obligation; the present two-stage tape is a tape of requested experiments and replies.

Same-run counting must relate each requested triple to exactly one actual read and include every closing action. In the original notation its target equalities are Q=T0+T1, NR=L_H*(K*T0+(K+1)*T1), and NG=H*sum(g_j), followed by the stated bounds Q<=2B, NR<=L_H*(2K+1)*B and NG<=2H*Gamma*B. These equalities, the integer affine endpoint and every-prefix growth bounds do not follow merely from compiler-word counts. An installed continuation must additionally preserve the immutable earned entry and a separately synchronized current residue after each action, acknowledgement and local commit. No such closing or synchronized continuation is asserted here.

**Definition 1.8 (Finite binary local control).**

$$\operatorname{binaryRounds}\left(H, answer, j, b\right) = \operatorname{iterateBinaryFullReply}\left(j, b\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.binaryRounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encode each natural local field and every complete reply with Nat.digits 2, least significant digit first; zero has the empty encoding. A finite association list has one binary triple per public prime-factor key. decodeJoint looks up that finite table. binaryShift emits the binary encoding of the bounded CRT shift; binaryAdvance decodes the full incoming reply and commits the next encoded table. binaryRounds iterates these operations by structural recursion with an explicit finite round count.

**Theorem 1.9 (The binary refinement preserves every finite execution).**

$$\forall H \in \operatorname{Nat}\left(\right), \forall answer \in \operatorname{NatToNat}\left(\right), \forall j \in \operatorname{Nat}\left(\right), \forall a \in \operatorname{Joint}\left(H\right), (\operatorname{binaryRunEncoded}\left(H, answer, j, a\right) = \operatorname{encodeNumericRun}\left(H, answer, j, a\right) \land \operatorname{decodeEncode}\left(H, a\right) = a \land \operatorname{encodedTableLength}\left(H, a\right) = \operatorname{primeFactorCount}\left(H\right) \land \operatorname{allDigitsBelowTwo}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.finite_binary_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every public H, every total scalar reply function, every finite j and every local table, binaryRounds on encoded inputs equals the encoded numeric execution, including its entire ordered shift/reply tape. Decoding an encoded table is exact, the table length is the number of prime divisors, and every encoded digit is below two. There is no positivity restriction on replies or source coordinates. The all-horizon identity applies in particular to both B-round stages with the actual compiler replies.

Nat.ofDigits_digits gives exact field and reply round trips. Finite-table lookup recovers the encoded record for each public prime key. The local binary update therefore commutes with the numeric update, and induction on j transports the entire chronological execution. This proves a finite effective representation. It supplies no numerical bit-work or bit-space bound. Factoring H, bounded shift search, binary arithmetic, word emission, tape storage, service work and backing are still charged resources under the original public finite-computation premises. Only paid reads are optimized.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.Axis`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.advance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.binaryRounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.decode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.effective_scheduler`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.finite_binary_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.rounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.schedule`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.shift`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](../GraftAffineClosure.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler](PositiveProbeCompiler.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost](../TerminalGcdAcquisitionCost.md)
