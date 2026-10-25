# Effective common-direction digit scheduling

## Abstract

A uniform digit controller combines prime-power tests into common-direction positive experiments and retains their complete scalar replies.

Fix a public natural modulus H>=1 and an arbitrary natural pair v=(a,b), including zero. The original chronological calls are R(a,b)=(b,a+b) and G(a,b)=(a+1,b); true means R in TerminalGcdAcquisitionCost.runWord. Write q(a,b)=2a+3b, K=PositiveProbeCompiler.direction(H), Gamma=PositiveProbeCompiler.graftBound(H), and B=costBound(H), the maximum of factorization(H,p)*(p-1) over the finite set primeFactors(H), with empty maximum zero. An experiment word precedes a separately paid current gcd read. The reply is the whole natural number gcd(q(current),H).

In the formulas N denotes the naturals and A(H)=ZMod(H); for positive H this is the residue ring modulo H, while A(0) is the integers. cast(H,n) is the canonical natural-number cast into A(H). PrimeIndex(H) is the subtype of natural primes in primeFactors(H); factorization(H,p) is the exponent of its underlying natural prime. Joint(H) is the function type PrimeIndex(H)->Axis. The definitions below are total for all natural parameters, without a validity condition on local records. All natural subtractions, including p-1 and the rank, truncate at zero; subtraction in a typed A(H) expression is ring subtraction. ite(P,x,y) means x if P holds and y otherwise. let binds its typed local name in the following expression; a typed mapsto expression denotes a function, and constant(X,x) is the function on X taking the value x at every argument. fst and snd are product projections. Triples associate to the right, except that an Axis triple denotes its three-field record constructor; braces in the Axis display list the typed fields of that record type. List(X) is the type of finite ordered lists of X; nil is the empty list, cons prepends, append concatenates left before right, map(f,l) applies f in list order, length counts entries, and count(w,b) counts occurrences of Boolean b in w.

**Definition 1.1 (A finite digit record).**

$$\operatorname{Axis} = \{\operatorname{level}: \mathbb{N}, \operatorname{residue}: \mathbb{N}, \operatorname{trial}: \mathbb{N}\}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.Axis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a prime power p^e, a record (s,r,d) consists of a completed digit level, its prefix residue, and the trial digit. Initially it is (0,0,0). The field functions level, residue and trial project these three natural fields; initialAxis=(0,0,0), and center(p,a)=residue(a)+p^level(a)*trial(a). The proof invariant for the unknown scalar n is s<=e, r=n mod p^s, 0<=d<p-1, and d<=floor(n/p^s) mod p. The natural rank is (e-s)*(p-1)-d.

**Definition 1.2 (Advance from the full reply).**

$$\forall p: \mathbb{N}, (\forall e: \mathbb{N}, (\forall a: \operatorname{Axis}, (\forall g: \mathbb{N}, (\operatorname{advance}\left(p, e, a, g\right) = \operatorname{ite}\left(e \le \operatorname{level}\left(a\right), a, \operatorname{ite}\left((p)^{(\operatorname{level}\left(a\right) + 1)} \mid g, ((\operatorname{level}\left(a\right) + 1), (\operatorname{residue}\left(a\right) + ((p)^{\operatorname{level}\left(a\right)} \cdot \operatorname{trial}\left(a\right))), 0), \operatorname{ite}\left((\operatorname{trial}\left(a\right) + 1) < (p - 1), (\operatorname{level}\left(a\right), \operatorname{residue}\left(a\right), (\operatorname{trial}\left(a\right) + 1)), ((\operatorname{level}\left(a\right) + 1), (\operatorname{residue}\left(a\right) + ((p)^{\operatorname{level}\left(a\right)} \cdot (p - 1))), 0)\right)\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Completed records stay fixed. Otherwise divisibility of the complete reply g by p^(s+1) accepts the center as the next prefix and resets the trial to zero. A failed test increments d when another tested digit remains. After all p-1 failures the last digit p-1 is inferred, the prefix is extended, and the trial resets. Each active update strictly decreases the rank; accepting a low trial can decrease it by more than one. No valuation or Boolean answer replaces g.

**Definition 1.3 (One computable CRT shift).**

$$\forall H: \mathbb{N}, (\forall a: \operatorname{Joint}\left(H\right), ((\forall c: \mathbb{N}, (\operatorname{Compatible}\left(H, a, c\right) \iff (\forall p: \operatorname{PrimeIndex}\left(H\right), ((p)^{\operatorname{factorization}\left(H, p\right)} \mid (\operatorname{ite}\left(\operatorname{factorization}\left(H, p\right) \le \operatorname{level}\left(\operatorname{a}\left(p\right)\right), \operatorname{residue}\left(\operatorname{a}\left(p\right)\right), (\operatorname{residue}\left(\operatorname{a}\left(p\right)\right) + ((p)^{\operatorname{level}\left(\operatorname{a}\left(p\right)\right)} \cdot \operatorname{trial}\left(\operatorname{a}\left(p\right)\right)))\right) + c)))) \land \operatorname{shift}\left(H, a\right) = \operatorname{getD}\left(\operatorname{find}\left(\operatorname{range}\left(H\right), ((c: \mathbb{N}) \mapsto \operatorname{decide}\left(\operatorname{Compatible}\left(H, a, c\right)\right))\right), 0\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.shift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each unfinished axis request the negative of its trial center modulo p^e; for a finished axis request the negative of its recovered residue. Compatible(H,a,c) means that desired(p,a)+c is divisible by p^e at every prime divisor. The algorithm searches 0,...,H-1 for the first compatible shift. The existing ZMod CRT equivalence proves that this bounded search succeeds when H>0. The equivalence is used only in the correctness proof; the computation is the finite search. In the formula range(H) is the ascending list 0,...,H-1, decide turns a decidable proposition into its Boolean truth value, find(l,f) returns the first element of l satisfying f as an option, and getD(o,z) returns that element or the default z if the option is empty. This specifies shift even at H=0. No polynomial local-work bound is attached to it.

**Definition 1.4 (Chronological full-reply execution).**

$$\forall H: \mathbb{N}, ((\forall a: \operatorname{Joint}\left(H\right), (\forall g: \mathbb{N}, (\operatorname{advanceAll}\left(H, a, g\right) = ((p: \operatorname{PrimeIndex}\left(H\right)) \mapsto \operatorname{advance}\left(p, \operatorname{factorization}\left(H, p\right), \operatorname{a}\left(p\right), g\right)))) \land \forall answer: \mathbb{N} \to \mathbb{N}, ((\forall a: \operatorname{Joint}\left(H\right), (\operatorname{rounds}\left(H, answer, 0, a\right) = (a, \operatorname{nil})) \land \forall j: \mathbb{N}, (\forall a: \operatorname{Joint}\left(H\right), (\operatorname{rounds}\left(H, answer, (j + 1), a\right) = \operatorname{let} c: \mathbb{N} := \operatorname{shift}\left(H, a\right) \operatorname{in} (\operatorname{let} g: \mathbb{N} := \operatorname{answer}\left(c\right) \operatorname{in} (\operatorname{let} t: \operatorname{Joint}\left(H\right) \times \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right) := \operatorname{rounds}\left(H, answer, j, \operatorname{advanceAll}\left(H, a, g\right)\right) \operatorname{in} ((\operatorname{fst}\left(t\right), \operatorname{cons}\left((c, g), \operatorname{snd}\left(t\right)\right)))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.rounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A round computes c from the current finite table, receives g from the reply interface, advances every axis from that same g, and records (c,g) before the recursively generated suffix. After B rounds every prime-power residue is complete. Completed axes remain valid during padding rounds. Negating a final compatible shift in ZMod H reconstructs n modulo H. Thus all axes finish with B paid scalar replies, rather than a sum of their budgets. advanceAll(H,a,g) updates each prime record with the same full reply: at p it is advance(p,factorization(H,p),a(p),g).

**Definition 1.5 (The two public directions).**

$$\forall H: \mathbb{N}, ((\forall f: \mathbb{N} \to \mathbb{N}, (\operatorname{stage}\left(H, f\right) = \operatorname{ite}\left(H = 1, (\operatorname{cast}\left(H, 0\right), \operatorname{nil}), \operatorname{let} u: \operatorname{Joint}\left(H\right) \times \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right) := \operatorname{rounds}\left(H, f, \operatorname{costBound}\left(H\right), \operatorname{constant}\left(\operatorname{PrimeIndex}\left(H\right), \operatorname{initialAxis}\right)\right) \operatorname{in} ((-\operatorname{cast}\left(H, \operatorname{shift}\left(H, \operatorname{fst}\left(u\right)\right)\right), \operatorname{snd}\left(u\right)))\right)) \land \forall answer: \mathbb{N} \to (\mathbb{N} \to \mathbb{N}), (\operatorname{schedule}\left(H, answer\right) = \operatorname{let} s: \operatorname{A}\left(H\right) \times \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right) := \operatorname{stage}\left(H, \operatorname{answer}\left(\operatorname{direction}\left(H\right)\right)\right) \operatorname{in} (\operatorname{let} t: \operatorname{A}\left(H\right) \times \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right) := \operatorname{stage}\left(H, \operatorname{answer}\left((\operatorname{direction}\left(H\right) + 1)\right)\right) \operatorname{in} (((\operatorname{fst}\left(s\right), \operatorname{fst}\left(t\right)), \operatorname{append}\left(\operatorname{map}\left(((x: \mathbb{N} \times \mathbb{N}) \mapsto (\operatorname{direction}\left(H\right), x)), \operatorname{snd}\left(s\right)\right), \operatorname{map}\left(((x: \mathbb{N} \times \mathbb{N}) \mapsto ((\operatorname{direction}\left(H\right) + 1), x)), \operatorname{snd}\left(t\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.schedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same local digit policy runs first at direction K and then at direction K+1. The output contains both recovered scalars and the chronological concatenation of triples (k,c,g). For H=1 both stages return zero with an empty tape. The controller takes only H and incoming replies; it never takes a hidden source coordinate. compiledReply(H,v,k,c) is the mathematical interpreter obtained by executing the actual compiler word at v and reading its gcd. Explicitly, terminalGcd(H,w,v)=gcd(q(runWord(w,v)),H), compiledReply(H,v,k,c)=terminalGcd(H,compile(H,k,c),v), and recover(H,a)=-cast(H,shift(H,a)). The displayed stage equation uses this last definition directly. compile is the PositiveProbeCompiler positive Boolean-word compiler; direction is its least k>=1 with fib(k+4)>=H, where fib(0)=0 and fib(1)=1, and graftBound(H)=1+floor((direction(H)+2)/2). runWord executes its list chronologically with true=R and false=G. The interpreter is not a local primitive supplied to the controller.

**Definition 1.6 (An explicit earned entry residue).**

$$\forall H: \mathbb{N}, (\forall y: \operatorname{A}\left(H\right) \times \operatorname{A}\left(H\right), (\operatorname{decode}\left(H, y\right) = \operatorname{apply}\left(\operatorname{inverse}\left((\operatorname{residueReplace}\left(H\right))^{\operatorname{direction}\left(H\right)}\right), (((5 \cdot \operatorname{fst}\left(y\right)) - (3 \cdot \operatorname{snd}\left(y\right))), ((-3 \cdot \operatorname{fst}\left(y\right)) + (2 \cdot \operatorname{snd}\left(y\right))))\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two consecutive quantity rows have matrix [[2,3],[3,5]]. Apply its integer inverse [[5,-3],[-3,2]] in ZMod H, then apply the inverse of the public residue replacement permutation to the K-th power. The resulting pair is the entry residue. This is a computation on the two earned scalars, not a hidden label. Here residueReplace(H) is the permutation of A(H) x A(H) sending (x,z) to (z,x+z), with inverse (x,z) |-> (z-x,x). Its power is composition iterated direction(H) times, and inverse denotes the inverse permutation; apply evaluates it. All coefficients in decode are cast into A(H).

**Theorem 1.7 (All natural sources and the complete reply tape).**

$$\forall H: \mathbb{N}, ((1 \le H) \implies (\forall v: \mathbb{N} \times \mathbb{N}, (\operatorname{let} T: (\operatorname{A}\left(H\right) \times \operatorname{A}\left(H\right)) \times \operatorname{List}\left(\mathbb{N} \times (\mathbb{N} \times \mathbb{N})\right) := \operatorname{schedule}\left(H, \operatorname{compiledReply}\left(H, v\right)\right) \operatorname{in} ((\operatorname{decode}\left(H, \operatorname{fst}\left(T\right)\right) = \operatorname{residueSource}\left(H, v\right) \land \operatorname{fst}\left(T\right) = (\operatorname{cast}\left(H, \operatorname{q}\left(\operatorname{iterateR}\left(\operatorname{direction}\left(H\right), v\right)\right)\right), \operatorname{cast}\left(H, \operatorname{q}\left(\operatorname{iterateR}\left((\operatorname{direction}\left(H\right) + 1), v\right)\right)\right)) \land \operatorname{length}\left(\operatorname{snd}\left(T\right)\right) = \operatorname{ite}\left(H = 1, 0, (2 \cdot \operatorname{costBound}\left(H\right))\right) \land \forall t: \mathbb{N} \times (\mathbb{N} \times \mathbb{N}), ((t \in \operatorname{snd}\left(T\right)) \implies (((\operatorname{fst}\left(t\right) = \operatorname{direction}\left(H\right) \lor \operatorname{fst}\left(t\right) = (\operatorname{direction}\left(H\right) + 1)) \land \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right) < H \land \operatorname{count}\left(\operatorname{compile}\left(H, \operatorname{fst}\left(t\right), \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)\right), \operatorname{true}\right) = \operatorname{fst}\left(t\right) \land \operatorname{count}\left(\operatorname{compile}\left(H, \operatorname{fst}\left(t\right), \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)\right), \operatorname{false}\right) \le \operatorname{graftBound}\left(H\right) \land \operatorname{snd}\left(\operatorname{snd}\left(t\right)\right) = \operatorname{gcd}\left((\operatorname{q}\left(\operatorname{iterateR}\left(\operatorname{fst}\left(t\right), v\right)\right) + \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)), H\right) \land \operatorname{snd}\left(\operatorname{snd}\left(t\right)\right) = \operatorname{terminalGcd}\left(H, \operatorname{compile}\left(H, \operatorname{fst}\left(t\right), \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)\right), v\right) \land \forall current: \mathbb{N} \times \mathbb{N}, ((\operatorname{residueSource}\left(H, current\right) = \operatorname{residueSource}\left(H, v\right)) \implies ((\operatorname{residueSource}\left(H, current\right) = \operatorname{residueSource}\left(H, v\right) \land \operatorname{terminalGcd}\left(H, \operatorname{compile}\left(H, \operatorname{fst}\left(t\right), \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)\right), current\right) = \operatorname{terminalGcd}\left(H, \operatorname{compile}\left(H, \operatorname{fst}\left(t\right), \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)\right), v\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.effective_scheduler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every H>=1 and every actual natural pair v, the decoded output is residueSource(H,v). The two scalar outputs are q(R^K(v)) and q(R^(K+1)(v)) in ZMod H. The tape has zero entries when H=1 and exactly 2B otherwise. Every triple has k in {K,K+1}, c<H, exactly k actual R calls and at most Gamma actual G calls in its compiler word, and its retained g equals both the original complete terminal gcd and gcd(q(R^k(v))+c,H). In the formula iterateR(k,v) denotes k iterations of the original R on v, and residueSource(H,v) is its coordinatewise natural cast into A(H) x A(H). The innermost conjunction expands ClosingCut(H,k,c,v,current) into its residue equality and its equality of complete terminal compiler replies.

Digit correctness uses Nat.mod_pow_succ to split a prefix and its next digit. Since p^(s+1) divides H, its divisibility in gcd(n+c,H) is equivalent to the next prefix matching the center. The rank decreases on every unfinished axis; its initial value is e*(p-1)<=B. A finite induction therefore completes all axes at once. CRT injectivity reconstructs the scalar. The concrete PositiveProbeCompiler.effective_short_compiler supplies the actual word, its two action counts, and the exact full terminal reply identity for every natural source. Finally the inverse scalar rows and the residue replacement permutation recover the entry pair.

The reply-interface interpretation requires an actual cut of the same retained handle before each experiment. At that cut the current residue must equal the entry residue. Execute compile(H,k,c) in its listed chronological order, consume each fixed acknowledgement, perform one paid full current gcd read, close by positive original actions back to the required residue, and commit the local table before the next callable cut. ClosingCut states the residue and complete-reply equalities required at an experiment cut. Constructing those positive closing words, their least period, and their actual concatenated action tape is a separate obligation; the present two-stage tape is a tape of requested experiments and replies.

Same-run counting must relate each requested triple to exactly one actual read and include every closing action. In the original notation its target equalities are Q=T0+T1, NR=L_H*(K*T0+(K+1)*T1), and NG=H*sum(g_j), followed by the stated bounds Q<=2B, NR<=L_H*(2K+1)*B and NG<=2H*Gamma*B. These equalities, the integer affine endpoint and every-prefix growth bounds do not follow merely from compiler-word counts. An installed continuation must additionally preserve the immutable earned entry and a separately synchronized current residue after each action, acknowledgement and local commit. No such closing or synchronized continuation is asserted here.

**Definition 1.8 (Finite binary local control).**

$$\forall H: \mathbb{N}, (\forall answer: \operatorname{Binary} \to \operatorname{Binary}, ((\forall b: \operatorname{BinaryJoint}\left(H\right), (\operatorname{binaryRounds}\left(H, answer, 0, b\right) = (b, \operatorname{nil})) \land \forall j: \mathbb{N}, (\forall b: \operatorname{BinaryJoint}\left(H\right), (\operatorname{binaryRounds}\left(H, answer, (j + 1), b\right) = \operatorname{let} c: \operatorname{Binary} := \operatorname{binaryShift}\left(H, b\right) \operatorname{in} (\operatorname{let} g: \operatorname{Binary} := \operatorname{answer}\left(c\right) \operatorname{in} (\operatorname{let} t: \operatorname{BinaryJoint}\left(H\right) \times \operatorname{List}\left(\operatorname{Binary} \times \operatorname{Binary}\right) := \operatorname{binaryRounds}\left(H, answer, j, \operatorname{binaryAdvance}\left(H, b, g\right)\right) \operatorname{in} ((\operatorname{fst}\left(t\right), \operatorname{cons}\left((c, g), \operatorname{snd}\left(t\right)\right))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.binaryRounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encode each natural local field and every complete reply with Nat.digits 2, least significant digit first; zero has the empty encoding. A finite association list has one binary triple per public prime-factor key. decodeJoint looks up that finite table. binaryShift emits the binary encoding of the bounded CRT shift; binaryAdvance decodes the full incoming reply and commits the next encoded table. binaryRounds iterates these operations by structural recursion with an explicit finite round count. Precisely, Binary=List(N), BinaryAxis=Binary x Binary x Binary, and BinaryJoint(H)=List(PrimeIndex(H) x BinaryAxis). digits(n)=Nat.digits(2,n) and ofDigits(c)=Nat.ofDigits(2,c); the latter is the sum of c[i]*2^i over list positions, including lists with digits above one. encodeAxis(a) applies digits to level(a), residue(a), trial(a); decodeAxis applies ofDigits to the three fields. encodeJoint(H,a) is the ascending list of all public prime keys paired with encodeAxis(a(p)). decodeJoint(H,b)(p) decodes the first record with key p in b, using (nil,nil,nil) when p is absent. Thus arbitrary binary tables, not only encoded valid histories, have a defined meaning. binaryShift(H,b)=digits(shift(H,decodeJoint(H,b))) and binaryAdvance(H,b,g)=encodeJoint(H,advanceAll(H,decodeJoint(H,b), ofDigits(g))). card(primeFactors(H)) counts distinct prime keys.

**Theorem 1.9 (The binary refinement preserves every finite execution).**

$$\forall H: \mathbb{N}, (\forall answer: \mathbb{N} \to \mathbb{N}, (\forall j: \mathbb{N}, (\forall a: \operatorname{Joint}\left(H\right), ((\operatorname{binaryRounds}\left(H, ((c: \operatorname{Binary}) \mapsto \operatorname{digits}\left(\operatorname{answer}\left(\operatorname{ofDigits}\left(c\right)\right)\right)), j, \operatorname{encodeJoint}\left(H, a\right)\right) = (\operatorname{encodeJoint}\left(H, \operatorname{fst}\left(\operatorname{rounds}\left(H, answer, j, a\right)\right)\right), \operatorname{map}\left(((t: \mathbb{N} \times \mathbb{N}) \mapsto (\operatorname{digits}\left(\operatorname{fst}\left(t\right)\right), \operatorname{digits}\left(\operatorname{snd}\left(t\right)\right))), \operatorname{snd}\left(\operatorname{rounds}\left(H, answer, j, a\right)\right)\right)) \land \operatorname{decodeJoint}\left(H, \operatorname{encodeJoint}\left(H, a\right)\right) = a \land \operatorname{length}\left(\operatorname{encodeJoint}\left(H, a\right)\right) = \operatorname{card}\left(\operatorname{primeFactors}\left(H\right)\right) \land \forall n: \mathbb{N}, (\forall d: \mathbb{N}, ((d \in \operatorname{digits}\left(n\right)) \implies (d < 2))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.finite_binary_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural public H, including H=0, every total scalar reply function, every finite j and every local table, binaryRounds on encoded inputs equals the encoded numeric execution, including its entire ordered shift/reply tape. Decoding an encoded table is exact, the table length is the number of prime divisors, and every encoded digit is below two. There is no positivity restriction on replies or source coordinates. The all-horizon identity applies in particular to both B-round stages with the actual compiler replies.

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
