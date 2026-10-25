# Returned arithmetic behavior and serial continued use

## Abstract

Paid positive closing earns an immutable entry and a synchronized callable current state on the retained source binding.

Fix H>=1. Sources are all natural pairs, including zero; true denotes the original R(a,b)=(b,a+b), and false denotes G(a,b)=(a+1,b). The only informative source call is the paid nondestructive complete reply gcd(2a+3b,H). The local acquisition program is exactly PositiveClosingExecution.controller(H). It receives H and its acquired replies; neither the source projection nor service tariffs enter its code. Its actual action word w and event tape es are executionWord(H,v) and executionEvents(H,v), for the semantic entry v.

A supplied SourceService(T,X) has an arbitrary handle type T and backend-state type X. Its value(h,x) is a semantic projection to the actual natural pair at h, not a controller port. lawful(h,x) records the supplied lawful authority and adequate provision. The relations action(h,b,x,y) and read(h,H,x,g,y) describe successful completed calls. For lawful x, an action has value(h,y)=step(b,value(h,x)) and preserves lawfulness. A read preserves that value and lawfulness and has g=gcd(q(value(h,x)),H). Calls can change backend bookkeeping or finite allocations without adding a numeric reply.

Completion(B,h,H) is the supplied premise at the fixed public modulus H that every admitted next action and read on a lawful state completes: for each b,x there is a y with action(h,b,x,y), and for each lawful x there are g,y with read(h,H,x,g,y). No read at a different modulus, including zero, is required. This models retained rights, service completion and adequate backing under exclusive serial use. It is not constructed from a residue, finite program or source size. Dynamically provisioned finite states are allowed; no fixed finite capacity for all entries or all future lengths is asserted. A concrete backend must justify these premises for its chosen finite run. Unreported writers, revoked rights and incomplete commits fall outside this service contract.

ServiceRun uses this very B and h in every action and read constructor. Its local transitions are the original controller's compute, action, full-reply and halt instructions. Action completion returns only its fixed acknowledgement; only the full paid gcd enters a read continuation. There is no allocation, replacement handle, clone, reset or source-inverse instruction. Induction through the actual positive-closing Run constructs a ServiceRun with the identical event tape and earned output. Every completed backend run has this same tape, output, local terminal state, arithmetic endpoint and bill; backend bookkeeping may differ. Its source projection has the identical integer endpoint. This correspondence is proved from individual supplied service effects and completion, not assumed as a simulation law.

Tariffs has three external natural-valued functions on actual pre-call pairs: read, replacement and graft. serviceBill(p,[],v)=0; a compute event contributes nothing; an action b contributes its corresponding tariff at v and continues at step(b,v); a reply contributes the read tariff at v and continues at v. ServiceRun's work index adds precisely these amounts at its actual backend states. Thus serviceBill is the same-run sum over paid reads, R and G calls, including all closing letters. Its work index is never supplied to code or used to select an action.

**Definition 1.1 (The installed local residue update).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall b \in \operatorname{Bool}\left(\right), (\forall c \in \operatorname{ResiduePair}\left(H\right), \operatorname{update}\left(H, b, c\right) = \operatorname{ite}\left(b, \operatorname{R}\left(c\right), \operatorname{addAlpha}\left(c\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.update` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R(c)=(c.second,c.first+c.second), and addAlpha(c)=c+(1,0), in (ZMod H) squared. These are the supplied GraftAffineClosure autonomous updates, with the original alpha graft.

**Definition 1.2 (Finite hypothetical evaluation).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall c \in \operatorname{ResiduePair}\left(H\right), (\forall V \in \operatorname{ListBool}\left(\right), \operatorname{scratch}\left(H, c, V\right) = \operatorname{graftRun}\left(\operatorname{alpha}\left(\right), \operatorname{mapNot}\left(V\right), c\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.scratch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

graftRun is GraftAffineClosure.run with graft vector (1,0). Its Boolean convention is opposite to the original runWord, so mapNot complements every letter. Evaluation uses only the retained current pair and the supplied finite word. It changes no source.

**Definition 1.3 (Current output and future prediction).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall c \in \operatorname{ResiduePair}\left(H\right), (\forall V \in \operatorname{ListBool}\left(\right), \operatorname{predict}\left(H, c, V\right) = \operatorname{residueReadout}\left(H, \operatorname{scratch}\left(H, c, V\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.predict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

residueReadout(H,z)=gcd((2z.first+3z.second).val,H). The existing representative-independent decoder gives the actual current gcd when c is synchronized. The empty word is current output; applying this finite computation to every requested prefix gives prefix predictions. A hypothetical result is a prediction from acquired memory, not an additional observation.

Memory(H) has distinct entry and current residue fields and a phase. A Frame contains this local memory and one backend state. The four phases are ready, requested(b), completed(b) and acknowledged(b). Only ready exposes the callable reader or predictor. MicroStep first records request(b), leaving the backend and registers unchanged. Its completion step invokes the actual action(B,h,b) and changes only the backend and phase. The acknowledgement event is the same constant event for either action and every source; it changes only the phase. Finally commit replaces current by update(H,b,current) and returns to ready. Every constructor preserves entry. No read, rebind or source allocation is present in this continuation protocol.

**Definition 1.4 (The actual four-stage word protocol).**

$$(\forall V \in \operatorname{ListBool}\left(\right), \operatorname{continuationEvents}\left(V\right) = \operatorname{flatMapTransactions}\left(V\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.continuationEvents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

flatMapTransactions replaces each chronological letter b with the exact four events request(b), complete, acknowledge, commit. ProtocolRun is the empty execution or a MicroStep followed by a ProtocolRun. Hence an arbitrary protocol prefix may stop with a request pending or after completion, but exposes no new callable cut before commit.

**Definition 1.5 (The pending-action invariant).**

$$(\forall T \in \operatorname{Type}\left(\right), (\forall X \in \operatorname{Type}\left(\right), (\forall B \in \operatorname{SourceService}\left(T, X\right), (\forall h \in T, (\forall H \in \operatorname{Nat}\left(\right), (\forall f \in \operatorname{Frame}\left(X, H\right), \operatorname{Aligned}\left(B, h, H, f\right) = ((\operatorname{lawful}\left(B, h, \operatorname{world}\left(f\right)\right)) \land (\operatorname{pendingAgreement}\left(B, h, H, f\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.Aligned` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pendingAgreement means current=res(H,value(h,world)) in ready or requested(b), and update(H,b,current)=res(H,value(h,world)) in completed(b) or acknowledged(b). Each microstep preserves this invariant and entry. In particular the source may have advanced while the old local register is still stored, but this intermediate state is not callable. Every subsequent ready state has the committed correct current register.

**Theorem 1.6 (The earned return supports all finite continuations at the read optimum).**

$$(\forall T \in \operatorname{Type}\left(\right), (\forall X \in \operatorname{Type}\left(\right), (\forall H \in \operatorname{Nat}\left(\right), ((1 \le H) \implies ((\forall B \in \operatorname{SourceService}\left(T, X\right), (\forall h \in T, ((\operatorname{Completion}\left(B, h, H\right)) \implies ((\forall p \in \operatorname{Tariffs}\left(\right), (\forall x \in X, ((\operatorname{lawful}\left(B, h, x\right)) \implies ((\exists t \in \operatorname{AcquisitionPhase}\left(H\right), (\exists y \in X, ((\operatorname{ServiceRun}\left(B, h, p, \operatorname{P}\left(H\right), H, \operatorname{initial}\left(\operatorname{P}\left(H\right)\right), x, \operatorname{executionEvents}\left(H, \operatorname{value}\left(B, h, x\right)\right), t, y, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{serviceBill}\left(p, \operatorname{executionEvents}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{value}\left(B, h, x\right)\right)\right)) \land (\operatorname{value}\left(B, h, y\right) = \operatorname{runWord}\left(\operatorname{executionWord}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{value}\left(B, h, x\right)\right)) \land (\operatorname{lawful}\left(B, h, y\right)) \land (\operatorname{paidReads}\left(\operatorname{executionEvents}\left(H, \operatorname{value}\left(B, h, x\right)\right)\right) = \operatorname{ite}\left(H = 1, 0, \operatorname{twice}\left(\operatorname{costBound}\left(H\right)\right)\right)) \land (((H = 1) \implies (y = x))) \land ((\forall S \in \operatorname{Type}\left(\right), (\forall P \in \operatorname{Controller}\left(S, \operatorname{ResiduePair}\left(H\right)\right), (\forall J \in \operatorname{Nat}\left(\right), (((\forall z \in \operatorname{NatPair}\left(\right), (\exists r \in \operatorname{ListEvent}\left(\right), (\exists s \in S, (\exists u \in \operatorname{NatPair}\left(\right), ((\operatorname{Run}\left(P, H, \operatorname{initial}\left(P\right), z, r, s, u, \operatorname{res}\left(H, z\right)\right)) \land (\operatorname{paidReads}\left(r\right) \le J))))))) \implies (\operatorname{paidReads}\left(\operatorname{executionEvents}\left(H, \operatorname{value}\left(B, h, x\right)\right)\right) \le J)))))) \land (\operatorname{Continued}\left(B, h, H, \operatorname{value}\left(B, h, x\right), \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), y\right)) \land ((\forall rs \in \operatorname{ListEvent}\left(\right), (\forall t2 \in \operatorname{AcquisitionPhase}\left(H\right), (\forall y2 \in X, (\forall l2 \in \operatorname{ResiduePair}\left(H\right), (\forall n2 \in \operatorname{Nat}\left(\right), ((\operatorname{ServiceRun}\left(B, h, p, \operatorname{P}\left(H\right), H, \operatorname{initial}\left(\operatorname{P}\left(H\right)\right), x, rs, t2, y2, l2, n2\right)) \implies (((rs = \operatorname{executionEvents}\left(H, \operatorname{value}\left(B, h, x\right)\right)) \land (t2 = t) \land (l2 = \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right)) \land (\operatorname{value}\left(B, h, y2\right) = \operatorname{runWord}\left(\operatorname{executionWord}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{value}\left(B, h, x\right)\right)) \land (\operatorname{lawful}\left(B, h, y2\right)) \land (n2 = \operatorname{serviceBill}\left(p, \operatorname{executionEvents}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{value}\left(B, h, x\right)\right)) \land (((H = 1) \implies (y2 = x))) \land (\operatorname{Continued}\left(B, h, H, \operatorname{value}\left(B, h, x\right), \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), y2\right)))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.same_handle_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed statement v=value(B,h,x), w=executionWord(H,v), es=executionEvents(H,v), e=res(H,v), Q=paidReads(es), and readyFrame(y,e,c) has backend y, immutable entry e, separate current c and phase ready. P(H) is the original positive-closing controller. ServiceRun is indexed by its controller, modulus, initial local/backend states, exact event tape, terminal local/backend states, earned output and external work. ProtocolRun uses the same B,h,H. All displayed conjunctions and implications retain their indicated scopes.

### The complete continuation contract at each backend endpoint

For the same fixed T,X,H,B,h,x and the abbreviations v,e above, let a be any backend endpoint in X. Continued(B,h,H,v,e,a) means exactly the conjunction of the following five formulas, in order. The theorem asserts this entire conjunction at y and at every admitted completed acquisition endpoint y2. The formulas share these fixed parameters; each displayed quantifier and implication keeps its full scope. This is the existing Lean definition Continued with start=readyFrame(a,e,e).

The installed returned cut is aligned:

$$
\operatorname{Aligned}\left(B, h, H, \operatorname{readyFrame}\left(a, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right)\right)\right)
$$

Every actual finite protocol prefix preserves entry and alignment; each reachable ready frame has its synchronized reader and every further finite execution:

$$
(\forall r \in \operatorname{ListSignal}\left(\right), (\forall f \in \operatorname{Frame}\left(X, H\right), ((\operatorname{ProtocolRun}\left(B, h, H, \operatorname{readyFrame}\left(a, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right)\right), r, f\right)) \implies (((\operatorname{entry}\left(\operatorname{memory}\left(f\right)\right) = \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right)) \land (\operatorname{Aligned}\left(B, h, H, f\right)) \land (((\operatorname{phase}\left(\operatorname{memory}\left(f\right)\right) = \operatorname{ready}\left(\right)) \implies (((\operatorname{current}\left(\operatorname{memory}\left(f\right)\right) = \operatorname{res}\left(H, \operatorname{value}\left(B, h, \operatorname{world}\left(f\right)\right)\right)) \land ((\forall W \in \operatorname{ListBool}\left(\right), \operatorname{predict}\left(H, \operatorname{current}\left(\operatorname{memory}\left(f\right)\right), W\right) = \operatorname{terminalGcd}\left(H, W, \operatorname{value}\left(B, h, \operatorname{world}\left(f\right)\right)\right))) \land ((\forall V \in \operatorname{ListBool}\left(\right), (\exists z \in X, ((\operatorname{ProtocolRun}\left(B, h, H, f, \operatorname{continuationEvents}\left(V\right), \operatorname{readyFrame}\left(z, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{scratch}\left(H, \operatorname{current}\left(\operatorname{memory}\left(f\right)\right), V\right)\right)\right)) \land (\operatorname{value}\left(B, h, z\right) = \operatorname{runWord}\left(V, \operatorname{value}\left(B, h, \operatorname{world}\left(f\right)\right)\right)) \land (\operatorname{scratch}\left(H, \operatorname{current}\left(\operatorname{memory}\left(f\right)\right), V\right) = \operatorname{res}\left(H, \operatorname{value}\left(B, h, z\right)\right)) \land ((\forall W \in \operatorname{ListBool}\left(\right), \operatorname{predict}\left(H, \operatorname{scratch}\left(H, \operatorname{current}\left(\operatorname{memory}\left(f\right)\right), V\right), W\right) = \operatorname{terminalGcd}\left(H, \operatorname{append}\left(V, W\right), \operatorname{value}\left(B, h, \operatorname{world}\left(f\right)\right)\right))))))))))))))))
$$

Every finite original word has a completed actual execution from the returned cut, with its exact source endpoint, synchronized current and all later predictions:

$$
(\forall V \in \operatorname{ListBool}\left(\right), (\exists z \in X, ((\operatorname{ProtocolRun}\left(B, h, H, \operatorname{readyFrame}\left(a, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right)\right), \operatorname{continuationEvents}\left(V\right), \operatorname{readyFrame}\left(z, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{scratch}\left(H, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), V\right)\right)\right)) \land (\operatorname{value}\left(B, h, z\right) = \operatorname{runWord}\left(V, \operatorname{value}\left(B, h, a\right)\right)) \land (\operatorname{scratch}\left(H, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), V\right) = \operatorname{res}\left(H, \operatorname{value}\left(B, h, z\right)\right)) \land ((\forall W \in \operatorname{ListBool}\left(\right), \operatorname{predict}\left(H, \operatorname{scratch}\left(H, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), V\right), W\right) = \operatorname{terminalGcd}\left(H, \operatorname{append}\left(V, W\right), \operatorname{value}\left(B, h, x\right)\right))))))
$$

Every completed actual execution of such a word has the displayed ready phase, current, arithmetic endpoint and all later predictions:

$$
(\forall V \in \operatorname{ListBool}\left(\right), (\forall f \in \operatorname{Frame}\left(X, H\right), ((\operatorname{ProtocolRun}\left(B, h, H, \operatorname{readyFrame}\left(a, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right)\right), \operatorname{continuationEvents}\left(V\right), f\right)) \implies (((\operatorname{phase}\left(\operatorname{memory}\left(f\right)\right) = \operatorname{ready}\left(\right)) \land (\operatorname{current}\left(\operatorname{memory}\left(f\right)\right) = \operatorname{scratch}\left(H, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), V\right)) \land (\operatorname{value}\left(B, h, \operatorname{world}\left(f\right)\right) = \operatorname{runWord}\left(V, \operatorname{value}\left(B, h, a\right)\right)) \land ((\forall W \in \operatorname{ListBool}\left(\right), \operatorname{predict}\left(H, \operatorname{current}\left(\operatorname{memory}\left(f\right)\right), W\right) = \operatorname{terminalGcd}\left(H, \operatorname{append}\left(V, W\right), \operatorname{value}\left(B, h, x\right)\right))))))))
$$

Every finite future prediction at the returned cut agrees with both the actual returned source and the entry source, including the empty word:

$$
(\forall W \in \operatorname{ListBool}\left(\right), ((\operatorname{predict}\left(H, \operatorname{res}\left(H, \operatorname{value}\left(B, h, x\right)\right), W\right) = \operatorname{terminalGcd}\left(H, W, \operatorname{value}\left(B, h, a\right)\right)) \land (\operatorname{terminalGcd}\left(H, W, \operatorname{value}\left(B, h, a\right)\right) = \operatorname{terminalGcd}\left(H, W, \operatorname{value}\left(B, h, x\right)\right))))
$$

The same result holds for every admitted completed acquisition outcome: any ServiceRun from the given actual x has es as its tape, t as its final local state, e as its earned output, the same arithmetic endpoint and exact serviceBill, and lawful retained authority, with y=x for every outcome at H=1. Continued(B,h,H,v,e,y) names exactly the displayed alignment, all-prefix/callable-cut, finite-word execution and prediction clauses. It is proved for each such backend endpoint y, including outcomes that differ in allocation or bookkeeping. No deterministic-backend choice is required.

The acquisition output e is actually produced by P(H); it is not installed from a hidden source projection. The supplied D execution restores the entry residue after its last positive closing block. Storing its earned output in two separate fields therefore gives current=res(H,value(h,y)) as well as entry=res(H,v). The supplied whole-word residue transport and decoder prove predict(H,e,W)=terminalGcd(H,W,value(h,y))=terminalGcd(H,W,v) for every W. This returns the callable original R/G behavior, including the empty word, rather than just one reply or a fresh simulated source.

Induction on MicroStep and ProtocolRun proves entry immutability and the pending-action invariant for every actual finite protocol prefix. At every ready state, all finite predictions agree with continuations of that very actual current source. A second induction constructs a completed protocol for every finite original word V using the actual service at h and only local updates. Every completed actual execution has endpoint V(value(h,y)) and current scratch(H,e,V); each later prediction W equals the entry behavior on V appended to W. The same two inductions apply again at any reachable ready frame. Every actual source letter is paid; the continuation contains no further paid read. All finite choices and externally supplied adaptive word sequences are covered by their actual finite prefixes under the same completion premises.

Q is zero at H=1 and 2B(H) otherwise. Here B(H) is the existing maximum of h(p-1) for p^h exactly dividing H. The universal lower-bound clause directly uses ContinuousAcquisitionTransport.continuous_acquisition_lower_bound. S is arbitrary local configuration space in Type u for any universe u; the successful competitor may use arbitrary finite adaptive source words and local work and actions after its final read. Only its per-entry termination and common finite worst read budget are required. Entry identification already forces Q<=J, hence the same-handle service attains the original read minimum. At H=1 its event tape is empty and y=x, including backend identity. At every H all zero coordinates remain in the source domain.

The spatial field at a ready cut is this same current c. Its first two prospective replacement quantities are C*c=(2*c.first+3*c.second, 3*c.first+5*c.second), and further quantities follow the supplied Fibonacci step. GraftAffineClosure.result gives observe(R(v))=R(observe(v)), the progression identity, and the inverse (x,y) maps to (5*x-3*y,-3*x+2*y). The full original-alpha behavior quotient identifies precisely this residue pair. These existing correspondences are applied to the acquired synchronized c; they share the same actual cut and do not acquire a second label. Prospective replacement quantities describe arithmetic evolution, not elapsed time or a clock.

For this identical acquisition word and tape, PositiveClosingExecution also supplies the least 1<=L<=H^4, M^L=I, Q=T0+T1, NR=L*(K*T0+(K+1)*T1), NG=H*J, NR<=L*(2K+1)*B and NG<=2H*Gamma*B. Its exact endpoint is R iterated NR times on v plus the sum of R iterated r times on alpha for every graft's number r of strictly later replacements, with multiplicity. Every actual prefix quantity is bounded by the endpoint, which is at most 2^NR*(q(v)+2NG). The service lift preserves that endpoint, every complete reply and every closing letter; none of these accounts comes from a separately optimized run.

The numerical workspace O(A+Q*b+b^2) and local-work O(H^4*b^3+(A+Q+1)*b^5), with A=NR+NG and b=ceil(log2(H+1)), remain unproved for this implementation. The actual scheduler uses List.range(H) for public shift search. Its binary refinement proves finite representations and exact decisions, not these bounds. A sequential binary implementation, its finite CRT/prime/Fibonacci tables and short buffer, and a proved cost/space simulation of order search, test selection, compilation, closing, tape writes and decoding are still required under the original bit model. The service sum does not replace these local resource obligations.

Add actual local bit work, public input/output and fixed-acknowledgement handling, installation of code/data and service blocks, authentic binding and rights, backing provision, source storage/retention and retained records. A global replacement is not one local rewrite or bit operation. Each chosen finite continuation adds its own R/G calls, service tariffs, local input/update/output work and any retained future data; hypothetical evaluation adds local work and no source call. No acquisition bound covers an unbounded future tape. Realizing the current gcd port and these supplied services/rights on a narrower Native, LAB or physical backend remains separate. Arithmetic return recovers neither exact integer source, syntax, chronology, elapsed time nor whole-memory installation. No total-resource optimum or physical inverse is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.Aligned`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.continuationEvents`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.predict`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.same_handle_return`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.scratch`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.update`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport](ContinuousAcquisitionTransport.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution](PositiveClosingExecution.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](../GraftAffineClosure.md)
