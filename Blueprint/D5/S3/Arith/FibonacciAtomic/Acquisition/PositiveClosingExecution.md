# One chronological acquisition trajectory

## Abstract

Positive reverse closing implements the common-direction policy on one continuous natural-pair source.

The source is any v=(a,b) in Nat squared, including zero. Its original operations are R(a,b)=(b,a+b) and G(a,b)=(a+1,b). A chronological Boolean word uses true for R and false for G. Run(w,v) is the original runWord, q(a,b)=2a+3b, and res(H,v) is coordinatewise reduction in (ZMod H) squared. The only informative source event is a paid nondestructive full reply gcd(q u,H); action events consume their fixed completion acknowledgement. All actions operate on the same source thread in ContinuousAcquisitionTransport.Run.

**Definition 1.1 (The public matrix).**

$$(\forall H \in \operatorname{Nat}\left(\right), \operatorname{M}\left(H\right) = \operatorname{matrixTwo}\left(0, 1, 1, 1\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.matrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M(H) is the matrix with rows (0,1) and (1,1) over ZMod H. Its inverse has rows (-1,1) and (1,0), including the singleton ring when H=1.

**Definition 1.2 (An effective least matrix period).**

$$(\forall H \in \operatorname{Nat}\left(\right), \operatorname{L}\left(H\right) = \operatorname{ite}\left(H = 0, 1, \operatorname{min}\left(\operatorname{positiveMatrixPeriods}\left(H\right)\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.period` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(H)=period(H) is the least positive k with M(H)^k=I for H>0; L(0)=1 is an unused public convention. The search is Nat.find with a decidable matrix equality. The matrix is a unit. Its finite order is bounded by the number of matrix units, which inject into the H^4 matrices. This proves termination with 1<=L(H)<=H^4, rather than using a factorial-sized closing word. No source query occurs in this public computation.

**Definition 1.3 (Chronological positive closing).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall w \in \operatorname{ListBool}\left(\right), \operatorname{close}\left(H, w\right) = \operatorname{flatMap}\left(\operatorname{closeLetter}\left(H\right), \operatorname{reverse}\left(w\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.closing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

closeLetter(H,true) is L(H)-1 individual R calls; closeLetter(H,false) is H-1 individual G calls. Subtraction is truncated in these total definitions. For H>=1 the exponents are the required nonnegative integers. The closing list reverses the original letters before expanding them. Thus it cancels the most recent residue action first. It is a list of positive original actions, with no inverse-action service.

**Definition 1.4 (A source-blind public controller).**

$$(\forall H \in \operatorname{Nat}\left(\right), \operatorname{P}\left(H\right) = \operatorname{Controller}\left(\operatorname{code}\left(H\right), \operatorname{initial}\left(H\right), \operatorname{zeroPair}\left(\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.controller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Phase(H) has four constructors: stage(s,j,a,y), forward(todo,w,s,j,a,y), reading(w,s,j,a,y), and close(todo,s,j,a,y). Here s is Boolean, j is a natural counter, a:Joint(H) is the scheduler's public prime-axis record, y:ZMod H is the first acquired scalar, and todo,w are finite Boolean words. None contains a source coordinate. The direction is K(H) when s=false and K(H)+1 when s=true, where K is the existing least positive Fibonacci compiler direction. Gamma(H)=graftBound(H) is 1+floor((K(H)+2)/2); B(H)=costBound(H) is the maximum of factorization(H,p)*(p-1) over the prime divisors p of H.

At a nonzero stage counter the code computes c=shift(H,a) and w=compile(H,k,c), then enters forward. Each nonempty forward list emits its next original action. Its empty list enters reading. Reading makes exactly one current gcd call, retains that full reply g in the event tape, and enters close(close(H,w),s,j,advanceAll(H,a,g),y). Every closing action is completed before the empty closing list commits the next stage cut. A completed first stage computes its recover value and starts the second stage. A completed second stage halts with decode(H,(y,recover(H,a))). For H>1 initialization is stage(false,B(H),initialAxis,0). For H=1 it is stage(true,0,initialAxis,0), so no source call is made. The fallback is the zero residue pair.

**Theorem 1.5 (Whole-word residue transport).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall w \in \operatorname{ListBool}\left(\right), (\forall v \in \operatorname{NatPair}\left(\right), \operatorname{res}\left(H, \operatorname{Run}\left(w, v\right)\right) = \operatorname{graftRun}\left(\operatorname{alpha}\left(\right), \operatorname{mapNot}\left(w\right), \operatorname{res}\left(H, v\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.residue_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

graftRun is GraftAffineClosure.run with alpha=(1,0). Its Boolean convention is false for replacement and true for graft, so mapNot complements the original chronological word. The equality holds for every natural H and every natural pair, without a positive-modulus premise. It transports the actual original word to its residue action; the installed scratch predictor uses this same transport at every synchronized current cut.

**Definition 1.6 (The action word of this same run).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall v \in \operatorname{NatPair}\left(\right), \operatorname{A}\left(H, v\right) = \operatorname{ite}\left(H = 1, \operatorname{nil}\left(\right), \operatorname{append}\left(\operatorname{actions}\left(H, \operatorname{K}\left(H\right), \operatorname{tape}\left(H, v, \operatorname{false}\left(\right)\right)\right), \operatorname{actions}\left(H, (\operatorname{K}\left(H\right)+1), \operatorname{tape}\left(H, v, \operatorname{true}\left(\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.executionWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

stageData(H,v,s) is the existing rounds(H,compiledReply(H,v,k),B(H),initialAxis), with k the public stage direction; tape(H,v,s) is its second component. These are mathematical descriptions of a run, not inputs of code. actions(H,k,tape) concatenates compile(H,k,c) followed by its positive closing list for each tape record (c,g), in order. A(H,v)=executionWord(H,v).

**Definition 1.7 (The actual full-reply tape).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall v \in \operatorname{NatPair}\left(\right), \operatorname{E}\left(H, v\right) = \operatorname{ite}\left(H = 1, \operatorname{nil}\left(\right), \operatorname{stageEventJoin}\left(H, v\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.executionEvents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E(H,v)=executionEvents(H,v) concatenates the two stage tapes with the one intervening compute event. Each test contributes: one compute, all forward action events, one compute, one full reply g, every closing action event, and one compute. stageEventJoin denotes exactly this concatenation of events(H,K,tape(H,v,false)), the intervening compute, and events(H,K+1,tape(H,v,true)). Thus no closing call is omitted and no cached answer is moved across an action.

**Definition 1.8 (Per-stage actual read counts).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall v \in \operatorname{NatPair}\left(\right), (\forall s \in \operatorname{Bool}\left(\right), \operatorname{T}\left(H, v, s\right) = \operatorname{ite}\left(H = 1, 0, \operatorname{length}\left(\operatorname{tape}\left(H, v, s\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.tests` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(H,v,s) is zero for H=1 and the length of that actual stage's tape otherwise. Write T0=T(H,v,false), T1=T(H,v,true). Each equals B(H) for H>1.

**Definition 1.9 (Forward graft counts, one per paid test).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall v \in \operatorname{NatPair}\left(\right), \operatorname{J}\left(H, v\right) = \operatorname{sumForwardGrafts}\left(H, v\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.graftSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J(H,v)=graftSum(H,v) sums countG(compile(H,k,c)) over the actual triples (k,c,g) of schedule(H,compiledReply(H,v)). It is the sum of the individual g_j in the source statement; it does not include closing grafts, which multiply this total by H.

**Definition 1.10 (Suffix replacement indices).**

$$((\operatorname{suffixes}\left(\operatorname{nil}\left(\right)\right) = \operatorname{nil}\left(\right)) \land ((\forall w \in \operatorname{ListBool}\left(\right), \operatorname{suffixes}\left(\operatorname{consR}\left(w\right)\right) = \operatorname{suffixes}\left(w\right))) \land ((\forall w \in \operatorname{ListBool}\left(\right), \operatorname{suffixes}\left(\operatorname{consG}\left(w\right)\right) = \operatorname{cons}\left(\operatorname{countR}\left(w\right), \operatorname{suffixes}\left(w\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.graftSuffixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

suffixes(w)=graftSuffixes(w) lists, in graft occurrence order, the number of R letters strictly after that graft in w. R at the front adds no graft index; G at the front contributes countR of its tail. suffixAffineSum(w) is the sum, for r in suffixes(w) with multiplicity, of iterateR(r,(1,0)); iterateR(r,x) is R iterated r times on x. The affine sum therefore follows each actual graft through precisely its later replacements, including those in positive closing lists.

**Theorem 1.11 (Operational execution, exact counts and every-prefix growth).**

$$(\forall H \in \operatorname{Nat}\left(\right), ((1 \le H) \implies ((\forall v \in \operatorname{NatPair}\left(\right), (((\exists t \in \operatorname{Phase}\left(H\right), \operatorname{OperationalRun}\left(\operatorname{P}\left(H\right), H, \operatorname{initial}\left(H\right), v, \operatorname{E}\left(H, v\right), t, \operatorname{Run}\left(\operatorname{A}\left(H, v\right), v\right), \operatorname{res}\left(H, v\right)\right))) \land (\operatorname{finalWord}\left(\operatorname{nil}\left(\right), \operatorname{E}\left(H, v\right)\right) = \operatorname{A}\left(H, v\right)) \land (\operatorname{res}\left(H, \operatorname{Run}\left(\operatorname{A}\left(H, v\right), v\right)\right) = \operatorname{res}\left(H, v\right)) \land (1 \le \operatorname{L}\left(H\right)) \land (\operatorname{L}\left(H\right) \le \operatorname{power}\left(H, 4\right)) \land (\operatorname{matrixPower}\left(H, \operatorname{L}\left(H\right)\right) = \operatorname{identity}\left(\right)) \land ((\forall k \in \operatorname{Nat}\left(\right), ((((1 \le k) \land (\operatorname{matrixPower}\left(H, k\right) = \operatorname{identity}\left(\right)))) \implies (\operatorname{L}\left(H\right) \le k)))) \land (\operatorname{paidReads}\left(\operatorname{E}\left(H, v\right)\right) = (\operatorname{T}\left(H, v, \operatorname{false}\left(\right)\right)+\operatorname{T}\left(H, v, \operatorname{true}\left(\right)\right))) \land (\operatorname{paidReads}\left(\operatorname{E}\left(H, v\right)\right) = \operatorname{ite}\left(H = 1, 0, (2 \cdot \operatorname{B}\left(H\right))\right)) \land (\operatorname{countR}\left(\operatorname{A}\left(H, v\right)\right) = (\operatorname{L}\left(H\right) \cdot ((\operatorname{K}\left(H\right) \cdot \operatorname{T}\left(H, v, \operatorname{false}\left(\right)\right))+((\operatorname{K}\left(H\right)+1) \cdot \operatorname{T}\left(H, v, \operatorname{true}\left(\right)\right))))) \land (\operatorname{countG}\left(\operatorname{A}\left(H, v\right)\right) = (H \cdot \operatorname{J}\left(H, v\right))) \land (\operatorname{countR}\left(\operatorname{A}\left(H, v\right)\right) \le ((\operatorname{L}\left(H\right) \cdot ((2 \cdot \operatorname{K}\left(H\right))+1)) \cdot \operatorname{B}\left(H\right))) \land (\operatorname{countG}\left(\operatorname{A}\left(H, v\right)\right) \le (((2 \cdot H) \cdot \operatorname{Gamma}\left(H\right)) \cdot \operatorname{B}\left(H\right))) \land (\operatorname{length}\left(\operatorname{suffixes}\left(\operatorname{A}\left(H, v\right)\right)\right) = \operatorname{countG}\left(\operatorname{A}\left(H, v\right)\right)) \land (\operatorname{Run}\left(\operatorname{A}\left(H, v\right), v\right) = (\operatorname{iterateR}\left(\operatorname{countR}\left(\operatorname{A}\left(H, v\right)\right), v\right)+\operatorname{suffixAffineSum}\left(\operatorname{A}\left(H, v\right)\right))) \land ((\forall p \in \operatorname{ListBool}\left(\right), (\forall z \in \operatorname{ListBool}\left(\right), ((\operatorname{A}\left(H, v\right) = \operatorname{append}\left(p, z\right)) \implies (\operatorname{q}\left(\operatorname{Run}\left(p, v\right)\right) \le \operatorname{q}\left(\operatorname{Run}\left(\operatorname{A}\left(H, v\right), v\right)\right)))))) \land (\operatorname{q}\left(\operatorname{Run}\left(\operatorname{A}\left(H, v\right), v\right)\right) \le (\operatorname{power}\left(2, \operatorname{countR}\left(\operatorname{A}\left(H, v\right)\right)\right) \cdot (\operatorname{q}\left(v\right)+(2 \cdot \operatorname{countG}\left(\operatorname{A}\left(H, v\right)\right))))) \land (((H = 1) \implies (((\operatorname{A}\left(H, v\right) = \operatorname{nil}\left(\right)) \land (\operatorname{E}\left(H, v\right) = \operatorname{nil}\left(\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.positive_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every H>=1 and every natural pair v, the fixed controller has the displayed terminating operational run. The same event tape's complete action projection is A. Its terminal residue equals the entry residue and its earned output is res(H,v). The period is least among all positive matrix return exponents. Every test really executes its compiler word, pays one full current gcd, and completes its closing list before the next test.

Induction on the remaining rounds proves that every next test starts at the entry residue. Congruence makes its actual reply equal to the existing scheduler's compiled reply on the entry. Positive reverse closing restores that residue and earns the next cut. The existing scheduler then decodes the entry. Its answer function occurs only in this mathematical correspondence; the controller receives only its actual paid replies.

A word with r replacements and g grafts contributes L(H)r and Hg calls after closing. Summing the actual two tapes gives the exact resource vector. No component is borrowed from a reset run or from the different parity-scan construction. The affine endpoint is indexed by actual suffix counts. On natural pairs R never decreases q and at most doubles it, while G adds exactly two. Induction gives the upper bound and the inequality for every chronological source prefix.

Read optimality against all continuous competitors, immutable entry storage, a separate synchronized mutable current register, and the installed action/acknowledgement/commit continuation remain separate mathematical interfaces. This execution uses the supplied current gcd service, exclusive serialization, genuine binding and rights, completion of finite local work and sufficient per-run source/controller backing. It does not construct those physical services or derive rights or backing from finite code. All source calls, acknowledgements, local work, tape writes, installation and retention remain charged. In particular the scheduler's bounded public shift search does not establish the original polynomial bit-work or workspace bounds. No resource optimum beyond the separate read problem and no syntax, chronology or whole-memory inverse is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.closing`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.controller`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.executionEvents`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.executionWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.graftSuffixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.graftSum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.matrix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.period`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.positive_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.residue_run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.tests`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport](ContinuousAcquisitionTransport.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler](../SourceCoordinates/CommonDirectionScheduler.md)
