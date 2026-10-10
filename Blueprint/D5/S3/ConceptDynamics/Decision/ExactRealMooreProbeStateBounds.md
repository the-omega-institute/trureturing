# Exact Real Moore Probe State Bounds

## Abstract

A globally correct fixed literal Moore probe table has at least four query rows and at least six nominal rows.

**Theorem 1.1 (Four query rows and six nominal rows are necessary).**

$$\forall P \in Type,\; \operatorname{Finite}\left(P\right) \Rightarrow \left(\forall u \in P \to \operatorname{Sum}\left(I, Bool\right),\; \forall v \in P \to \left(Bool \to P\right),\; \forall entry \in P,\; \operatorname{CorrectEntry}\left(u, v, entry\right) \Rightarrow \left(4 \le \operatorname{card}\left(\operatorname{QueryRows}\left(u\right)\right) \land 6 \le \operatorname{card}\left(P\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds.nominal_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederic Magniez, Ashwin Nayak, Miklos Santha, Jonah Sherman, Gabor Tardos, and David Xiao (2013). *Improved bounds for the randomized decision tree complexity of recursive majority*. URL: <https://arxiv.org/abs/1309.7565v1>.

*Commentary.*

P is an arbitrary finite type, in any universe. The fixed action map u assigns each row either one exact parameter in the closed unit interval or one literal Boolean Halt output. The fixed successor map v reads only the current row and the Boolean response. There is one fixed entry, independent of the source. The source is the entire unit interval times Bool, with no source probability law. At source (x,b), query a returns the complement of b when a equals x, and b otherwise. Queries leave the source unchanged.

CorrectEntry means that for each source separately, some finite fuel makes mooreRun stop at the first literal Halt with output b. There is no common fuel premise. Actual is a finite first-Halt trace retaining each issuing row, exact parameter and response, together with the terminal row. Its conversion to and from mooreRun preserves the ordered record. Folding only the responses reconstructs the current row and supplies the history policy used by the exact real probe cost theorem. That theorem gives an actual run with three different parameters.

QueryRows(u) in the displayed statement is the subtype of all p in P for which u(p) is a query, and card is its nominal cardinality. The proof also uses the finite set queryRows(u) with the same members. Unreachable rows, repeated query literals and repeated output literals remain in P. The transition table may contain cycles. A finite actual run on one fixed read-only source cannot repeat a query row, since its remaining deterministic behavior would then repeat forever.

Suppose there are at most three query rows. Parameter containment and the three-parameter run force exactly three such rows and make their literal parameters pairwise distinct. The entry A must query a. Either response at A is compatible with two opposite labels, so neither successor can be any literal Halt row. A successor equal to A repeats an actual query row and is also impossible.

If both responses at A lead to B, every original source reaches B after one query. The actual suffix is finite and correct for each source, so B is a globally correct entry. Prepending the A query to any correct B run shows that A cannot occur in that run. Only the two remaining query rows are available. Applying the three-parameter theorem at B contradicts this bound.

Otherwise write A:false to B and A:true to C, with literals a,c,d respectively. Sources (c,false) and (a,true) reach B after response false and both give response true at B, while requiring opposite outputs. A literal Halt successor fails one of them. A or B as successor repeats an actual row, so B:true must lead to C. Sources (c,false) and (d,true) now reach C with response false and opposite required outputs. Any Halt successor again fails one source; each query successor repeats a row already visited by (c,false). This exhausts every nominal successor and proves four query rows are necessary.

The correct first-Halt runs on (0,false) and (0,true) have terminal rows carrying different literal outputs, so those rows are distinct. Both lie outside the set of all query rows. Its union with these two rows therefore has at least six members and is contained in the full nominal carrier P. The different-parameter lower bound is reused from exact real probe costs. The additional row obstruction uses the fixed literal Moore actions and counts the Halt rows. This is a nominal control-state bound, not a physical storage-bit bound.

**Example 1.2 (The response-fold policy satisfies the original Borel contract).**

$$
\forall P \in Type,\; \forall u \in P \to \operatorname{Sum}\left(I, Bool\right),\; \forall v \in P \to \left(Bool \to P\right),\; \forall entry \in P,\; \operatorname{MeasurableStrategy}\left(\operatorname{constantUnit}\left(\operatorname{policy}\left(u, v, entry\right)\right)\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* Frederic Magniez, Ashwin Nayak, Miklos Santha, Jonah Sherman, Gabor Tardos, and David Xiao (2013). *Improved bounds for the randomized decision tree complexity of recursive majority*. URL: <https://arxiv.org/abs/1309.7565v1>.

*Commentary.*

P is arbitrary in any universe; no finiteness hypothesis is needed. The policy folds only Boolean responses over every finite ordered history, including impossible histories, and extends Halt by a stopped state. The Unit-indexed strategy has Borel controls at every record length and sourcewise measurable cost, finite-return and error events. This follows by composition with the finite Boolean response word at each record length.

**Theorem 1.3 (Finite nominal tables have Borel cost on the entire original source).**

$$\forall P \in Type,\; \operatorname{Finite}\left(P\right) \Rightarrow \left(\forall u \in P \to \operatorname{Sum}\left(I, Bool\right),\; \forall v \in P \to \left(Bool \to P\right),\; \forall entry \in P,\; \operatorname{Measurable}\left(\operatorname{sourceCost}\left(\operatorname{policy}\left(u, v, entry\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds.cost_source_borel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederic Magniez, Ashwin Nayak, Miklos Santha, Jonah Sherman, Gabor Tardos, and David Xiao (2013). *Improved bounds for the randomized decision tree complexity of recursive majority*. URL: <https://arxiv.org/abs/1309.7565v1>.

*Commentary.*

P is finite, u and v are fixed literal maps, and entry is fixed. Source is the entire closed interval times Bool. sourceCost(pi) denotes the function sending an original source s to cost(pi,s). Cost counts distinct query parameters on the unique finite return and is infinite when no return exists. The finite response signature is a proof-side factorization, not a finite replacement of the source domain or a controller input.

**Theorem 1.4 (Every finite-return record event is Borel on the original source).**

$$\forall P \in Type,\; \operatorname{Finite}\left(P\right) \Rightarrow \left(\forall u \in P \to \operatorname{Sum}\left(I, Bool\right),\; \forall v \in P \to \left(Bool \to P\right),\; \forall entry \in P,\; \forall E \in \operatorname{Set}\left(\operatorname{Product}\left(History, Bool\right)\right),\; \operatorname{MeasurableSet}\left(\operatorname{mooreReturnEvent}\left(u, v, entry, E\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds.terminal_event_source_borel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederic Magniez, Ashwin Nayak, Miklos Santha, Jonah Sherman, Gabor Tardos, and David Xiao (2013). *Improved bounds for the randomized decision tree complexity of recursive majority*. URL: <https://arxiv.org/abs/1309.7565v1>.

*Commentary.*

P is finite. For every set E of ordered records paired with outputs, mooreReturnEvent(u,v,entry,E) is the set of original sources s for which some natural fuel n and returned pair hb satisfy mooreRun(u,v,s,n,entry)=some(hb) and hb belongs to E. E has no extra measurability premise. No correctness, acyclicity or common fuel hypothesis is assumed.

**Example 1.5 (The literal six-row table attains the bound).**

$$
\operatorname{CorrectEntry}\left(U, V, F\right) \land \left(\left(\forall s \in Source,\; \operatorname{Actual}\left(U, V, s, F, \operatorname{T}\left(s\right), \operatorname{L}\left(\operatorname{bit}\left(s\right)\right), \operatorname{bit}\left(s\right)\right) \land \left(\operatorname{M}\left(s, 4, F\right) = \operatorname{some}\left(\operatorname{pair}\left(\operatorname{R}\left(\operatorname{T}\left(s\right)\right), \operatorname{bit}\left(s\right)\right)\right) \land \left(\left(\forall n \in Nat,\; \operatorname{Epi}\left(piThree, n, \operatorname{nil}\left(\right), s\right) = \operatorname{M}\left(s, n, F\right)\right) \land \left(\operatorname{cost}\left(pi, s\right) = \operatorname{C}\left(s\right) \land \left(\forall rs \in \operatorname{ListTagged}\left(LiteralRow\right),\; \forall q \in LiteralRow,\; \forall b \in Bool,\; \operatorname{Actual}\left(U, V, s, F, rs, q, b\right) \Rightarrow \left(\operatorname{R}\left(rs\right) = \operatorname{R}\left(\operatorname{T}\left(s\right)\right) \land \left(q = \operatorname{L}\left(\operatorname{bit}\left(s\right)\right) \land \left(b = \operatorname{bit}\left(s\right) \land \operatorname{card}\left(\operatorname{parameters}\left(\operatorname{R}\left(rs\right)\right)\right) = \operatorname{C}\left(s\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall p \in LiteralRow,\; \exists pre \in \operatorname{ListTagged}\left(LiteralRow\right),\; \exists tail \in \operatorname{ListTagged}\left(LiteralRow\right),\; \exists q \in LiteralRow,\; \operatorname{Prefix}\left(U, V, \operatorname{W}\left(p\right), F, pre, p\right) \land \operatorname{Actual}\left(U, V, \operatorname{W}\left(p\right), p, tail, q, \operatorname{bit}\left(\operatorname{W}\left(p\right)\right)\right)\right) \land \left(\operatorname{card}\left(\operatorname{queryRows}\left(U\right)\right) = 4 \land \left(\operatorname{card}\left(LiteralRow\right) = 6 \land \left(\left(\forall s \in Source,\; \forall pre \in \operatorname{ListTagged}\left(LiteralRow\right),\; \forall p \in LiteralRow,\; \operatorname{Prefix}\left(U, V, s, F, pre, p\right) \Rightarrow \operatorname{pi}\left(\operatorname{R}\left(pre\right)\right) = \operatorname{U}\left(p\right)\right) \land \left(\left(\forall h \in History,\; \forall k \in History,\; \operatorname{responses}\left(h\right) = \operatorname{responses}\left(k\right) \Rightarrow \operatorname{pi}\left(h\right) = \operatorname{pi}\left(k\right)\right) \land \left(\operatorname{MeasurableStrategy}\left(\operatorname{constantUnit}\left(pi\right)\right) \land \left(\operatorname{Measurable}\left(\operatorname{sourceCost}\left(pi\right)\right) \land \left(\left(\forall E \in \operatorname{Set}\left(\operatorname{Product}\left(History, Bool\right)\right),\; \operatorname{MeasurableSet}\left(\operatorname{returnEvent}\left(pi, E\right)\right)\right) \land \left(\left(\forall s \in Source,\; \operatorname{cost}\left(pi, s\right) \le 3\right) \land \operatorname{cost}\left(pi, \operatorname{pair}\left(0, \operatorname{false}\left(\right)\right)\right) = 3\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* Frederic Magniez, Ashwin Nayak, Miklos Santha, Jonah Sherman, Gabor Tardos, and David Xiao (2013). *Improved bounds for the randomized decision tree complexity of recursive majority*. URL: <https://arxiv.org/abs/1309.7565v1>.

*Commentary.*

The carrier LiteralRow consists of F, B0, B1, G, H0 and H1. The entry is F for every source. F queries 0 and sends false to B0 and true to B1. B0 queries 1/2 and sends false to H0 and true to G. B1 queries the same literal 1/2 and sends false to G and true to H1. G queries 1 and sends false to H0 and true to H1. H0 halts with false; H1 halts with true. Both Halt successors are their own row, and are unused after the first Halt. These are fixed literal real actions; no source name, history, clock or additional output port is read.

Write U for literalAction, V for literalNext, L(b) for literalHalt(b), T(s) for literalTrace(s), and R for records. The first tagged record is (F,0,response(0,s)); the second is (B1,1/2,response(1/2,s)) when the first response is true and (B0,1/2,response(1/2,s)) otherwise. The tagged record (G,1,response(1,s)) is appended exactly when the first two responses differ. The terminal row is L(b). Write C(s) for the natural number 2 plus the indicator that the coordinate of s is 0 or 1/2, also coerced to the extended nonnegative reals when used as a cost. In the formula, Epi is the original finite-fuel execute response pi, M is mooreRun U V, pi is policy U V F, piThree is threeProbe(0,1/2,1), bit is the Boolean component, and parameters is the finite set of distinct literal query values.

For every original (x,b) in the whole closed interval times Bool, T(s) is an actual finite first-Halt trace. If x is outside {0,1/2}, its responses are b,b, and the table stops after two queries. If x is 0, its responses are complement(b),b,b; if x is 1/2, they are b,complement(b),b. In both exceptional cases the table queries 1 and stops after three queries. The returned output is b in every case. Fuel four suffices for this construction; that bound is a consequence and is not a premise on competing tables.

At every fuel the original threeProbe execution and this Moore execution agree on the same source, preserving the ordered literal query-response record and first stopping output. Every actual first-Halt trace agrees with T(s), including its terminal row. The cost is the number of distinct parameters in that record, equal to C(s), at most three, and exactly three at (0,false). Four nominal query rows and six total rows count both midpoint rows and both literal output rows.

W(p) in the formula is the explicit source literalWitness(p): (1,false) for F, B0 and H0; (1,true) for B1 and H1; and (0,false) for G. The empty prefix witnesses F. The first query reaches B0 or B1; the first two queries reach H0 or H1 on their stated sources. On (0,false), the prefix F then B1 reaches G. Each prefix has an actual finite continuation to the first Halt, including the empty continuation at a Halt row.

The policy folds only Boolean responses over the entire original history space and keeps Halt rows stopped. Equal response words give equal actions, including on histories that never occur. On each actual prefix, its action is the current row's literal action. Each fixed record length has a Borel control map. The input-independent Unit strategy satisfies the original sourcewise cost and finite return/error event measurability contract. Cost is also Borel as a function of the original source, and every finite-return record/output event is Borel. Agreement with threeProbe is asserted on actual executions; no equality on impossible or post-Halt histories is required.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds.cost_source_borel`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds.nominal_lower_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds.terminal_event_source_borel`
- Dependency: [D5/S3/ConceptDynamics/Decision/ExactRealProbeCosts](ExactRealProbeCosts.md)
