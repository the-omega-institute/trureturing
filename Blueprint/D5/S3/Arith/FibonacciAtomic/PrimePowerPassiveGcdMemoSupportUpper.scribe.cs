using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PrimePowerPassiveGcdMemoSupportUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One empty-cache memoized original prime-power tree determines every positive numerical gcd future with a uniform bound on distinct paid addresses.",
        H("Prime-Power Passive Gcd Memo Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-passive-gcd-memo-support-upper"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdMemoSupportUpper.result"),
                H("The original tree on every natural source pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural prime p and every natural exponent e>=1, "
                        + "fix empty-cache memoization of PrimePowerPassiveGcdController.protocol(p,e). "
                        + "Its query type is the positive natural times and each response is a "
                        + "natural number. At the actual selected time k, its channel reads "
                        + "actualGcd(p^e,k,v) on the original pair v. Put r=zeroRank(p). "
                        + "For every v in N times N, the completed history has length at most "
                        + "r when e=1, and at most r+(e-1)*(p-1)-1 when e>=2. "
                        + "For all v,w in that same domain, equal completed histories imply "
                        + "actualGcd(p^e,k,v)=actualGcd(p^e,k,w) for every natural k>0. "
                        + "The same tree is fixed before either source is selected.")),
                    Paragraph(Text("The counting invariant concerns the support of an actual "
                        + "original continuation with arbitrary remaining fuel n, precision d, "
                        + "content and phase t. Against any finite set S of addresses already "
                        + "accounted for, adjoining that support adds at most n*(p-1) addresses. "
                        + "If the current representative t+1 already belongs to S, the bound "
                        + "improves to n*(p-1)-1, with natural subtraction giving zero at n=0. "
                        + "The two estimates are proved together by induction on the fuel. "
                        + "Moving a queried address into S costs at most one and costs zero "
                        + "when it is already present.")),
                    Paragraph(Text("At a stagnant lift the original tree queries t+1. A hit "
                        + "continues with one less fuel and the same representative; a miss "
                        + "stops. At a growing lift, the child scan tests up to p-1 children "
                        + "j=0 through j=p-2. Each queried hit continues at that queried "
                        + "representative. Exhaustion selects child j=p-1 without querying "
                        + "it, and therefore uses the general-parent estimate for its "
                        + "continuation. When the parent address is already in S, the first "
                        + "j=0 query costs zero. A hit then uses the remaining continuation "
                        + "bound; a miss leaves p-2 tests and a general-parent continuation. "
                        + "This supplies the saved address without assuming that the next "
                        + "representative after exhaustion was queried. The same proof "
                        + "includes p=2, for which p-2 is zero.")),
                    Paragraph(Text("All first-layer scan addresses, together with the two "
                        + "initial content times, belong to the interval from 1 through r, "
                        + "whose cardinality is r because r>=3. Scan exhaustion adds no "
                        + "continuation. A hit at phase t<r supplies the already-accounted "
                        + "representative t+1. A content label p^c with c<e leaves fuel "
                        + "e-c-1, so the cached-parent estimate gives the stated uniform "
                        + "bound for every content depth. Saturated content and malformed "
                        + "labels stop after the initial queries. Zero pairs, mixed-zero "
                        + "pairs, all hits, all scan exhaustions and stagnant lifts remain "
                        + "in the original source domain.")),
                    Paragraph(Text("The existing PassiveQueryMemoization result identifies "
                        + "empty-cache paid length with the original support cardinality "
                        + "and preserves equality of completed histories in both directions. "
                        + "The existing PrimePowerPassiveGcdController.protocol_spec then "
                        + "supplies equality of the complete positive numerical gcd future. "
                        + "These are reused suppliers; the added proof is the arbitrary-fuel "
                        + "support estimate distinguishing accounted and general parents. "
                        + "The result bounds paid query count and makes no optimality, "
                        + "maximum-index or total running-time assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-power-passive-gcd-rank-pattern-exact"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdMemoSupportUpper.rank_pattern_exact"),
                H("Exact worst history length of the fixed original tree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every prime p and exponent e>=1, put r_d=zeroRank(p^d). "
                        + "Let g count the depths d=1 through e-1 where r_(d+1) differs from r_d. "
                        + "The public growthCount recursively counts precisely these changes. "
                        + "Let delta be zero when e=1 or the last lift is stagnant, and one "
                        + "otherwise. Put B=r_1+g*(p-1)-delta. Fix the same original protocol, "
                        + "positive-time numerical read channel and empty-cache memo. Every "
                        + "source v in N times N has completed history length at most B. "
                        + "There is one fixed natural source v with both coordinates below "
                        + "p^e whose completed history has length exactly B.")),
                    Paragraph(Text("The refined proof counts a cached parent and an arbitrary "
                        + "parent together. Both extra budgets are zero at zero fuel. A "
                        + "stagnant lift has cached cost equal to the next cached budget; "
                        + "its arbitrary-parent cost is one plus that budget. A growing "
                        + "lift has cached cost p-2 plus the next arbitrary-parent budget, "
                        + "and arbitrary-parent cost p-1 plus that budget. Exhaustion "
                        + "selects an omitted address, so its successor uses the arbitrary "
                        + "budget. For positive fuel the two budgets differ by one. The "
                        + "cached budget equals g*(p-1) minus the final-growth indicator. "
                        + "Prefix monotonicity includes every content depth in the upper "
                        + "bound. The finite prior set S is proof accounting and supplies "
                        + "no runtime responses or additional cache.")),
                    Paragraph(Text("For attainment, the public modular realization and "
                        + "observation inverse supply a bounded natural source with "
                        + "observation (0,1) modulo H=p^e. Existing actual-source identities "
                        + "and gcd congruence give its reading gcd(fib(k),H) at every "
                        + "positive k. Its content depth is zero. The first scan first "
                        + "hits at r_1 and visits the whole interval 1 through r_1. "
                        + "At depth d the phase is r_d-1. Stagnation queries r_d and "
                        + "hits. Growth tests q*r_d for 1<=q<=p-1, all miss the next "
                        + "threshold, and selects the unqueried representative r_(d+1).")),
                    Paragraph(Text("Along this same source, cached prior support lies at or "
                        + "below r_d and contains r_d, while fresh prior support lies "
                        + "strictly below r_d. Distinct growing multiples beyond that "
                        + "support add exactly p-2 or p-1 addresses, respectively. The "
                        + "omitted next parent is beyond every tested address and remains "
                        + "fresh. Stagnation adds zero or one address before becoming "
                        + "cached. The exact cardinal recurrence therefore matches the "
                        + "universal upper recurrence. The precision/fuel condition keeps "
                        + "every tested threshold inside H. Existing memoization then "
                        + "transports support cardinality to paid length.")),
                    Paragraph(Text("The new mathematical content is the rank-dependent "
                        + "support bound together with its attained cardinality on the "
                        + "original source domain. Rank dichotomy, bounded modular "
                        + "realization, actual-source identities and memo transport are "
                        + "reused suppliers with no new mathematical credit. This is "
                        + "the exact worst cost of this fixed tree; it does not claim "
                        + "minimum adaptive cost, arbitrary-modulus optimality, maximum "
                        + "query index, running time or the larger full14 goal."))),
                DescribeRole.Theorem))));
}
