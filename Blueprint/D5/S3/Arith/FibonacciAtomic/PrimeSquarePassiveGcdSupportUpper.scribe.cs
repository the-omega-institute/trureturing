using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PrimeSquarePassiveGcdSupportUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single memoized original prime-square tree determines every positive gcd future with at most zeroRank(p)+p-2 distinct paid addresses.",
        H("Prime-Square Passive Gcd Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-square-passive-gcd-support-upper"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/PrimeSquarePassiveGcdSupportUpper.result"),
                H("One tree for all natural source pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural prime p, let T be empty-cache memoization of "
                        + "PrimePowerPassiveGcdController.protocol(p,2). The query type is the "
                        + "positive natural times and each response is a natural number. "
                        + "The channel reads actualGcd(p^2,k,v) at the actual selected time k "
                        + "on the original natural pair v. For every v in N times N, the "
                        + "completed actual history of T has length at most zeroRank(p)+p-2. "
                        + "For all v,w in that same domain, equality of their completed histories "
                        + "implies actualGcd(p^2,k,v)=actualGcd(p^2,k,w) for every natural k>0. "
                        + "The tree is fixed before either source is chosen.")),
                    Paragraph(Text("Put r=zeroRank(p). For each run, some t<r contains all its "
                        + "query addresses in the union of the interval 1 through r and "
                        + "the values t+j*r+1 with 1<=j<=p-2. The initial times 1 and 2 "
                        + "belong to the first interval because r>=3. The first-layer scan "
                        + "maintains n+phase=r. Exhaustion has no selected phase and no later "
                        + "query; a hit selects its own phase t<r. At prime-square precision "
                        + "the chosen content depth c<2 is either zero, leaving one lift, "
                        + "or one, leaving no lift.")),
                    Paragraph(Text("A stagnant lift repeats t+1, already in the first interval. "
                        + "A growing lift maintains n+j=p-1 during its child scan. An emitted "
                        + "query has j<p-1. Its j=0 address again lies in the first interval; "
                        + "each positive j is at most p-2 and lies in the shifted band. "
                        + "Selection or exhaustion enters a continuation with zero remaining "
                        + "fuel, so the omitted j=p-1 child adds no reply. This includes p=2, "
                        + "whose shifted band is empty.")),
                    Paragraph(Text("The union has at most r+(p-2) elements. Uniform dependent "
                        + "memoization pays exactly once per original query address and "
                        + "preserves equality of completed histories in both directions. "
                        + "The complete-future law of the concrete original protocol therefore "
                        + "continues to hold. Zero pairs, mixed-zero pairs, saturated content, "
                        + "scan exhaustion, hits and all growth or stagnant branches remain "
                        + "in the same domain. The result bounds paid query count; it gives "
                        + "no optimality, maximum-index or total running-time assertion."))),
                DescribeRole.Theorem))));
}
