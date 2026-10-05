using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitCoarseScanAttainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three real coarse scans and a rational tail law attain both orders of maximum cost.",
        H("Four-Exit Coarse Scan Attainment"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-exit-coarse-scan-attainment"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitCoarseScanAttainment.result"),
            H("Simultaneous attainment by a finite rational law"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each positive k the evaluation family has one baseline and four exceptional "
                    + "rows per slot, each with n = 8k + 16 leaves. Branch and absent responses have "
                    + "one common coarse label. The retained slot, tail, and other slot scan kinds "
                    + "are chosen before execution.")),
                Paragraph(Text(
                    "The three scans place the second nonleaf request on A, Y, or Z. The three tails "
                    + "have excess vectors (1,0,1,2,1), (1,1,2,0,1), and (1,2,0,1,1) on the "
                    + "baseline and retained A, Y, H, Z rows. Every route selects its actual row. "
                    + "Complete leaf verification and full acquisition extend each route to a "
                    + "globally correct controller whose decisions depend only on coarse history.")),
                Paragraph(Text(
                    "On every evaluation row the set of addresses actually paid is exactly its "
                    + "leaf set together with the specified scan or tail nonleaf set. Each member "
                    + "has baseline excess one, maximum excess two, and total excess 5k. The cache "
                    + "merges repeated exact addresses from routing and verification.")),
                Paragraph(Text(
                    "The retained slot is uniform. Tail probabilities are (1/3,1/3,1/3) for k=1, "
                    + "(11/24,5/24,1/3) for k=2, ((k+3)/8,(5-k)/8,0) for 3<=k<=5, and "
                    + "(1,0,0) for k>=5. Scan probabilities are (3/8,3/8,1/4) for k=2, "
                    + "((3k+1)/(8(k-1)),(3k-7)/(8(k-1)),1/4) for 3<=k<=5, and "
                    + "((k+1)/(3(k-1)),(k-2)/(3(k-1)),(k-2)/(3(k-1))) for k>=5. "
                    + "The k=5 prescriptions agree; k=1 has no other slot.")),
                Paragraph(Text(
                    "This nonnegative normalized finite rational law has maximum expected cost "
                    + "n + max((5k-1)/(4k),(4k-2)/(3k)). Every selected controller has maximum "
                    + "cost n+2, so the same law has expected maximum cost n+2. "
                    + "The statement concerns actual address costs and does not impose an input prior."))),
            DescribeRole.Theorem))));
}
