using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class Scale40BetaGainChildrenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual leaf reports fix beta frontiers in literal Fibonacci blocks.",
        H("Beta Resources in an Actual Leaf History"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-beta-frontier"),
                DeclarationHandle.Create(Prefix + "betaLeaves"), H("Actual beta frontier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The beta frontier filters the existing actual leaf-address set by the original beta reply. "
                    + "Addresses are finite left/right words, including the empty root."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("history-fixed-beta-union"),
                DeclarationHandle.Create(Prefix + "psi"), H("Fixed beta union"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each block decoded from an actual leaf report, prefix its actual beta frontier by its block root. "
                    + "Take the finite union of these addresses. A contributes LL and R; C contributes LLL, LR and RL. "
                    + "Branch and absent reports contribute no blocks, and repeated addresses are counted once."))), DescribeRole.Definition))));
}
