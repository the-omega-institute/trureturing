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
                    + "Branch and absent reports contribute no blocks, and repeated addresses are counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("strict-beta-growth"),
                DeclarationHandle.Create(Prefix + "result"), H("Strict beta growth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a finite family consist of actual third images, and retain the members matching every report in a finite history. "
                    + "Suppose an actual address strictly splits this survivor queue and has a nonempty alpha or beta leaf child. "
                    + "The old fixed beta union is contained in every surviving member's beta frontier. "
                    + "Adding the leaf report increases the fixed union by one, two or three addresses. "
                    + "The increase is one exactly when the report forces C and its immediately left A was already decoded from the history. "
                    + "A new A contributes two beta addresses; a new C contributes three unless its left A already contributes LLL and LR."))), DescribeRole.Theorem))));
}
