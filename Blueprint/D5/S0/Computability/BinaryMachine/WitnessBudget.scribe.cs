using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class WitnessBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Checking the original target certificate bound.",
        H("Checking the original target certificate bound"),
        Blocks(
            Paragraph(Text("For an arbitrary target x and witness w, the finite program computes unary length(x) plus one, constructs c times that base to exponent e, and compares length(w) to it. The target bytes are preserved and work registers are empty on return. Runtime and residual stack bounds are polynomial in the actual target and witness lengths, including c equal to zero and e equal to zero.")),
            Describe.Lean(
                DescribeId.Create("exec-test"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/WitnessBudget.exec_test"),
                H("exec_test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("For an arbitrary target x and witness w, the finite program computes unary length(x) plus one, constructs c times that base to exponent e, and compares length(w) to it. The target bytes are preserved and work registers are empty on return. Runtime and residual stack bounds are polynomial in the actual target and witness lengths, including c equal to zero and e equal to zero."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackPower")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackCompare")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackPair"))]));
}
