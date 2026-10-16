using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackCompareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A total primitive witness-length comparison.",
        H("A total primitive witness-length comparison"),
        Blocks(
            Paragraph(Text("A four-state finite program pops one source and one budget bit for each match. It returns true exactly when source length is at most budget length, irrespective of the bit values. Its actual instruction count is bounded by twice the source length plus three. Every other register remains unchanged.")),
            Describe.Lean(
                DescribeId.Create("exec-check"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackCompare.exec_check"),
                H("exec_check"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("A four-state finite program pops one source and one budget bit for each match. It returns true exactly when source length is at most budget length, irrespective of the bit values. Its actual instruction count is bounded by twice the source length plus three. Every other register remains unchanged."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackControl"))]));
}
