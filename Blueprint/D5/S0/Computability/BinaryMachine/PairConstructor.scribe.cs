using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class PairConstructorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An executed ordered pair constructor.",
        H("An executed ordered pair constructor"),
        Blocks(
            Paragraph(Text("Registers zero and one contain arbitrary raw words u and v. With work registers two and three empty, the finite program writes exactly pairWords u v into register zero and empties register one in seven times length(u) plus four times length(v) plus twelve instructions. Every other register remains unchanged.")),
            Describe.Lean(
                DescribeId.Create("exec-build"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/PairConstructor.exec_build"),
                H("exec_build"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Registers zero and one contain arbitrary raw words u and v. With work registers two and three empty, the finite program writes exactly pairWords u v into register zero and empties register one in seven times length(u) plus four times length(v) plus twelve instructions. Every other register remains unchanged."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackPair")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackControl"))]));
}
