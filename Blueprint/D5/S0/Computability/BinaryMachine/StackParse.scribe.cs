using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackParseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive unary-prefix parsing.",
        H("Primitive unary-prefix parsing"),
        Blocks(
            Paragraph(Text("The finite parser consumes unary prefix bits into a Boolean counter and leaves the remaining payload unchanged. Missing terminators reject by actual execution. Its exact instruction budget is used by paired input decoding.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackparse"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackParse.exec_readUnary_encoded"),
                H("exec_readUnary_encoded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text(
                    "This declaration and its proof are attributed immutable source supply. "
                    + "The mathematical namespace and proof body are preserved. Full license, "
                    + "source correspondence and the finite retirement contract are recorded "
                    + "in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies "
                    + "no new classification or independent mathematical escape content."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackWords")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/UnaryWords"))]));
}
