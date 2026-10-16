using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact total ordered pair decoding.",
        H("Exact total ordered pair decoding"),
        Blocks(
            Paragraph(Text("The outer format is a unary prefix of the first payload length, zero, first payload, then second payload. Decoding succeeds exactly on pairWords x y. The actual unpack program handles every raw word in at most four times its length plus eight instructions; success returns the two unchanged payloads in separate registers.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackpair"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackPair.decodePair_eq_some_iff"),
                H("decodePair_eq_some_iff"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackParse")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Classes"))]));
}
