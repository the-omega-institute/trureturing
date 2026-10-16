using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class UnaryWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unary outer-length prefixes.",
        H("Unary outer-length prefixes"),
        Blocks(
            Paragraph(Text("This live slice retains only the unary natural-prefix writer, reader, exact reconstruction and length law. It contains no supplied SAT language or Cook-Levin classification. A prefix consists of the stated number of ones followed by zero.")),
            Describe.Lean(
                DescribeId.Create("supplied-unarywords"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/UnaryWords.readNat_eq_some"),
                H("SAT.readNat_eq_some"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Classes"))]));
}
