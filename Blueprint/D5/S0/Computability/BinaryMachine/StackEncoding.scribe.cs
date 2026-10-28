using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean register regions on a tape.",
        H("Boolean register regions on a tape"),
        Blocks(
            Paragraph(Text("Boolean words occupy delimited tape regions. Register update identities preserve the ordered surrounding regions. Initial input encoding and physical output extraction use this exact representation, with no alternate language encoding.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackencoding"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackEncoding.homeTape_initial"),
                H("homeTape_initial"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackCompiler"))]));
}
