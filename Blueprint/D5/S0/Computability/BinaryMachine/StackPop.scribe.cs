using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackPopDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical stack deletion.",
        H("Physical stack deletion"),
        Blocks(
            Paragraph(Text("Deleting a stack head uses the supplied tape deletion and shifting machines. The representation relates the entire remaining encoded register region and both neighboring regions; output projection is taken from the actual final tape.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackpop"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackPop.pop_register_of_equivalent"),
                H("pop_register_of_equivalent"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackCompiler")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/TapeEquiv"))]));
}
