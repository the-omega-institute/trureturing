using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackInitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Initialization of encoded Boolean registers.",
        H("Initialization of encoded Boolean registers"),
        Blocks(
            Paragraph(Text("A fixed tape program transforms the literal input tape into the marked register representation with all other stacks empty. Its complete run and cell layout supply the initialization part of the same-model stack compiler.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackinit"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackInit.initMachine_run"),
                H("initMachine_run"),
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
