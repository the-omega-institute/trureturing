using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class DecisionSimulationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both tape decisions in a stack frame.",
        H("Both tape decisions in a stack frame"),
        Blocks(
            Paragraph(Text("The supplied initializer and core simulator are lifted injectively into registers zero, two and three. For every actual tape halt, accepting or rejecting, the finite program returns the identical Boolean decision in at most six times input length plus executed tape fuel plus one. This supplies decision transport without requiring true-halt output normalization.")),
            Describe.Lean(
                DescribeId.Create("exec-program"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/DecisionSimulation.exec_program"),
                H("exec_program"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The supplied initializer and core simulator are lifted injectively into registers zero, two and three. For every actual tape halt, accepting or rejecting, the finite program returns the identical Boolean decision in at most six times input length plus executed tape fuel plus one. This supplies decision transport without requiring true-halt output normalization."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/TransducerPair"))]));
}
