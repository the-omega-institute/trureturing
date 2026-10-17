using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteSymmetryBoundReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteSymmetryBoundReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual events, partial assignments and compatibility",
        H("Finite event and partial-assignment interface"),
        Blocks(
            Paragraph(Text("A complete event assigns a value to every original coordinate. A partial event records either an assigned value or an unknown coordinate. Compatibility requires the complete event to agree at every assigned coordinate. These shared definitions are used by the accepted local row DAG and cache association proofs.")),
            Node("event", "Event", "Complete events", "A complete event is a function from original coordinates to values."),
            Node("partial", "Partial", "Partial assignments", "Each original coordinate holds either a value or none; the entire function is retained in every association."),
            Node("compatible", "Compatible", "Agreement at every assigned coordinate", "Every recorded value must equal the corresponding value of the actual complete event."),
            Node("completed", "completed", "View a complete event as a partial assignment", "Every coordinate is assigned its actual value. The local DAG's terminal checker uses this exact completed function."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
