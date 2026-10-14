using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMSharedLocalReadoutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadouts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared original EJM local readouts",
        H("Shared original EJM local readouts"),
        Blocks(
            Paragraph(Text("Every shared readout retains its original local row, complete coordinate and outcome action, full actual local partial assignment and integer lower. The existing receipts relate the lookup assignment and lower to the entire original row. Transition slots and edges are neither copied nor used by static leaf arithmetic. Every actual global leaf still checks its own sixteen triangle projections, sixteen singleton projections and original lower sum.")),
            Node("triangle-readout", "TriangleReadout", "Shared triangle row and action readout",
                "Names one of the original 41,294 ten-coordinate triangle rows with its complete local action, transported assignment and lower.", DescribeRole.Definition),
            Node("singleton-readout", "SingletonReadout", "Shared singleton row and action readout",
                "Names one of the original 8,689 nine-coordinate singleton rows with its complete local action, transported assignment and lower.", DescribeRole.Definition),
            Node("check-triangle", "checkTriangle", "Check an original triangle readout once",
                "Checks the entire original triangle assignment against the earned action and the proposed partial, and checks the original lower.", DescribeRole.Definition),
            Node("check-singleton", "checkSingleton", "Check an original singleton readout once",
                "The corresponding full assignment and lower check uses the original singleton rows.", DescribeRole.Definition),
            Node("check-bound", "checkBound", "Check all actual projections and the original threshold",
                "All thirty-two selected readout assignments must match this actual global partial event. Their exact integer lower sum must reach the unchanged original scale 6,987,435.", DescribeRole.Definition),
            Node("checked-bound", "checked_bound", "The checked leaf bounds every original completion",
                "Complete local certificate acceptance and checked shared readouts discharge all numerical premises. The separately checked actual projections and original sum give the original EJM score bound on every compatible complete event.", DescribeRole.Theorem),
            Paragraph(Text("This conditional leaf checker does not assert acceptance of any concrete readout table, complete global context table, ideal-law nonlocality or source-noise region. Those conclusions require their corresponding actual kernel-checked certificates.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
