using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMAdaptiveResponseBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMAdaptiveResponseBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Turn original suffix acceptance into a smaller bad event",
        H("Turn original suffix acceptance into a smaller bad event"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("canonical-valid", "canonical_valid", "Validate the canonical cache and partial prefix together",
                "For every natural code and depth at most twenty, the complete prefix cache and partial assignment satisfy Valid at fuel twenty-one minus depth. The proof combines the fuel and future-coordinate conditions with prefix_associated.", DescribeRole.Theorem),
            Node("accepted-suffix-bad-event-response", "accepted_suffix_bad_event_response", "Apply original cached replay at the exact suffix",
                "For a depth at most twenty, original finite index and accepted original suffix, each compatible event with original F1/F2 score below scale has a smaller-rank event still below scale. The proof uses canonical_valid and the original cache lower bound, step validity, score invariance and domination-rank theorems.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
