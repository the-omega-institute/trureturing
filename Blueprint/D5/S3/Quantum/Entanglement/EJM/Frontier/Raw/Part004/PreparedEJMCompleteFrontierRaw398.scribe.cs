using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part004;

internal sealed class PreparedEJMCompleteFrontierRaw398Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part004/PreparedEJMCompleteFrontierRaw398.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 398",
        H("Original suffix contexts and responses 398"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 128 original suffix acceptance declarations and 128 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("raw-cut-50944", "raw_cut_50944", "Original suffix at depth 6, code 109, node 434744",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 6, code 109 and original node 434744. Its checker retains remaining fuel 15, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("raw-cut-51071", "raw_cut_51071", "Original suffix at depth 11, code 114329, node 1467530",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 11, code 114329 and original node 1467530. Its checker retains remaining fuel 10, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("response-cut-50944", "response_cut_50944", "Canonical response for cut 50944",
                "The complete row has depth 6, base-four code 109, original node 434744, kind 1, reserved field 0, 1 subtree occurrences and completion domain 268435456. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-51071", "response_cut_51071", "Canonical response for cut 51071",
                "The complete row has depth 11, base-four code 114329, original node 1467530, kind 2, reserved field 0, 3521 subtree occurrences and completion domain 262144. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
