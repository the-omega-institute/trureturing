using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part001;

internal sealed class PreparedEJMCompleteFrontierRaw123Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part001/PreparedEJMCompleteFrontierRaw123.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 123",
        H("Original suffix contexts and responses 123"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 128 original suffix acceptance declarations and 128 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("raw-cut-15744", "raw_cut_15744", "Original suffix at depth 13, code 111747, node 403211",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 111747 and original node 403211. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("raw-cut-15871", "raw_cut_15871", "Original suffix at depth 13, code 111877, node 405663",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 111877 and original node 405663. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("response-cut-15744", "response_cut_15744", "Canonical response for cut 15744",
                "The complete row has depth 13, base-four code 111747, original node 403211, kind 2, reserved field 0, 829 subtree occurrences and completion domain 16384. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-15871", "response_cut_15871", "Canonical response for cut 15871",
                "The complete row has depth 13, base-four code 111877, original node 405663, kind 2, reserved field 0, 3421 subtree occurrences and completion domain 16384. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
