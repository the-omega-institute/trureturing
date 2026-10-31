using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part002;

internal sealed class PreparedEJMCompleteFrontierRaw218Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part002/PreparedEJMCompleteFrontierRaw218.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 218",
        H("Original suffix contexts and responses 218"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 128 original suffix acceptance declarations and 128 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("raw-cut-27904", "raw_cut_27904", "Original suffix at depth 13, code 367780, node 704957",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 367780 and original node 704957. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("raw-cut-28031", "raw_cut_28031", "Original suffix at depth 13, code 368006, node 707763",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 368006 and original node 707763. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("response-cut-27904", "response_cut_27904", "Canonical response for cut 27904",
                "The complete row has depth 13, base-four code 367780, original node 704957, kind 2, reserved field 0, 969 subtree occurrences and completion domain 16384. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-28031", "response_cut_28031", "Canonical response for cut 28031",
                "The complete row has depth 13, base-four code 368006, original node 707763, kind 2, reserved field 0, 2225 subtree occurrences and completion domain 16384. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
