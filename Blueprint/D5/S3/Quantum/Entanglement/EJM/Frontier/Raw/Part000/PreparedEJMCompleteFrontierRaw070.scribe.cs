using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000;

internal sealed class PreparedEJMCompleteFrontierRaw070Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/PreparedEJMCompleteFrontierRaw070.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 070",
        H("Original suffix contexts and responses 070"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 128 original suffix acceptance declarations and 128 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("raw-cut-08960", "raw_cut_08960", "Original suffix at depth 12, code 23195, node 248790",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 12, code 23195 and original node 248790. Its checker retains remaining fuel 9, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("raw-cut-09087", "raw_cut_09087", "Original suffix at depth 14, code 372897, node 251806",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 14, code 372897 and original node 251806. Its checker retains remaining fuel 7, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("response-cut-08960", "response_cut_08960", "Canonical response for cut 08960",
                "The complete row has depth 12, base-four code 23195, original node 248790, kind 2, reserved field 0, 1921 subtree occurrences and completion domain 65536. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-09087", "response_cut_09087", "Canonical response for cut 09087",
                "The complete row has depth 14, base-four code 372897, original node 251806, kind 2, reserved field 0, 1313 subtree occurrences and completion domain 4096. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
