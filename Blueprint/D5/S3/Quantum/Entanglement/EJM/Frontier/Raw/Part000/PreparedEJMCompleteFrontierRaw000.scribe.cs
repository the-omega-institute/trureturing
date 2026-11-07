using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000;

internal sealed class PreparedEJMCompleteFrontierRaw000Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/PreparedEJMCompleteFrontierRaw000.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 000",
        H("Original suffix contexts and responses 000"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 128 original suffix acceptance declarations and 128 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("raw-cut-00000", "raw_cut_00000", "Original suffix at depth 12, code 0, node 415",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 12, code 0 and original node 415. Its checker retains remaining fuel 9, the full prefixCache and full prefixPartial. The proof uses the imported replay assembly for this exact original prefix and node.", DescribeRole.Theorem),
            Node("raw-cut-00127", "raw_cut_00127", "Original suffix at depth 14, code 4486, node 8193",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 14, code 4486 and original node 8193. Its checker retains remaining fuel 7, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("raw-cut-00001", "raw_cut_00001", "Original suffix at depth 13, code 4, node 674",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 4 and original node 674. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof uses the imported replay assembly for this exact original prefix and node.", DescribeRole.Theorem),
            Node("response-cut-00000", "response_cut_00000", "Canonical response for cut 00000",
                "The complete row has depth 12, base-four code 0, original node 415, kind 2, reserved field 0, 2061 subtree occurrences and completion domain 65536. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-00127", "response_cut_00127", "Canonical response for cut 00127",
                "The complete row has depth 14, base-four code 4486, original node 8193, kind 2, reserved field 0, 1429 subtree occurrences and completion domain 4096. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-00001", "response_cut_00001", "Canonical response for cut 00001",
                "The complete row has depth 13, base-four code 4, original node 674, kind 2, reserved field 0, 3269 subtree occurrences and completion domain 16384. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
