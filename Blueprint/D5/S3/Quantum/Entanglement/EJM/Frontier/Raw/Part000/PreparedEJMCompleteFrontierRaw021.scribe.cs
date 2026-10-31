using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000;

internal sealed class PreparedEJMCompleteFrontierRaw021Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/PreparedEJMCompleteFrontierRaw021.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 021",
        H("Original suffix contexts and responses 021"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 128 original suffix acceptance declarations and 128 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("raw-cut-02688", "raw_cut_02688", "Original suffix at depth 13, code 23007, node 83640",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 23007 and original node 83640. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof unfolds Accepted and reduces the original cached suffix check at these exact inputs.", DescribeRole.Theorem),
            Node("raw-cut-02815", "raw_cut_02815", "Original suffix at depth 14, code 106513, node 86698",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 14, code 106513 and original node 86698. Its checker retains remaining fuel 7, the full prefixCache and full prefixPartial. The proof unfolds Accepted and reduces the original cached suffix check at these exact inputs.", DescribeRole.Theorem),
            Node("response-cut-02688", "response_cut_02688", "Canonical response for cut 02688",
                "The complete row has depth 13, base-four code 23007, original node 83640, kind 2, reserved field 0, 1041 subtree occurrences and completion domain 16384. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-02815", "response_cut_02815", "Canonical response for cut 02815",
                "The complete row has depth 14, base-four code 106513, original node 86698, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 4096. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
