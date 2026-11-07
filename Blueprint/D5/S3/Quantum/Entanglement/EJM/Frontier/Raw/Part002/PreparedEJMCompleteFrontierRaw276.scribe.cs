using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part002;

internal sealed class PreparedEJMCompleteFrontierRaw276Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part002/PreparedEJMCompleteFrontierRaw276.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 276",
        H("Original suffix contexts and responses 276"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 128 original suffix acceptance declarations and 128 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("raw-cut-35328", "raw_cut_35328", "Original suffix at depth 10, code 17829, node 893098",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 10, code 17829 and original node 893098. Its checker retains remaining fuel 11, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("raw-cut-35455", "raw_cut_35455", "Original suffix at depth 12, code 286729, node 932060",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 12, code 286729 and original node 932060. Its checker retains remaining fuel 9, the full prefixCache and full prefixPartial. The proof transports the concrete memoized checker equation through check_eq_original at exactly this fuel, index, cache and partial assignment. Decoder memoization supplies equality; the concrete suffix check remains a separate premise of the transport.", DescribeRole.Theorem),
            Node("response-cut-35328", "response_cut_35328", "Canonical response for cut 35328",
                "The complete row has depth 10, base-four code 17829, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem),
            Node("response-cut-35455", "response_cut_35455", "Canonical response for cut 35455",
                "The complete row has depth 12, base-four code 286729, original node 932060, kind 2, reserved field 0, 2989 subtree occurrences and completion domain 65536. For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proof invokes response_of_raw with the matching raw_cut acceptance and concrete depth/index side conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
