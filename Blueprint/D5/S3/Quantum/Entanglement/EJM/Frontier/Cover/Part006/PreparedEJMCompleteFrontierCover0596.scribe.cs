using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0596Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0596.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0596",
        H("Original frontier context coverage 0596"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28611", "selected_cut_28611", "Selected cut at depth 12, code 92550, node 721795",
                "At remaining fuel 9 and original index 721795, selection on the full partial prefix of depth 12 and code 92550 returns the complete row with depth 12, base-four code 92550, original node 721795, kind 2, reserved field 0, 2233 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28658", "selected_cut_28658", "Selected cut at depth 11, code 23153, node 722768",
                "At remaining fuel 10 and original index 722768, selection on the full partial prefix of depth 11 and code 23153 returns the complete row with depth 11, base-four code 23153, original node 722768, kind 2, reserved field 0, 2453 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23137-721821", "unmarked_context_11_23137_721821", "Unmarked parent at depth 11, code 23137",
                "The frontier Boolean is false at remaining fuel 10, original node 721821, the whole prefixCache at depth 11 and code 23137, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1446-722708", "unmarked_context_9_1446_722708", "Unmarked parent at depth 9, code 1446",
                "The frontier Boolean is false at remaining fuel 12, original node 722708, the whole prefixCache at depth 9 and code 1446, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23137-721821", "node_context_11_23137_721821", "Original split at fuel 10 and node 721821",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 721770, 721771, 721795, 721820. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1446-722708", "node_context_9_1446_722708", "Original split at fuel 12 and node 722708",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 722045, 722339, 722517, 722707. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-92550-721795", "context_12_92550_721795", "Context at depth 12, code 92550, node 721795",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92550 and original node 721795, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-23153-722768", "context_11_23153_722768", "Context at depth 11, code 23153, node 722768",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23153 and original node 722768, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
