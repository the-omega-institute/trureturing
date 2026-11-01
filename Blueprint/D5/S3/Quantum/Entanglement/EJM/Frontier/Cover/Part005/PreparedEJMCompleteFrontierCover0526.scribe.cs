using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0526Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0526.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0526",
        H("Original frontier context coverage 0526"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25252", "selected_cut_25252", "Selected cut at depth 12, code 77704, node 638422",
                "At remaining fuel 9 and original index 638422, selection on the full partial prefix of depth 12 and code 77704 returns the complete row with depth 12, base-four code 77704, original node 638422, kind 2, reserved field 0, 2457 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25300", "selected_cut_25300", "Selected cut at depth 12, code 77755, node 639710",
                "At remaining fuel 9 and original index 639710, selection on the full partial prefix of depth 12 and code 77755 returns the complete row with depth 12, base-four code 77755, original node 639710, kind 2, reserved field 0, 1021 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19425-638387", "unmarked_context_11_19425_638387", "Unmarked parent at depth 11, code 19425",
                "The frontier Boolean is false at remaining fuel 10, original node 638387, the whole prefixCache at depth 11 and code 19425, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19437-639653", "unmarked_context_11_19437_639653", "Unmarked parent at depth 11, code 19437",
                "The frontier Boolean is false at remaining fuel 10, original node 639653, the whole prefixCache at depth 11 and code 19437, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19425-638387", "node_context_11_19425_638387", "Original split at fuel 10 and node 638387",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 638276, 638313, 638337, 638386. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19437-639653", "node_context_11_19437_639653", "Original split at fuel 10 and node 639653",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 639612, 639629, 639639, 639652. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19425-638387", "context_11_19425_638387", "Context at depth 11, code 19425, node 638387",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19425 and original node 638387, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77700_638276, context_12_77701_638313, context_12_77702_638337, context_12_77703_638386.", DescribeRole.Theorem),
            Node("context-12-77755-639710", "context_12_77755_639710", "Context at depth 12, code 77755, node 639710",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77755 and original node 639710, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
