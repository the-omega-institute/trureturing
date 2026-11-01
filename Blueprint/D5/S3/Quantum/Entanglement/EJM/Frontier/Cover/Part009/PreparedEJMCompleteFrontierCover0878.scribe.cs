using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0878Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0878.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0878",
        H("Original frontier context coverage 0878"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42147", "selected_cut_42147", "Selected cut at depth 11, code 84357, node 892405",
                "At remaining fuel 10 and original index 892405, selection on the full partial prefix of depth 11 and code 84357 returns the complete row with depth 11, base-four code 84357, original node 892405, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42194", "selected_cut_42194", "Selected cut at depth 12, code 337481, node 1153320",
                "At remaining fuel 9 and original index 1153320, selection on the full partial prefix of depth 12 and code 337481 returns the complete row with depth 12, base-four code 337481, original node 1153320, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84356-1152027", "unmarked_context_11_84356_1152027", "Unmarked parent at depth 11, code 84356",
                "The frontier Boolean is false at remaining fuel 10, original node 1152027, the whole prefixCache at depth 11 and code 84356, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84369-1153261", "unmarked_context_11_84369_1153261", "Unmarked parent at depth 11, code 84369",
                "The frontier Boolean is false at remaining fuel 10, original node 1153261, the whole prefixCache at depth 11 and code 84369, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84356-1152027", "node_context_11_84356_1152027", "Original split at fuel 10 and node 1152027",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1151931, 1151970, 1152026. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84369-1153261", "node_context_11_84369_1153261", "Original split at fuel 10 and node 1153261",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1153198, 170504, 1153230, 1153260. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84356-1152027", "context_11_84356_1152027", "Context at depth 11, code 84356, node 1152027",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84356 and original node 1152027, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_337424_1108174, context_12_337425_1151931, context_12_337426_1151970, context_12_337427_1152026.", DescribeRole.Theorem),
            Node("context-12-337481-1153320", "context_12_337481_1153320", "Context at depth 12, code 337481, node 1153320",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337481 and original node 1153320, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
