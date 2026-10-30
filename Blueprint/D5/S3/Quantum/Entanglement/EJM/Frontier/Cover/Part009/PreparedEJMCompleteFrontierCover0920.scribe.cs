using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0920Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0920.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0920",
        H("Original frontier context coverage 0920"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44162", "selected_cut_44162", "Selected cut at depth 10, code 22085, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 22085 returns the complete row with depth 10, base-four code 22085, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44210", "selected_cut_44210", "Selected cut at depth 12, code 353549, node 1214111",
                "At remaining fuel 9 and original index 1214111, selection on the full partial prefix of depth 12 and code 353549 returns the complete row with depth 12, base-four code 353549, original node 1214111, kind 2, reserved field 0, 1317 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88347-1212932", "unmarked_context_11_88347_1212932", "Unmarked parent at depth 11, code 88347",
                "The frontier Boolean is false at remaining fuel 10, original node 1212932, the whole prefixCache at depth 11 and code 88347, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88386-1214092", "unmarked_context_11_88386_1214092", "Unmarked parent at depth 11, code 88386",
                "The frontier Boolean is false at remaining fuel 10, original node 1214092, the whole prefixCache at depth 11 and code 88386, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88347-1212932", "node_context_11_88347_1212932", "Original split at fuel 10 and node 1212932",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1212879, 896706, 1212904, 1212931. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88386-1214092", "node_context_11_88386_1214092", "Original split at fuel 10 and node 1214092",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1213962, 1214028, 1214091. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22085-893098", "context_10_22085_893098", "Context at depth 10, code 22085, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22085 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-353549-1214111", "context_12_353549_1214111", "Context at depth 12, code 353549, node 1214111",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353549 and original node 1214111, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
