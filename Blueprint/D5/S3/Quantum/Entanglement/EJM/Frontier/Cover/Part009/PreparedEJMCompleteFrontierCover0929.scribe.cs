using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0929Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0929.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0929",
        H("Original frontier context coverage 0929"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44595", "selected_cut_44595", "Selected cut at depth 12, code 354579, node 1227888",
                "At remaining fuel 9 and original index 1227888, selection on the full partial prefix of depth 12 and code 354579 returns the complete row with depth 12, base-four code 354579, original node 1227888, kind 2, reserved field 0, 2513 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44642", "selected_cut_44642", "Selected cut at depth 11, code 88664, node 1229181",
                "At remaining fuel 10 and original index 1229181, selection on the full partial prefix of depth 11 and code 88664 returns the complete row with depth 11, base-four code 88664, original node 1229181, kind 2, reserved field 0, 2985 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88644-1227889", "unmarked_context_11_88644_1227889", "Unmarked parent at depth 11, code 88644",
                "The frontier Boolean is false at remaining fuel 10, original node 1227889, the whole prefixCache at depth 11 and code 88644, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22164-1229120", "unmarked_context_10_22164_1229120", "Unmarked parent at depth 10, code 22164",
                "The frontier Boolean is false at remaining fuel 11, original node 1229120, the whole prefixCache at depth 10 and code 22164, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88644-1227889", "node_context_11_88644_1227889", "Original split at fuel 10 and node 1227889",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1227818, 1227855, 1227888. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22164-1229120", "node_context_10_22164_1229120", "Original split at fuel 11 and node 1229120",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1228972, 1229026, 1229069, 1229119. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-354579-1227888", "context_12_354579_1227888", "Context at depth 12, code 354579, node 1227888",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 354579 and original node 1227888, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88664-1229181", "context_11_88664_1229181", "Context at depth 11, code 88664, node 1229181",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88664 and original node 1229181, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
