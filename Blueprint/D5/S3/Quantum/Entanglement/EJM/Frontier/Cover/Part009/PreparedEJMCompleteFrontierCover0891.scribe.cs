using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0891Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0891.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0891",
        H("Original frontier context coverage 0891"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42772", "selected_cut_42772", "Selected cut at depth 12, code 338716, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 338716 returns the complete row with depth 12, base-four code 338716, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42818", "selected_cut_42818", "Selected cut at depth 10, code 21173, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 21173 returns the complete row with depth 10, base-four code 21173, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84678-1168537", "unmarked_context_11_84678_1168537", "Unmarked parent at depth 11, code 84678",
                "The frontier Boolean is false at remaining fuel 10, original node 1168537, the whole prefixCache at depth 11 and code 84678, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21172-1169840", "unmarked_context_10_21172_1169840", "Unmarked parent at depth 10, code 21172",
                "The frontier Boolean is false at remaining fuel 11, original node 1169840, the whole prefixCache at depth 10 and code 21172, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84678-1168537", "node_context_11_84678_1168537", "Original split at fuel 10 and node 1168537",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1168437, 1168482, 1168536. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21172-1169840", "node_context_10_21172_1169840", "Original split at fuel 11 and node 1169840",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1169596, 1169687, 1169788, 1169839. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84678-1168537", "context_11_84678_1168537", "Context at depth 11, code 84678, node 1168537",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84678 and original node 1168537, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_338712_1108174, context_12_338713_1168437, context_12_338714_1168482, context_12_338715_1168536.", DescribeRole.Theorem),
            Node("context-10-21173-893098", "context_10_21173_893098", "Context at depth 10, code 21173, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21173 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
