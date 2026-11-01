using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0066Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0066.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0066",
        H("Original frontier context coverage 0066"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03170", "selected_cut_03170", "Selected cut at depth 12, code 6752, node 1738",
                "At remaining fuel 9 and original index 1738, selection on the full partial prefix of depth 12 and code 6752 returns the complete row with depth 12, base-four code 6752, original node 1738, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03218", "selected_cut_03218", "Selected cut at depth 12, code 6797, node 100894",
                "At remaining fuel 9 and original index 100894, selection on the full partial prefix of depth 12 and code 6797 returns the complete row with depth 12, base-four code 6797, original node 100894, kind 2, reserved field 0, 2865 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-6755-98972", "unmarked_context_12_6755_98972", "Unmarked parent at depth 12, code 6755",
                "The frontier Boolean is false at remaining fuel 9, original node 98972, the whole prefixCache at depth 12 and code 6755, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1698-100785", "unmarked_context_11_1698_100785", "Unmarked parent at depth 11, code 1698",
                "The frontier Boolean is false at remaining fuel 10, original node 100785, the whole prefixCache at depth 11 and code 1698, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-6755-98972", "node_context_12_6755_98972", "Original split at fuel 9 and node 98972",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 98917, 98949, 98971. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1698-100785", "node_context_11_1698_100785", "Original split at fuel 10 and node 100785",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 100618, 100670, 100745, 100784. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-6752-1738", "context_12_6752_1738", "Context at depth 12, code 6752, node 1738",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 6752 and original node 1738, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-6797-100894", "context_12_6797_100894", "Context at depth 12, code 6797, node 100894",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 6797 and original node 100894, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
