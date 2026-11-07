using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0739Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0739.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0739",
        H("Original frontier context coverage 0739"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35474", "selected_cut_35474", "Selected cut at depth 12, code 286748, node 1738",
                "At remaining fuel 9 and original index 1738, selection on the full partial prefix of depth 12 and code 286748 returns the complete row with depth 12, base-four code 286748, original node 1738, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35522", "selected_cut_35522", "Selected cut at depth 12, code 286862, node 934118",
                "At remaining fuel 9 and original index 934118, selection on the full partial prefix of depth 12 and code 286862 returns the complete row with depth 12, base-four code 286862, original node 934118, kind 2, reserved field 0, 1377 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71687-932739", "unmarked_context_11_71687_932739", "Unmarked parent at depth 11, code 71687",
                "The frontier Boolean is false at remaining fuel 10, original node 932739, the whole prefixCache at depth 11 and code 71687, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71714-934055", "unmarked_context_11_71714_934055", "Unmarked parent at depth 11, code 71714",
                "The frontier Boolean is false at remaining fuel 10, original node 934055, the whole prefixCache at depth 11 and code 71714, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71687-932739", "node_context_11_71687_932739", "Original split at fuel 10 and node 932739",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 932662, 932704, 932738. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71714-934055", "node_context_11_71714_934055", "Original split at fuel 10 and node 934055",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 933961, 933991, 934016, 934054. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-286748-1738", "context_12_286748_1738", "Context at depth 12, code 286748, node 1738",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 286748 and original node 1738, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-286862-934118", "context_12_286862_934118", "Context at depth 12, code 286862, node 934118",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 286862 and original node 934118, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
