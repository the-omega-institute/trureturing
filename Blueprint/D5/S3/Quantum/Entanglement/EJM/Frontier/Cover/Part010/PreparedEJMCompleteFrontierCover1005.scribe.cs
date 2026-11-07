using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1005Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1005.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1005",
        H("Original frontier context coverage 1005"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48244", "selected_cut_48244", "Selected cut at depth 12, code 375625, node 1025817",
                "At remaining fuel 9 and original index 1025817, selection on the full partial prefix of depth 12 and code 375625 returns the complete row with depth 12, base-four code 375625, original node 1025817, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48291", "selected_cut_48291", "Selected cut at depth 12, code 375834, node 806997",
                "At remaining fuel 9 and original index 806997, selection on the full partial prefix of depth 12 and code 375834 returns the complete row with depth 12, base-four code 375834, original node 806997, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93906-1352928", "unmarked_context_11_93906_1352928", "Unmarked parent at depth 11, code 93906",
                "The frontier Boolean is false at remaining fuel 10, original node 1352928, the whole prefixCache at depth 11 and code 93906, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93957-1354336", "unmarked_context_11_93957_1354336", "Unmarked parent at depth 11, code 93957",
                "The frontier Boolean is false at remaining fuel 10, original node 1354336, the whole prefixCache at depth 11 and code 93957, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93906-1352928", "node_context_11_93906_1352928", "Original split at fuel 10 and node 1352928",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1352878, 1025817, 1352906, 1352927. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93957-1354336", "node_context_11_93957_1354336", "Original split at fuel 10 and node 1354336",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1354272, 1172003, 1354335, 347235. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-375625-1025817", "context_12_375625_1025817", "Context at depth 12, code 375625, node 1025817",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 375625 and original node 1025817, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-375834-806997", "context_12_375834_806997", "Context at depth 12, code 375834, node 806997",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 375834 and original node 806997, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
