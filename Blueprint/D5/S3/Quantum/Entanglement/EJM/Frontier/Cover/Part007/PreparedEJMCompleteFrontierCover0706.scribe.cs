using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0706Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0706.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0706",
        H("Original frontier context coverage 0706"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33891", "selected_cut_33891", "Selected cut at depth 13, code 450693, node 873043",
                "At remaining fuel 8 and original index 873043, selection on the full partial prefix of depth 13 and code 450693 returns the complete row with depth 13, base-four code 450693, original node 873043, kind 2, reserved field 0, 1941 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33939", "selected_cut_33939", "Selected cut at depth 12, code 112698, node 875157",
                "At remaining fuel 9 and original index 875157, selection on the full partial prefix of depth 12 and code 112698 returns the complete row with depth 12, base-four code 112698, original node 875157, kind 2, reserved field 0, 2877 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-112673-873105", "unmarked_context_12_112673_873105", "Unmarked parent at depth 12, code 112673",
                "The frontier Boolean is false at remaining fuel 9, original node 873105, the whole prefixCache at depth 12 and code 112673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-28173-874953", "unmarked_context_11_28173_874953", "Unmarked parent at depth 11, code 28173",
                "The frontier Boolean is false at remaining fuel 10, original node 874953, the whole prefixCache at depth 11 and code 28173, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-112673-873105", "node_context_12_112673_873105", "Original split at fuel 9 and node 873105",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 872967, 873043, 873088, 873104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-28173-874953", "node_context_11_28173_874953", "Original split at fuel 10 and node 874953",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 874688, 874784, 874859, 874952. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-450693-873043", "context_13_450693_873043", "Context at depth 13, code 450693, node 873043",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 450693 and original node 873043, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-112698-875157", "context_12_112698_875157", "Context at depth 12, code 112698, node 875157",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 112698 and original node 875157, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
