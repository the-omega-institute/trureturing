using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0732Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0732.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0732",
        H("Original frontier context coverage 0732"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35139", "selected_cut_35139", "Selected cut at depth 12, code 284199, node 920915",
                "At remaining fuel 9 and original index 920915, selection on the full partial prefix of depth 12 and code 284199 returns the complete row with depth 12, base-four code 284199, original node 920915, kind 2, reserved field 0, 2557 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35186", "selected_cut_35186", "Selected cut at depth 12, code 284261, node 896706",
                "At remaining fuel 9 and original index 896706, selection on the full partial prefix of depth 12 and code 284261 returns the complete row with depth 12, base-four code 284261, original node 896706, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71049-920916", "unmarked_context_11_71049_920916", "Unmarked parent at depth 11, code 71049",
                "The frontier Boolean is false at remaining fuel 10, original node 920916, the whole prefixCache at depth 11 and code 71049, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71064-922543", "unmarked_context_11_71064_922543", "Unmarked parent at depth 11, code 71064",
                "The frontier Boolean is false at remaining fuel 10, original node 922543, the whole prefixCache at depth 11 and code 71064, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71049-920916", "node_context_11_71049_920916", "Original split at fuel 10 and node 920916",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 920797, 920829, 920874, 920915. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71064-922543", "node_context_11_71064_922543", "Original split at fuel 10 and node 922543",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 922467, 896706, 922508, 922542. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-284199-920915", "context_12_284199_920915", "Context at depth 12, code 284199, node 920915",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 284199 and original node 920915, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-284261-896706", "context_12_284261_896706", "Context at depth 12, code 284261, node 896706",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 284261 and original node 896706, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
