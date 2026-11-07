using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0734Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0734.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0734",
        H("Original frontier context coverage 0734"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35235", "selected_cut_35235", "Selected cut at depth 11, code 71082, node 923706",
                "At remaining fuel 10 and original index 923706, selection on the full partial prefix of depth 11 and code 71082 returns the complete row with depth 11, base-four code 71082, original node 923706, kind 2, reserved field 0, 1769 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35282", "selected_cut_35282", "Selected cut at depth 12, code 285203, node 925639",
                "At remaining fuel 9 and original index 925639, selection on the full partial prefix of depth 12 and code 285203 returns the complete row with depth 12, base-four code 285203, original node 925639, kind 2, reserved field 0, 3945 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17770-923753", "unmarked_context_10_17770_923753", "Unmarked parent at depth 10, code 17770",
                "The frontier Boolean is false at remaining fuel 11, original node 923753, the whole prefixCache at depth 10 and code 17770, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17824-925416", "unmarked_context_10_17824_925416", "Unmarked parent at depth 10, code 17824",
                "The frontier Boolean is false at remaining fuel 11, original node 925416, the whole prefixCache at depth 10 and code 17824, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17770-923753", "node_context_10_17770_923753", "Original split at fuel 11 and node 923753",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 923658, 923681, 923706, 923752. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17824-925416", "node_context_10_17824_925416", "Original split at fuel 11 and node 925416",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 924493, 924827, 925052, 925415. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-71082-923706", "context_11_71082_923706", "Context at depth 11, code 71082, node 923706",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71082 and original node 923706, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-285203-925639", "context_12_285203_925639", "Context at depth 12, code 285203, node 925639",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 285203 and original node 925639, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
