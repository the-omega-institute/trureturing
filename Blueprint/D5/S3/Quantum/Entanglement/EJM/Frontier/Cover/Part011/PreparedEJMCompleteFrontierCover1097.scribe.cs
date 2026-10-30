using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1097Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1097.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1097",
        H("Original frontier context coverage 1097"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52658", "selected_cut_52658", "Selected cut at depth 9, code 18644, node 1542771",
                "At remaining fuel 12 and original index 1542771, selection on the full partial prefix of depth 9 and code 18644 returns the complete row with depth 9, base-four code 18644, original node 1542771, kind 2, reserved field 0, 3921 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52705", "selected_cut_52705", "Selected cut at depth 10, code 74800, node 1468246",
                "At remaining fuel 11 and original index 1468246, selection on the full partial prefix of depth 10 and code 74800 returns the complete row with depth 10, base-four code 74800, original node 1468246, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18645-1543074", "unmarked_context_9_18645_1543074", "Unmarked parent at depth 9, code 18645",
                "The frontier Boolean is false at remaining fuel 12, original node 1543074, the whole prefixCache at depth 9 and code 18645, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-4673-1545547", "unmarked_context_8_4673_1545547", "Unmarked parent at depth 8, code 4673",
                "The frontier Boolean is false at remaining fuel 13, original node 1545547, the whole prefixCache at depth 8 and code 4673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18645-1543074", "node_context_9_18645_1543074", "Original split at fuel 12 and node 1543074",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1542899, 1468874, 1542994, 1543073. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-4673-1545547", "node_context_8_4673_1545547", "Original split at fuel 13 and node 1545547",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1545336, 1545467, 1545530, 1545546. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-18644-1542771", "context_9_18644_1542771", "Context at depth 9, code 18644, node 1542771",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18644 and original node 1542771, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-74800-1468246", "context_10_74800_1468246", "Context at depth 10, code 74800, node 1468246",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 74800 and original node 1468246, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
