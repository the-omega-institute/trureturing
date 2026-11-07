using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0033Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0033.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0033",
        H("Original frontier context coverage 0033"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01587", "selected_cut_01587", "Selected cut at depth 13, code 18675, node 56467",
                "At remaining fuel 8 and original index 56467, selection on the full partial prefix of depth 13 and code 18675 returns the complete row with depth 13, base-four code 18675, original node 56467, kind 2, reserved field 0, 1041 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01633", "selected_cut_01633", "Selected cut at depth 13, code 18712, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 18712 returns the complete row with depth 13, base-four code 18712, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4668-56468", "unmarked_context_12_4668_56468", "Unmarked parent at depth 12, code 4668",
                "The frontier Boolean is false at remaining fuel 9, original node 56468, the whole prefixCache at depth 12 and code 4668, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4677-57471", "unmarked_context_12_4677_57471", "Unmarked parent at depth 12, code 4677",
                "The frontier Boolean is false at remaining fuel 9, original node 57471, the whole prefixCache at depth 12 and code 4677, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4668-56468", "node_context_12_4668_56468", "Original split at fuel 9 and node 56468",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 56367, 56423, 56456, 56467. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4677-57471", "node_context_12_4677_57471", "Original split at fuel 9 and node 57471",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 57438, 57461, 57470. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-18675-56467", "context_13_18675_56467", "Context at depth 13, code 18675, node 56467",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18675 and original node 56467, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-18712-3444", "context_13_18712_3444", "Context at depth 13, code 18712, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18712 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
