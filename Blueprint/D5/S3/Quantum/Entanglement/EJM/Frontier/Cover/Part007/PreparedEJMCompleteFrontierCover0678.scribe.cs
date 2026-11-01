using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0678Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0678.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0678",
        H("Original frontier context coverage 0678"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32547", "selected_cut_32547", "Selected cut at depth 13, code 438372, node 837606",
                "At remaining fuel 8 and original index 837606, selection on the full partial prefix of depth 13 and code 438372 returns the complete row with depth 13, base-four code 438372, original node 837606, kind 2, reserved field 0, 2141 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32595", "selected_cut_32595", "Selected cut at depth 13, code 438423, node 838796",
                "At remaining fuel 8 and original index 838796, selection on the full partial prefix of depth 13 and code 438423 returns the complete row with depth 13, base-four code 438423, original node 838796, kind 2, reserved field 0, 833 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109593-837708", "unmarked_context_12_109593_837708", "Unmarked parent at depth 12, code 109593",
                "The frontier Boolean is false at remaining fuel 9, original node 837708, the whole prefixCache at depth 12 and code 109593, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-109604-838681", "unmarked_context_12_109604_838681", "Unmarked parent at depth 12, code 109604",
                "The frontier Boolean is false at remaining fuel 9, original node 838681, the whole prefixCache at depth 12 and code 109604, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109593-837708", "node_context_12_109593_837708", "Original split at fuel 9 and node 837708",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 837606, 837643, 837699, 837707. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-109604-838681", "node_context_12_109604_838681", "Original split at fuel 9 and node 838681",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 838615, 838652, 838671, 838680. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-438372-837606", "context_13_438372_837606", "Context at depth 13, code 438372, node 837606",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 438372 and original node 837606, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-438423-838796", "context_13_438423_838796", "Context at depth 13, code 438423, node 838796",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 438423 and original node 838796, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
